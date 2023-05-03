#include "solver/bv/bv_bitblast_solver.h"

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "sat/cadical.h"
#include "solver/bv/bv_solver.h"
#include "solving_context.h"

namespace bzla::bv {

using namespace bzla::node;

/** Sat solver wrapper for AIG encoder. */
class BvBitblastSolver::BitblastSatSolver : public bb::SatInterface
{
 public:
  BitblastSatSolver(sat::SatSolver& solver) : d_solver(solver) {}

  void add(int64_t lit) override { d_solver.add(lit); }

  void add_clause(const std::initializer_list<int64_t>& literals) override
  {
    for (int64_t lit : literals)
    {
      d_solver.add(lit);
    }
    d_solver.add(0);
  }

  bool value(int64_t lit) override
  {
    return d_solver.value(lit) == 1 ? true : false;
  }

 private:
  sat::SatSolver& d_solver;
};

/* --- BvBitblastSolver public ---------------------------------------------- */

BvBitblastSolver::BvBitblastSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_assumptions(state.backtrack_mgr()),
      d_last_result(Result::UNKNOWN),
      d_stats(env.statistics())
{
  d_sat_solver.reset(new sat::Cadical());
  d_bitblast_sat_solver.reset(new BitblastSatSolver(*d_sat_solver));
  d_cnf_encoder.reset(new bb::AigCnfEncoder(*d_bitblast_sat_solver));
}

BvBitblastSolver::~BvBitblastSolver() {}

Result
BvBitblastSolver::solve()
{
  d_sat_solver->configure_terminator(d_env.terminator());

  for (const Node& assumption : d_assumptions)
  {
    d_sat_solver->assume(bits(assumption)[0].get_id());
  }

  update_statistics();
  util::Timer timer(d_stats.time_sat);
  d_last_result = d_sat_solver->solve();
  return d_last_result;
}

void
BvBitblastSolver::register_assertion(const Node& assertion,
                                     bool top_level,
                                     bool is_lemma)
{
  // If unsat cores are enabled, all assertions are assumptions except lemmas.
  if (d_env.options().produce_unsat_cores() && !is_lemma)
  {
    top_level = false;
  }

  if (!top_level)
  {
    d_assumptions.push_back(assertion);
  }

  bitblast(assertion);
  d_cnf_encoder->encode(bits(assertion)[0], top_level);
}

Node
BvBitblastSolver::value(const Node& term)
{
  assert(BvSolver::is_leaf(term));
  assert(term.type().is_bool() || term.type().is_bv());

  const auto& it   = d_bitblaster_cache.find(term);
  const Type& type = term.type();
  NodeManager& nm  = NodeManager::get();

  // Return default value if not bit-blasted
  if (it == d_bitblaster_cache.end())
  {
    return utils::mk_default_value(type);
  }

  const auto& bits = it->second;
  if (type.is_bool())
  {
    return nm.mk_value(d_cnf_encoder->value(bits[0]) == 1);
  }

  BitVector val(type.bv_size());
  for (size_t i = 0, size = bits.size(); i < size; ++i)
  {
    val.set_bit(size - 1 - i, d_cnf_encoder->value(bits[i]) == 1);
  }
  return nm.mk_value(val);
}

void
BvBitblastSolver::bitblast(const Node& t)
{
  using namespace node;

  node_ref_vector visit{t};
  do
  {
    const Node& cur = visit.back();
    assert(cur.type().is_bool() || cur.type().is_bv());

    auto it = d_bitblaster_cache.find(cur);
    if (it == d_bitblaster_cache.end())
    {
      d_bitblaster_cache.emplace(cur, bb::AigBitblaster::Bits());
      if (!BvSolver::is_leaf(cur))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.empty())
    {
      const Type& type = cur.type();
      assert(type.is_bool() || type.is_bv());

      switch (cur.kind())
      {
        case Kind::VALUE:
          it->second = type.is_bool()
                           ? d_bitblaster.bv_value(
                               BitVector::from_ui(1, cur.value<bool>() ? 1 : 0))
                           : d_bitblaster.bv_value(cur.value<BitVector>());
          break;

        // Boolean abstractions
        case Kind::FP_IS_INF:
        case Kind::FP_IS_NAN:
        case Kind::FP_IS_NEG:
        case Kind::FP_IS_NORMAL:
        case Kind::FP_IS_POS:
        case Kind::FP_IS_SUBNORMAL:
        case Kind::FP_IS_ZERO:
        case Kind::FP_EQUAL:
        case Kind::FP_LEQ:
        case Kind::FP_LT:
        case Kind::FORALL:
        // Bit-vector abstractions
        case Kind::FP_TO_SBV:
        case Kind::FP_TO_UBV:
        // Both
        case Kind::SELECT:
        case Kind::APPLY:
        case Kind::CONSTANT:
          assert(BvSolver::is_leaf(cur));
          it->second = type.is_bool()
                           ? d_bitblaster.bv_constant(1)
                           : d_bitblaster.bv_constant(type.bv_size());
          break;

        case Kind::NOT:
        case Kind::BV_NOT:
          assert(cur.kind() != Kind::NOT || type.is_bool());
          assert(cur.kind() != Kind::BV_NOT || type.is_bv());
          it->second = d_bitblaster.bv_not(bits(cur[0]));
          break;

        case Kind::AND:
        case Kind::BV_AND:
          assert(cur.kind() != Kind::NOT || type.is_bool());
          assert(cur.kind() != Kind::BV_NOT || type.is_bv());
          it->second = d_bitblaster.bv_and(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::OR:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_or(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_XOR:
          it->second = d_bitblaster.bv_xor(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_EXTRACT:
          assert(type.is_bv());
          it->second =
              d_bitblaster.bv_extract(bits(cur[0]), cur.index(0), cur.index(1));
          break;

        case Kind::EQUAL: {
          const Type& type0 = cur[0].type();
          if (type0.is_bool() || type0.is_bv())
          {
            it->second = d_bitblaster.bv_eq(bits(cur[0]), bits(cur[1]));
          }
          else
          {
            // For all other cases we abstract equality as a Boolean constant.
            it->second = d_bitblaster.bv_constant(1);
          }
        }
        break;

        case Kind::BV_COMP:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_eq(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_ADD:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_add(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_MUL:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_mul(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_ULT:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_ult(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_SHL:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_shl(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_SLT:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_slt(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_SHR:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_shr(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_ASHR:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_ashr(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_UDIV:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_udiv(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_UREM:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_urem(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_CONCAT:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_concat(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::ITE:
          assert(cur[0].type().is_bool());
          it->second =
              d_bitblaster.bv_ite(bits(cur[0])[0], bits(cur[1]), bits(cur[2]));
          break;

        // We should never reach other kinds.
        default: assert(false); break;
      }
    }
    visit.pop_back();
  } while (!visit.empty());
}

const bb::AigBitblaster::Bits&
BvBitblastSolver::bits(const Node& term) const
{
  assert(d_bitblaster_cache.find(term) != d_bitblaster_cache.end());
  return d_bitblaster_cache.at(term);
}

void
BvBitblastSolver::unsat_core(std::vector<Node>& core) const
{
  assert(d_last_result == Result::UNSAT);
  assert(d_env.options().produce_unsat_cores());

  for (const Node& assumption : d_assumptions)
  {
    if (d_sat_solver->failed(bits(assumption)[0].get_id()))
    {
      core.push_back(assumption);
    }
  }
}

/* --- BvBitblastSolver private --------------------------------------------- */

void
BvBitblastSolver::update_statistics()
{
  d_stats.num_aig_ands = d_bitblaster.num_aig_ands();
  d_stats.num_aig_consts = d_bitblaster.num_aig_consts();
  d_stats.num_aig_shared   = d_bitblaster.num_aig_shared();
  auto& cnf_stats = d_cnf_encoder->statistics();
  d_stats.num_cnf_vars = cnf_stats.num_vars;
  d_stats.num_cnf_clauses = cnf_stats.num_clauses;
  d_stats.num_cnf_literals = cnf_stats.num_literals;
  Msg(1) << d_stats.num_aig_consts << " AIG consts, " << d_stats.num_aig_ands
         << " AIG ands, " << d_stats.num_cnf_vars << " CNF vars, "
         << d_stats.num_cnf_clauses << " CNF clauses";
}

BvBitblastSolver::Statistics::Statistics(util::Statistics& stats)
    : time_sat(
        stats.new_stat<util::TimerStatistic>("bv::bitblast::sat::time_solve")),
      num_aig_ands(stats.new_stat<uint64_t>("bv::bitblast::aig::num_ands")),
      num_aig_consts(stats.new_stat<uint64_t>("bv::bitblast::aig::num_consts")),
      num_aig_shared(stats.new_stat<uint64_t>("bv::bitblast::aig::num_shared")),
      num_cnf_vars(stats.new_stat<uint64_t>("bv::bitblast::cnf::num_vars")),
      num_cnf_clauses(
          stats.new_stat<uint64_t>("bv::bitblast::cnf::num_clauses")),
      num_cnf_literals(
          stats.new_stat<uint64_t>("bv::bitblast::cnf::num_literals"))
{
}

}  // namespace bzla::bv
