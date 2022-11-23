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

/* --- BvSolver public ----------------------------------------------------- */

BvBitblastSolver::BvBitblastSolver(SolverEngine& solver_engine)
    : Solver(solver_engine), d_assumptions(solver_engine.backtrack_mgr())
{
  d_sat_solver.reset(new sat::Cadical());
  d_bitblast_sat_solver.reset(new BitblastSatSolver(*d_sat_solver));
  d_cnf_encoder.reset(new bb::AigCnfEncoder(*d_bitblast_sat_solver));
}

BvBitblastSolver::~BvBitblastSolver() {}

Result
BvBitblastSolver::solve()
{
  for (const Node& assumption : d_assumptions)
  {
    d_sat_solver->assume(bits(assumption)[0].get_id());
  }
  return d_sat_solver->solve();
}

void
BvBitblastSolver::register_assertion(const Node& assertion, bool top_level)
{
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
        case Kind::FP_LE:
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

        // TODO: maybe eliminate
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

        // We should never reach these kinds.
        case Kind::NUM_KINDS:
        case Kind::NULL_NODE:
        case Kind::VARIABLE:
        case Kind::IMPLIES:
        case Kind::DISTINCT:
        case Kind::XOR:
        case Kind::EXISTS:

        case Kind::BV_DEC:
        case Kind::BV_INC:
        case Kind::BV_NAND:
        case Kind::BV_NEG:
        case Kind::BV_NOR:
        case Kind::BV_OR:
        case Kind::BV_REDAND:
        case Kind::BV_REDOR:
        case Kind::BV_REDXOR:
        case Kind::BV_REPEAT:
        case Kind::BV_ROL:
        case Kind::BV_ROLI:
        case Kind::BV_ROR:
        case Kind::BV_RORI:
        case Kind::BV_SADDO:
        case Kind::BV_SDIV:
        case Kind::BV_SDIVO:
        case Kind::BV_SGE:
        case Kind::BV_SGT:
        case Kind::BV_SIGN_EXTEND:
        case Kind::BV_SLE:
        case Kind::BV_SMOD:
        case Kind::BV_SMULO:
        case Kind::BV_SREM:
        case Kind::BV_SSUBO:
        case Kind::BV_SUB:
        case Kind::BV_UADDO:
        case Kind::BV_UGE:
        case Kind::BV_UGT:
        case Kind::BV_ULE:
        case Kind::BV_UMULO:
        case Kind::BV_USUBO:
        case Kind::BV_XNOR:
        case Kind::BV_ZERO_EXTEND:

        case Kind::FP_ABS:
        case Kind::FP_ADD:
        case Kind::FP_DIV:
        case Kind::FP_FMA:
        case Kind::FP_FP:
        case Kind::FP_GE:
        case Kind::FP_GT:
        case Kind::FP_MAX:
        case Kind::FP_MIN:
        case Kind::FP_MUL:
        case Kind::FP_NEG:
        case Kind::FP_REM:
        case Kind::FP_RTI:
        case Kind::FP_SQRT:
        case Kind::FP_SUB:
        case Kind::FP_TO_FP_FROM_BV:
        case Kind::FP_TO_FP_FROM_FP:
        case Kind::FP_TO_FP_FROM_SBV:
        case Kind::FP_TO_FP_FROM_UBV:
        case Kind::LAMBDA:
        case Kind::STORE:
        case Kind::CONST_ARRAY: assert(false); break;
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

}  // namespace bzla::bv
