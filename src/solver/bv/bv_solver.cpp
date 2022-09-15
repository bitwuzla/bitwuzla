#include "solver/bv/bv_solver.h"

#include <iostream>

#include "node/node_manager.h"
#include "sat/cadical.h"
#include "solving_context.h"

namespace bzla::bv {

using namespace bzla::node;

/** Sat solver wrapper for AIG encoder. */
class BvSolver::BitblastSatSolver : public bb::SatInterface
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

BvSolver::BvSolver(SolvingContext& context) : Solver(context)
{
  d_sat_solver.reset(new sat::Cadical());
  d_bitblast_sat_solver.reset(new BitblastSatSolver(*d_sat_solver));
  d_cnf_encoder.reset(new bb::AigCnfEncoder(*d_bitblast_sat_solver));
}

BvSolver::~BvSolver() {}

Result
BvSolver::check()
{
  for (const Node& assertion : d_context.d_assertions)
  {
    auto it = d_bitblaster_cache.find(assertion);
    if (it != d_bitblaster_cache.end())
    {
      continue;
    }

    bitblast(assertion);
    d_cnf_encoder->encode(get_bits(assertion)[0], true);
  }

  auto sat_res = d_sat_solver->solve();
  if (sat_res == sat::SatSolver::Result::SAT)
  {
    d_sat_state = Result::SAT;
  }
  else if (sat_res == sat::SatSolver::Result::UNSAT)
  {
    d_sat_state = Result::UNSAT;
  }
  else
  {
    d_sat_state = Result::UNKNOWN;
  }
  return d_sat_state;
}

// TODO: move typedefs
using NodeRefVector = std::vector<std::reference_wrapper<const Node>>;
template <class T>
using NodeRefMap =
    std::unordered_map<std::reference_wrapper<const Node>, T, std::hash<Node>>;

Node
BvSolver::value(const Node& term)
{
  assert(d_sat_state == Result::SAT);
  assert(term.get_type().is_bool() || term.get_type().is_bv());

  NodeManager& nm = NodeManager::get();
  NodeRefVector visit{term};
  NodeRefMap<bool> cache;

  do
  {
    const Node& cur = visit.back();
    assert(cur.get_type().is_bool() || cur.get_type().is_bv());

    if (!get_cached_value(cur).is_null())
    {
      visit.pop_back();
      continue;
    }

    auto it = cache.find(cur);
    if (it == cache.end())
    {
      cache.emplace(cur, false);
      if (!is_leaf(cur))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (!it->second)
    {
      it->second = true;

      Node value;
      switch (cur.get_kind())
      {
        case Kind::VALUE: value = cur; break;

        // Boolean abstractions
        case Kind::FP_IS_INF:
        case Kind::FP_IS_NAN:
        case Kind::FP_IS_NEG:
        case Kind::FP_IS_NORM:
        case Kind::FP_IS_POS:
        case Kind::FP_IS_SUBNORM:
        case Kind::FP_IS_ZERO:
        case Kind::FP_EQUAL:
        case Kind::FP_LE:
        case Kind::FP_LT:
        case Kind::FORALL:
        case Kind::EXISTS:
        // Bit-vector abstractions
        case Kind::FP_TO_SBV:
        case Kind::FP_TO_UBV:
        // Both
        case Kind::SELECT:
        case Kind::APPLY:
        case Kind::CONSTANT:
          assert(is_leaf(cur));
          value = get_assignment(cur);
          break;

        case Kind::NOT:
          value = nm.mk_value(!get_cached_value(cur[0]).get_value<bool>());
          break;

        case Kind::BV_NOT:
          value = nm.mk_value(
              get_cached_value(cur[0]).get_value<BitVector>().bvnot());
          break;

        case Kind::AND:
          value = nm.mk_value(get_cached_value(cur[0]).get_value<bool>()
                              && get_cached_value(cur[1]).get_value<bool>());
          break;

        case Kind::BV_AND:
          value =
              nm.mk_value(get_cached_value(cur[0]).get_value<BitVector>().bvand(
                  get_cached_value(cur[1]).get_value<BitVector>()));
          break;

        case Kind::OR:
          value = nm.mk_value(get_cached_value(cur[0]).get_value<bool>()
                              || get_cached_value(cur[1]).get_value<bool>());
          break;

        case Kind::BV_EXTRACT:
          value = nm.mk_value(
              get_cached_value(cur[0]).get_value<BitVector>().bvextract(
                  cur.get_index(0), cur.get_index(1)));
          break;

        case Kind::EQUAL: {
          const Type& type0 = cur[0].get_type();
          if (type0.is_bool())
          {
            value = nm.mk_value(get_cached_value(cur[0]).get_value<bool>()
                                == get_cached_value(cur[1]).get_value<bool>());
          }
          else if (type0.is_bv())
          {
            value =
                nm.mk_value(get_cached_value(cur[0]).get_value<BitVector>()
                            == get_cached_value(cur[1]).get_value<BitVector>());
          }
          else
          {
            value = get_assignment(cur);
          }
        }
        break;

        case Kind::BV_ADD:
          value =
              nm.mk_value(get_cached_value(cur[0]).get_value<BitVector>().bvadd(
                  get_cached_value(cur[1]).get_value<BitVector>()));
          break;

        case Kind::BV_MUL:
          value =
              nm.mk_value(get_cached_value(cur[0]).get_value<BitVector>().bvmul(
                  get_cached_value(cur[1]).get_value<BitVector>()));
          break;

        case Kind::BV_ULT:
          value = nm.mk_value(
              get_cached_value(cur[0]).get_value<BitVector>().compare(
                  get_cached_value(cur[1]).get_value<BitVector>())
              < 0);
          break;

        case Kind::BV_SHL:
          value =
              nm.mk_value(get_cached_value(cur[0]).get_value<BitVector>().bvshl(
                  get_cached_value(cur[1]).get_value<BitVector>()));
          break;

        case Kind::BV_SLT:
          value = nm.mk_value(
              get_cached_value(cur[0]).get_value<BitVector>().signed_compare(
                  get_cached_value(cur[1]).get_value<BitVector>())
              < 0);
          break;

        case Kind::BV_SHR:
          value =
              nm.mk_value(get_cached_value(cur[0]).get_value<BitVector>().bvshr(
                  get_cached_value(cur[1]).get_value<BitVector>()));
          break;

        case Kind::BV_ASHR:
          value = nm.mk_value(
              get_cached_value(cur[0]).get_value<BitVector>().bvashr(
                  get_cached_value(cur[1]).get_value<BitVector>()));
          break;

        case Kind::BV_UDIV:
          value = nm.mk_value(
              get_cached_value(cur[0]).get_value<BitVector>().bvudiv(
                  get_cached_value(cur[1]).get_value<BitVector>()));
          break;

        case Kind::BV_UREM:
          value = nm.mk_value(
              get_cached_value(cur[0]).get_value<BitVector>().bvurem(
                  get_cached_value(cur[1]).get_value<BitVector>()));
          break;

        case Kind::BV_CONCAT:
          value = nm.mk_value(
              get_cached_value(cur[0]).get_value<BitVector>().bvconcat(
                  get_cached_value(cur[1]).get_value<BitVector>()));
          break;

        case Kind::ITE:
          value = get_cached_value(cur[0]).get_value<bool>()
                      ? get_cached_value(cur[1])
                      : get_cached_value(cur[2]);
          break;

        // We should never reach these kinds.
        case Kind::NUM_KINDS:
        case Kind::NULL_NODE:
        case Kind::VARIABLE:
        case Kind::FP_ABS:
        case Kind::FP_NEG:
        case Kind::FP_TO_FP_FROM_BV:
        case Kind::FP_MIN:
        case Kind::FP_MAX:
        case Kind::FP_SQRT:
        case Kind::FP_REM:
        case Kind::FP_RTI:
        case Kind::FP_TO_FP_FROM_FP:
        case Kind::FP_TO_FP_FROM_SBV:
        case Kind::FP_TO_FP_FROM_UBV:
        case Kind::LAMBDA:
        case Kind::FP_ADD:
        case Kind::FP_MUL:
        case Kind::FP_DIV:
        case Kind::STORE:
        case Kind::FP_FMA: assert(false); break;
      }
      cache_value(cur, value);
    }
    visit.pop_back();
  } while (!visit.empty());

  return get_cached_value(term);
}

/* --- BvSolver private ---------------------------------------------------- */

void
BvSolver::bitblast(const Node& t)
{
  using namespace node;

  std::vector<std::reference_wrapper<const Node>> visit{t};
  do
  {
    const Node& cur = visit.back();
    assert(cur.get_type().is_bool() || cur.get_type().is_bv());

    auto it = d_bitblaster_cache.find(cur);
    if (it == d_bitblaster_cache.end())
    {
      d_bitblaster_cache.emplace(cur, bb::AigBitblaster::Bits());
      if (!is_leaf(cur))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.empty())
    {
      const Type& type = cur.get_type();
      assert(type.is_bool() || type.is_bv());

      switch (cur.get_kind())
      {
        case Kind::VALUE:
          it->second = type.is_bool()
                           ? d_bitblaster.bv_value(
                               BitVector(1, cur.get_value<bool>() ? 1 : 0, 1))
                           : d_bitblaster.bv_value(cur.get_value<BitVector>());
          break;

        // Boolean abstractions
        case Kind::FP_IS_INF:
        case Kind::FP_IS_NAN:
        case Kind::FP_IS_NEG:
        case Kind::FP_IS_NORM:
        case Kind::FP_IS_POS:
        case Kind::FP_IS_SUBNORM:
        case Kind::FP_IS_ZERO:
        case Kind::FP_EQUAL:
        case Kind::FP_LE:
        case Kind::FP_LT:
        case Kind::FORALL:
        case Kind::EXISTS:
        // Bit-vector abstractions
        case Kind::FP_TO_SBV:
        case Kind::FP_TO_UBV:
        // Both
        case Kind::SELECT:
        case Kind::APPLY: register_abstraction(cur); [[fallthrough]];

        case Kind::CONSTANT:
          assert(is_leaf(cur));
          it->second = type.is_bool()
                           ? d_bitblaster.bv_constant(1)
                           : d_bitblaster.bv_constant(type.get_bv_size());
          break;

        case Kind::NOT:
        case Kind::BV_NOT:
          assert(cur.get_kind() != Kind::NOT || type.is_bool());
          assert(cur.get_kind() != Kind::BV_NOT || type.is_bv());
          it->second = d_bitblaster.bv_not(get_bits(cur[0]));
          break;

        case Kind::AND:
        case Kind::BV_AND:
          assert(cur.get_kind() != Kind::NOT || type.is_bool());
          assert(cur.get_kind() != Kind::BV_NOT || type.is_bv());
          it->second = d_bitblaster.bv_and(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::OR:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_or(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::BV_EXTRACT:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_extract(
              get_bits(cur[0]), cur.get_index(0), cur.get_index(1));
          break;

        case Kind::EQUAL: {
          const Type& type0 = cur[0].get_type();
          if (type0.is_bool() || type0.is_bv())
          {
            it->second = d_bitblaster.bv_eq(get_bits(cur[0]), get_bits(cur[1]));
          }
          else
          {
            // For all other cases we abstract equality as a Boolean constant.
            it->second = d_bitblaster.bv_constant(1);
            register_abstraction(cur);
          }
        }
        break;

        case Kind::BV_ADD:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_add(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::BV_MUL:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_mul(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::BV_ULT:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_ult(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::BV_SHL:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_shl(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::BV_SLT:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_slt(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::BV_SHR:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_shr(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::BV_ASHR:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_ashr(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::BV_UDIV:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_udiv(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::BV_UREM:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_urem(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::BV_CONCAT:
          assert(type.is_bv());
          it->second =
              d_bitblaster.bv_concat(get_bits(cur[0]), get_bits(cur[1]));
          break;

        case Kind::ITE:
          assert(cur[0].get_type().is_bool());
          it->second = d_bitblaster.bv_ite(
              get_bits(cur[0])[0], get_bits(cur[1]), get_bits(cur[2]));
          break;

        // We should never reach these kinds.
        case Kind::NUM_KINDS:
        case Kind::NULL_NODE:
        case Kind::VARIABLE:
        case Kind::FP_ABS:
        case Kind::FP_NEG:
        case Kind::FP_TO_FP_FROM_BV:
        case Kind::FP_MIN:
        case Kind::FP_MAX:
        case Kind::FP_SQRT:
        case Kind::FP_REM:
        case Kind::FP_RTI:
        case Kind::FP_TO_FP_FROM_FP:
        case Kind::FP_TO_FP_FROM_SBV:
        case Kind::FP_TO_FP_FROM_UBV:
        case Kind::LAMBDA:
        case Kind::FP_ADD:
        case Kind::FP_MUL:
        case Kind::FP_DIV:
        case Kind::STORE:
        case Kind::FP_FMA: assert(false); break;
      }
    }
    visit.pop_back();
  } while (!visit.empty());
}

void
BvSolver::register_abstraction(const Node& term)
{
  // TODO:
}

const bb::AigBitblaster::Bits&
BvSolver::get_bits(const Node& term) const
{
  assert(d_bitblaster_cache.find(term) != d_bitblaster_cache.end());
  return d_bitblaster_cache.at(term);
}

bool
BvSolver::is_leaf(const Node& term) const
{
  Kind k = term.get_kind();
  return k == Kind::CONSTANT
         // Quantifiers
         || k == Kind::FORALL
         || k == Kind::EXISTS
         // array selects and function applications
         || k == Kind::SELECT
         || k == Kind::APPLY
         // FP predicates
         || k == Kind::FP_IS_INF || k == Kind::FP_IS_NAN || k == Kind::FP_IS_NEG
         || k == Kind::FP_IS_NORM || k == Kind::FP_IS_POS
         || k == Kind::FP_IS_SUBNORM || k == Kind::FP_IS_ZERO
         || k == Kind::FP_EQUAL || k == Kind::FP_LE
         || k == Kind::FP_LT
         // FP to BV conversion
         || k == Kind::FP_TO_SBV
         || k == Kind::FP_TO_UBV
         // Equalities over terms that are not Booleans or bit-vectors
         || (k == Kind::EQUAL && !term[0].get_type().is_bool()
             && !term[0].get_type().is_bv());
}

Node
BvSolver::get_assignment(const Node& term) const
{
  assert(is_leaf(term));
  assert(term.get_type().is_bool() || term.get_type().is_bv());

  auto it          = d_bitblaster_cache.find(term);
  const Type& type = term.get_type();
  NodeManager& nm  = NodeManager::get();

  // Return default values if not bit-blasted
  if (it == d_bitblaster_cache.end())
  {
    if (type.is_bool())
    {
      return nm.mk_value(false);
    }
    else
    {
      return nm.mk_value(BitVector(type.get_bv_size(), 0));
    }
  }

  const auto& bits = it->second;
  if (type.is_bool())
  {
    return nm.mk_value(d_cnf_encoder->value(bits[0]));
  }

  BitVector val(type.get_bv_size());
  for (size_t i = 0, size = bits.size(); i < size; ++i)
  {
    val.set_bit(size - 1 - i, d_cnf_encoder->value(bits[i]) == 1);
  }
  return nm.mk_value(val);
}

}  // namespace bzla::bv
