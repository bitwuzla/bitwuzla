#include "solver/bv/bv_solver.h"

#include "bv/bitvector.h"
#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_map.h"
#include "solver/bv/bv_bitblast_solver.h"
#include "solving_context.h"

namespace bzla::bv {

using namespace bzla::node;

/* --- BvBitblastSolver public ---------------------------------------------- */

bool
BvSolver::is_leaf(const Node& term)
{
  Kind k = term.kind();
  return k == Kind::CONSTANT
         || k == Kind::VALUE
         // Quantifiers
         || k == Kind::FORALL
         || k == Kind::EXISTS
         // Array selects and function applications
         || k == Kind::SELECT
         || k == Kind::APPLY
         // FP predicates
         || k == Kind::FP_IS_INF || k == Kind::FP_IS_NAN || k == Kind::FP_IS_NEG
         || k == Kind::FP_IS_NORMAL || k == Kind::FP_IS_POS
         || k == Kind::FP_IS_SUBNORMAL || k == Kind::FP_IS_ZERO
         || k == Kind::FP_EQUAL || k == Kind::FP_LEQ
         || k == Kind::FP_LT
         // FP to BV conversion
         || k == Kind::FP_TO_SBV
         || k == Kind::FP_TO_UBV
         // Equalities over terms that are not Booleans or bit-vectors
         || (k == Kind::EQUAL && !term[0].type().is_bool()
             && !term[0].type().is_bv());
}

BvSolver::BvSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_bitblast_solver(env, state),
      d_prop_solver(env, state, d_bitblast_solver),
      d_cur_solver(env.options().bv_solver())
{
}

BvSolver::~BvSolver() {}

void
BvSolver::register_assertion(const Node& assertion, bool top_level)
{
  if (d_cur_solver == option::BvSolver::BITBLAST
      || d_cur_solver == option::BvSolver::PREPROP)
  {
    d_bitblast_solver.register_assertion(assertion, top_level);
  }
  if (d_cur_solver == option::BvSolver::PROP
      || d_cur_solver == option::BvSolver::PREPROP)
  {
    d_prop_solver.register_assertion(assertion, top_level);
  }
}

Result
BvSolver::solve()
{
  reset_cached_values();
  switch (d_env.options().bv_solver())
  {
    case option::BvSolver::BITBLAST:
      assert(d_cur_solver == option::BvSolver::BITBLAST);
      d_sat_state = d_bitblast_solver.solve();
      break;
    case option::BvSolver::PROP:
      assert(d_cur_solver == option::BvSolver::PROP);
      d_sat_state = d_prop_solver.solve();
      break;
    case option::BvSolver::PREPROP:
      d_cur_solver = option::BvSolver::PROP;
      assert(false);
      // TODO
      break;
  }
  return d_sat_state;
}

Node
BvSolver::value(const Node& term)
{
  assert(d_sat_state == Result::SAT);
  assert(term.type().is_bool() || term.type().is_bv());

  NodeManager& nm = NodeManager::get();
  node_ref_vector visit{term};
  unordered_node_ref_map<bool> cache;

  do
  {
    const Node& cur = visit.back();
    assert(cur.type().is_bool() || cur.type().is_bv());

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
      switch (cur.kind())
      {
        case Kind::VALUE: value = cur; break;

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
          assert(is_leaf(cur));
          value = assignment(cur);
          break;

        case Kind::NOT:
          value = nm.mk_value(!get_cached_value(cur[0]).value<bool>());
          break;

        case Kind::BV_NOT:
          value =
              nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvnot());
          break;

        case Kind::BV_DEC:
          value =
              nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvdec());
          break;

        case Kind::BV_INC:
          value =
              nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvinc());
          break;

        case Kind::AND:
          value = nm.mk_value(get_cached_value(cur[0]).value<bool>()
                              && get_cached_value(cur[1]).value<bool>());
          break;

        case Kind::BV_AND:
          value = nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvand(
              get_cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::OR:
          value = nm.mk_value(get_cached_value(cur[0]).value<bool>()
                              || get_cached_value(cur[1]).value<bool>());
          break;

        case Kind::BV_XOR:
          value = nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvxor(
              get_cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_EXTRACT:
          value =
              nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvextract(
                  cur.index(0), cur.index(1)));
          break;

        case Kind::EQUAL: {
          const Type& type0 = cur[0].type();
          if (type0.is_bool())
          {
            value = nm.mk_value(get_cached_value(cur[0]).value<bool>()
                                == get_cached_value(cur[1]).value<bool>());
          }
          else if (type0.is_bv())
          {
            value = nm.mk_value(get_cached_value(cur[0]).value<BitVector>()
                                == get_cached_value(cur[1]).value<BitVector>());
          }
          else
          {
            value = assignment(cur);
          }
        }
        break;

        // TODO: maybe eliminate
        case Kind::BV_COMP: {
          bool equal = get_cached_value(cur[0]).value<BitVector>()
                       == get_cached_value(cur[1]).value<BitVector>();
          value = nm.mk_value(
              BitVector::from_ui(cur[0].type().bv_size(), equal ? 1 : 0));
        }
        break;

        case Kind::BV_ADD:
          value = nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvadd(
              get_cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_MUL:
          value = nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvmul(
              get_cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_ULT:
          value =
              nm.mk_value(get_cached_value(cur[0]).value<BitVector>().compare(
                              get_cached_value(cur[1]).value<BitVector>())
                          < 0);
          break;

        case Kind::BV_SHL:
          value = nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvshl(
              get_cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_SLT:
          value = nm.mk_value(
              get_cached_value(cur[0]).value<BitVector>().signed_compare(
                  get_cached_value(cur[1]).value<BitVector>())
              < 0);
          break;

        case Kind::BV_SHR:
          value = nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvshr(
              get_cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_ASHR:
          value =
              nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvashr(
                  get_cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_UDIV:
          value =
              nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvudiv(
                  get_cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_UREM:
          value =
              nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvurem(
                  get_cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_CONCAT:
          value =
              nm.mk_value(get_cached_value(cur[0]).value<BitVector>().bvconcat(
                  get_cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::ITE:
          value = get_cached_value(cur[0]).value<bool>()
                      ? get_cached_value(cur[1])
                      : get_cached_value(cur[2]);
          break;

        // We should never reach these kinds.
        case Kind::NUM_KINDS:
        case Kind::NULL_NODE:
        case Kind::VARIABLE:
        case Kind::IMPLIES:
        case Kind::DISTINCT:
        case Kind::XOR:
        case Kind::EXISTS:

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
        case Kind::FP_GEQ:
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
      cache_value(cur, value);
    }
    visit.pop_back();
  } while (!visit.empty());

  return get_cached_value(term);
}

/* --- BvBitblastSolver private --------------------------------------------- */

Node
BvSolver::assignment(const Node& term)
{
  assert(is_leaf(term));
  assert(term.type().is_bool() || term.type().is_bv());
  if (d_cur_solver == option::BvSolver::BITBLAST)
  {
    return d_bitblast_solver.value(term);
  }
  assert(d_cur_solver == option::BvSolver::PROP);
  return d_prop_solver.value(term);
}

}  // namespace bzla::bv
