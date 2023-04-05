#include "solver/fp/fp_solver.h"

#include "env.h"
#include "node/node_kind.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "rewrite/rewriter.h"
#include "solver/array/array_solver.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "solver/fun/fun_solver.h"
#include "solver/quant/quant_solver.h"

namespace bzla::fp {

using namespace bzla::node;

bool
FpSolver::is_theory_leaf(const Node& term)
{
  Kind k = term.kind();
  return k == Kind::FP_IS_INF || k == Kind::FP_IS_NAN || k == Kind::FP_IS_NEG
         || k == Kind::FP_IS_NORMAL || k == Kind::FP_IS_POS
         || k == Kind::FP_IS_SUBNORMAL || k == Kind::FP_IS_ZERO
         || k == Kind::FP_EQUAL || k == Kind::FP_LEQ || k == Kind::FP_LT
         || k == Kind::FP_TO_SBV || k == Kind::FP_TO_UBV
         || (k == Kind::EQUAL
             && (term[0].type().is_fp() || term[0].type().is_rm()));
}

FpSolver::FpSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_word_blaster(state),
      d_word_blast_queue(state.backtrack_mgr()),
      d_word_blast_index(state.backtrack_mgr())
{
}

FpSolver::~FpSolver() {}

bool
FpSolver::check()
{
  Log(1) << "\n*** check fp";

  reset_cached_values();
  NodeManager& nm = NodeManager::get();
  for (size_t i = d_word_blast_index.get(), size = d_word_blast_queue.size();
       i < size;
       ++i)
  {
    const Node& node = d_word_blast_queue[i];
    Node wb = d_word_blaster.word_blast(node);

    if (wb == node) continue;

    if (node.type().is_bool())
    {
      assert(wb.type().is_bv() && wb.type().bv_size() == 1);
      d_solver_state.lemma(
          nm.mk_node(Kind::EQUAL, {node, node::utils::bv1_to_bool(wb)}));
    }
    else
    {
      assert(node.type().is_bv() && node.type() == wb.type());
      d_solver_state.lemma(nm.mk_node(Kind::EQUAL, {node, wb}));
    }
  }
  d_word_blast_index = d_word_blast_queue.size();
  return true;
}

namespace {
/**
 * Determine if given node is a leaf node for the value computation of the
 * floating-point solver, i.e., a term of floating-point or rounding mode type
 * that belongs to any of the other theories or is a conversion from a term
 * that belongs to other theories.
 * @param node The node to query.
 */
bool
is_leaf(const Node& node)
{
  if (array::ArraySolver::is_theory_leaf(node)
      || fun::FunSolver::is_theory_leaf(node)
      || quant::QuantSolver::is_theory_leaf(node))
  {
    return true;
  }
  Kind k = node.kind();
  return k == Kind::CONSTANT;
}
}  // namespace

Node
FpSolver::value(const Node& term)
{
  assert(term.type().is_fp() || term.type().is_rm());

  NodeManager& nm = NodeManager::get();
  node_ref_vector visit{term};
  unordered_node_ref_map<bool> cache;

  Rewriter& rw = d_env.rewriter();
  do
  {
    const Node& cur = visit.back();
    assert(is_theory_leaf(cur) || cur.type().is_fp() || cur.type().is_rm());

    if (!get_cached_value(cur).is_null())
    {
      visit.pop_back();
      continue;
    }

    auto [it, inserted] = cache.emplace(cur, false);
    if (inserted)
    {
      if (!is_leaf(cur))
      {
        Kind k = cur.kind();
        if (k == Kind::FP_TO_FP_FROM_SBV || k == Kind::FP_TO_FP_FROM_UBV)
        {
          visit.push_back(cur[0]);  // compute value for rounding mode only
        }
        // Skip bit-vector children
        else if (k != Kind::FP_TO_FP_FROM_BV)
        {
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
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

        case Kind::SELECT:
        case Kind::APPLY:
        case Kind::CONSTANT:
          assert(is_leaf(cur));
          value = assignment(cur);
          break;

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
        case Kind::FP_TO_SBV:
        case Kind::FP_TO_UBV:
        case Kind::FP_TO_FP_FROM_FP:
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
        case Kind::FP_SUB: {
          std::vector<Node> values;
          for (const Node& arg : cur)
          {
            values.push_back(get_cached_value(arg));
            assert(!values.back().is_null());
          }
          value = rw.rewrite(nm.mk_node(cur.kind(), values, cur.indices()));
        }
        break;

        // bit-vector as argument
        case Kind::FP_TO_FP_FROM_BV:
          assert(cur.num_children() == 1);
          value = rw.rewrite(nm.mk_node(
              cur.kind(), {d_solver_state.value(cur[0])}, cur.indices()));
          break;

        // rounding mode and bit-vector as argument
        case Kind::FP_TO_FP_FROM_SBV:
        case Kind::FP_TO_FP_FROM_UBV: {
          std::vector<Node> values;
          values.push_back(get_cached_value(cur[0]));      // rounding mode
          values.push_back(d_solver_state.value(cur[1]));  // bit-vector
          value = rw.rewrite(nm.mk_node(cur.kind(), values, cur.indices()));
        }
        break;

        default: assert(false); break;
      }
      cache_value(cur, value);
    }
    visit.pop_back();
  } while (!visit.empty());

  return get_cached_value(term);
}

void
FpSolver::register_term(const Node& term)
{
  d_word_blast_queue.push_back(term);
}

/* --- FpSolver private ----------------------------------------------------- */

Node
FpSolver::assignment(const Node& term)
{
  assert(is_leaf(term));
  assert(term.type().is_fp() || term.type().is_rm());
  if (d_word_blaster.is_word_blasted(term))
  {
    NodeManager& nm = NodeManager::get();
    Node wb         = d_env.rewriter().rewrite(d_word_blaster.word_blast(term));
    Node value      = d_solver_state.value(wb);
    assert(value.type().is_bv());
    const BitVector& bv = value.value<BitVector>();
    if (term.type().is_rm())
    {
      uint64_t rm = bv.to_uint64();
      return nm.mk_value(static_cast<RoundingMode>(rm));
    }
    assert(term.type().is_fp());
    return nm.mk_value(FloatingPoint(term.type(), bv));
  }
  return node::utils::mk_default_value(term.type());
}

}  // namespace bzla::fp
