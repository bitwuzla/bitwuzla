/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "rewrite/rewriter.h"

#include "env.h"
#include "node/node_kind.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_set.h"
#include "rewrite/rewrites_array.h"
#include "rewrite/rewrites_bool.h"
#include "rewrite/rewrites_bv.h"
#include "rewrite/rewrites_fp.h"
#include "util/logger.h"

#define BZLA_APPLY_RW_RULE(rw_rule)                                \
  do                                                               \
  {                                                                \
    std::tie(res, kind) =                                          \
        RewriteRule<RewriteRuleKind::rw_rule>::apply(*this, node); \
    if (res != node)                                               \
    {                                                              \
      d_stats_rewrites << kind;                                    \
      goto DONE;                                                   \
    }                                                              \
  } while (false);

#define BZLA_ELIM_KIND_IMPL(name, rule)           \
  Node Rewriter::rewrite_##name(const Node& node) \
  {                                               \
    RewriteRuleKind kind;                         \
    Node res;                                     \
                                                  \
    BZLA_APPLY_RW_RULE(rule);                     \
                                                  \
  DONE:                                           \
    return res;                                   \
  }

namespace bzla {

using namespace node;

#ifndef NDEBUG
namespace {

std::pair<size_t, size_t>
diff(uint64_t max_id, const Node& rewritten)
{
  node::node_ref_vector visit{rewritten};
  std::vector<size_t> depths{0};
  size_t max_depth = 0;
  node::unordered_node_ref_set cache;
  do
  {
    const Node& cur = visit.back();
    size_t depth    = depths.back();
    visit.pop_back();
    depths.pop_back();
    if (cur.id() < max_id)
    {
      continue;
    }
    if (depth > max_depth)
    {
      max_depth = depth;
    }
    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      for (size_t i = 0; i < cur.num_children(); ++i)
      {
        depths.push_back(depth + 1);
      }
    }
  } while (!visit.empty());
  return std::make_pair(cache.size(), max_depth);
}

}  // namespace
#endif

/* === Rewriter public ====================================================== */

Rewriter::Rewriter(Env& env, uint8_t level)
    : d_env(env),
      d_logger(env.logger()),
      d_level(level),
      d_stats_rewrites(env.statistics().new_stat<util::HistogramStatistic>(
          "rewriter::rewrite"))
{
  assert(d_level <= option::Options::REWRITE_LEVEL_MAX);
  (void) d_env;  // only used in debug mode
}

const Node&
Rewriter::rewrite(const Node& node)
{
  node::node_ref_vector visit{node};
  do
  {
    const Node& cur = visit.back();
    auto [it, inserted] = d_cache.emplace(cur, Node());
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      if (cur.num_children())
      {
#ifndef NDEBUG
        // Reset nodes counter
        d_num_nodes = 0;
        // Save current maximum node id
        int64_t max_id = NodeManager::get().max_node_id();
#endif
        it->second = _rewrite(node::utils::rebuild_node(cur, d_cache));
#ifndef NDEBUG
        uint64_t thresh = d_env.options().dbg_rw_node_thresh();
        if (thresh > 0 && d_num_nodes > 0)
        {
          auto [new_nodes, depth] = diff(max_id, it->second);
          Warn(new_nodes >= thresh) << "_rewrite() introduced " << new_nodes
                                    << " new nodes up to depth " << depth;
        }
#endif
      }
      else
      {
        it->second = cur;
      }
    }
    visit.pop_back();
  } while (!visit.empty());
  assert(d_cache.find(node) != d_cache.end());
  return d_cache.at(node);
}

const Node&
Rewriter::mk_node(node::Kind kind,
                  const std::vector<Node>& children,
                  const std::vector<uint64_t>& indices)
{
#ifndef NDEBUG
  uint64_t max_id = NodeManager::get().max_node_id();
#endif
  Node node = NodeManager::get().mk_node(kind, children, indices);
  ++d_num_rec_calls;
#ifndef NDEBUG
  auto [it, inserted] = d_rec_cache.insert(node);
  assert(inserted);  // Rewrite cycle detected if this fails.
#endif
  const Node& res = _rewrite(node);
#ifndef NDEBUG
  if (res.id() >= max_id)
  {
    ++d_num_nodes;
  }
  d_rec_cache.erase(node);
#endif
  --d_num_rec_calls;
  return res;
}

const Node&
Rewriter::invert_node(const Node& node)
{
  assert(node.type().is_bool() || node.type().is_bv());
  if (node.type().is_bool())
  {
    return mk_node(node::Kind::NOT, {node});
  }
  return mk_node(node::Kind::BV_NOT, {node});
}

const Node&
Rewriter::invert_node_if(bool condition, const Node& node)
{
  assert(node.type().is_bool() || node.type().is_bv());
  return condition ? invert_node(node) : node;
}

bool
Rewriter::is_or(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::OR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.is_inverted() && node[0].kind() == Kind::AND)
  {
    child0 = node[0][0].is_inverted() ? node[0][0][0] : invert_node(node[0][0]);
    child1 = node[0][1].is_inverted() ? node[0][1][0] : invert_node(node[0][1]);
    return true;
  }
  return false;
}

bool
Rewriter::is_xor(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::XOR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  Node or0, or1;
  if (node.kind() == Kind::AND)
  {
    if ((is_or(node[0], or0, or1) && node[1].is_inverted()
         && node[1][0].kind() == Kind::AND
         && (node[1][0][0] == or0 || node[1][0][0] == or1)
         && (node[1][0][1] == or0 || node[1][0][1] == or1))
        || (is_or(node[1], or0, or1) && node[0].is_inverted()
            && node[0][0].kind() == Kind::AND
            && (node[0][0][0] == or0 || node[0][0][0] == or1)
            && (node[0][0][1] == or0 || node[0][0][1] == or1)))
    {
      child0 = or0;
      child1 = or1;
      return true;
    }
  }
  return false;
}

bool
Rewriter::is_xnor(const Node& node, Node& child0, Node& child1)
{
  if (node.is_inverted())
  {
    Node xor0, xor1;
    if (is_xor(node[0], xor0, xor1))
    {
      child0 = xor0;
      child1 = xor1;
      return true;
    }
  }
  return false;
}

bool
Rewriter::is_bv_neg(const Node& node, Node& child)
{
  Node one =
      NodeManager::get().mk_value(BitVector::mk_one(node.type().bv_size()));
  if (node.kind() == Kind::BV_NEG)
  {
    child = node[0];
    return true;
  }
  if (node.kind() == Kind::BV_ADD)
  {
    if (node[0] == one)
    {
      child = invert_node(node[1]);
      return true;
    }
    if (node[1] == one)
    {
      child = invert_node(node[0]);
      return true;
    }
  }
  return false;
}

bool
Rewriter::is_bv_or(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::BV_OR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.is_inverted() && node[0].kind() == Kind::BV_AND)
  {
    child0 = node[0][0].is_inverted() ? node[0][0][0] : invert_node(node[0][0]);
    child1 = node[0][1].is_inverted() ? node[0][1][0] : invert_node(node[0][1]);
    return true;
  }
  return false;
}

bool
Rewriter::is_bv_sub(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::BV_SUB)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.kind() == Kind::BV_ADD)
  {
    if (is_bv_neg(node[0], child1))
    {
      child0 = node[1];
      return true;
    }
    if (is_bv_neg(node[1], child1))
    {
      child0 = node[0];
      return true;
    }
  }
  return false;
}

bool
Rewriter::is_bv_xnor(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::BV_XNOR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.is_inverted() && node[0].kind() == Kind::BV_XOR)
  {
    child0 = node[0][0];
    child1 = node[0][1];
    return true;
  }
  return false;
}

void
Rewriter::clear_cache()
{
  d_cache.clear();
}

/* === Rewriter private ===================================================== */

const Node&
Rewriter::_rewrite(const Node& node)
{
  // Lookup rewrite cache
  auto [it, inserted] = d_cache.emplace(node, Node());
  if (!inserted && !it->second.is_null())
  {
    return it->second;
  }

  // Limit rewrite recursion depth if we run into rewrite cycles in production
  // mode. Ideally, this should not happen, but if it does, we do not crash.
  if (d_num_rec_calls >= RECURSION_LIMIT)
  {
    assert(false);
    d_recursion_limit_reached = true;
    it->second                = node;
    return it->second;
  }

  // Normalize before rewriting
  Node n = normalize_commutative(node);

  Node res;
  switch (n.kind())
  {
    case node::Kind::AND: res = rewrite_and(n); break;
    case node::Kind::DISTINCT: res = rewrite_distinct(n); break;
    case node::Kind::IMPLIES: res = rewrite_implies(n); break;
    case node::Kind::NOT: res = rewrite_not(n); break;
    case node::Kind::OR: res = rewrite_or(n); break;
    case node::Kind::XOR: res = rewrite_xor(n); break;

    case node::Kind::EQUAL: res = rewrite_eq(n); break;
    case node::Kind::ITE: res = rewrite_ite(n); break;

    case node::Kind::BV_AND: res = rewrite_bv_and(n); break;
    case node::Kind::BV_ADD: res = rewrite_bv_add(n); break;
    case node::Kind::BV_ASHR: res = rewrite_bv_ashr(n); break;
    case node::Kind::BV_CONCAT: res = rewrite_bv_concat(n); break;
    case node::Kind::BV_DEC: res = rewrite_bv_dec(n); break;
    case node::Kind::BV_EXTRACT: res = rewrite_bv_extract(n); break;
    case node::Kind::BV_INC: res = rewrite_bv_inc(n); break;
    case node::Kind::BV_MUL: res = rewrite_bv_mul(n); break;
    case node::Kind::BV_NOT: res = rewrite_bv_not(n); break;
    case node::Kind::BV_SHL: res = rewrite_bv_shl(n); break;
    case node::Kind::BV_SHR: res = rewrite_bv_shr(n); break;
    case node::Kind::BV_SLT: res = rewrite_bv_slt(n); break;
    case node::Kind::BV_UDIV: res = rewrite_bv_udiv(n); break;
    case node::Kind::BV_ULT: res = rewrite_bv_ult(n); break;
    case node::Kind::BV_UREM: res = rewrite_bv_urem(n); break;
    case node::Kind::BV_COMP: res = rewrite_bv_comp(n); break;

    /* Eliminated bit-vector operators */
    case node::Kind::BV_NAND: res = rewrite_bv_nand(n); break;
    case node::Kind::BV_NEG: res = rewrite_bv_neg(n); break;
    case node::Kind::BV_NEGO: res = rewrite_bv_nego(n); break;
    case node::Kind::BV_NOR: res = rewrite_bv_nor(n); break;
    case node::Kind::BV_OR: res = rewrite_bv_or(n); break;
    case node::Kind::BV_REDAND: res = rewrite_bv_redand(n); break;
    case node::Kind::BV_REDOR: res = rewrite_bv_redor(n); break;
    case node::Kind::BV_REDXOR: res = rewrite_bv_redxor(n); break;
    case node::Kind::BV_REPEAT: res = rewrite_bv_repeat(n); break;
    case node::Kind::BV_ROL: res = rewrite_bv_rol(n); break;
    case node::Kind::BV_ROLI: res = rewrite_bv_roli(n); break;
    case node::Kind::BV_ROR: res = rewrite_bv_ror(n); break;
    case node::Kind::BV_RORI: res = rewrite_bv_rori(n); break;
    case node::Kind::BV_SADDO: res = rewrite_bv_saddo(n); break;
    case node::Kind::BV_SDIV: res = rewrite_bv_sdiv(n); break;
    case node::Kind::BV_SDIVO: res = rewrite_bv_sdivo(n); break;
    case node::Kind::BV_SGE: res = rewrite_bv_sge(n); break;
    case node::Kind::BV_SGT: res = rewrite_bv_sgt(n); break;
    case node::Kind::BV_SIGN_EXTEND: res = rewrite_bv_sign_extend(n); break;
    case node::Kind::BV_SLE: res = rewrite_bv_sle(n); break;
    case node::Kind::BV_SMOD: res = rewrite_bv_smod(n); break;
    case node::Kind::BV_SMULO: res = rewrite_bv_smulo(n); break;
    case node::Kind::BV_SREM: res = rewrite_bv_srem(n); break;
    case node::Kind::BV_SSUBO: res = rewrite_bv_ssubo(n); break;
    case node::Kind::BV_SUB: res = rewrite_bv_sub(n); break;
    case node::Kind::BV_UMULO: res = rewrite_bv_umulo(n); break;
    case node::Kind::BV_UADDO: res = rewrite_bv_uaddo(n); break;
    case node::Kind::BV_UGE: res = rewrite_bv_uge(n); break;
    case node::Kind::BV_UGT: res = rewrite_bv_ugt(n); break;
    case node::Kind::BV_ULE: res = rewrite_bv_ule(n); break;
    case node::Kind::BV_USUBO: res = rewrite_bv_usubo(n); break;
    case node::Kind::BV_XNOR: res = rewrite_bv_xnor(n); break;
    case node::Kind::BV_XOR: res = rewrite_bv_xor(n); break;
    case node::Kind::BV_ZERO_EXTEND: res = rewrite_bv_zero_extend(n); break;

    case node::Kind::FP_ABS: res = rewrite_fp_abs(n); break;
    case node::Kind::FP_ADD: res = rewrite_fp_add(n); break;
    case node::Kind::FP_DIV: res = rewrite_fp_div(n); break;
    case node::Kind::FP_EQUAL: res = rewrite_fp_equal(n); break;
    case node::Kind::FP_FMA: res = rewrite_fp_fma(n); break;
    case node::Kind::FP_FP: res = rewrite_fp_fp(n); break;
    case node::Kind::FP_GEQ: res = rewrite_fp_geq(n); break;
    case node::Kind::FP_GT: res = rewrite_fp_gt(n); break;

    case node::Kind::FP_IS_INF: res = rewrite_fp_is_inf(n); break;
    case node::Kind::FP_IS_NAN: res = rewrite_fp_is_nan(n); break;
    case node::Kind::FP_IS_NEG: res = rewrite_fp_is_neg(n); break;
    case node::Kind::FP_IS_NORMAL: res = rewrite_fp_is_normal(n); break;
    case node::Kind::FP_IS_POS: res = rewrite_fp_is_pos(n); break;
    case node::Kind::FP_IS_SUBNORMAL: res = rewrite_fp_is_subnormal(n); break;
    case node::Kind::FP_IS_ZERO: res = rewrite_fp_is_zero(n); break;

    case node::Kind::FP_LEQ: res = rewrite_fp_leq(n); break;
    case node::Kind::FP_LT: res = rewrite_fp_lt(n); break;
    case node::Kind::FP_MAX: res = rewrite_fp_max(n); break;
    case node::Kind::FP_MIN: res = rewrite_fp_min(n); break;
    case node::Kind::FP_MUL: res = rewrite_fp_mul(n); break;
    case node::Kind::FP_NEG: res = rewrite_fp_neg(n); break;
    case node::Kind::FP_REM: res = rewrite_fp_rem(n); break;
    case node::Kind::FP_RTI: res = rewrite_fp_rti(n); break;
    case node::Kind::FP_SQRT: res = rewrite_fp_sqrt(n); break;
    case node::Kind::FP_SUB: res = rewrite_fp_sub(n); break;

    case node::Kind::FP_TO_FP_FROM_BV: res = rewrite_fp_to_fp_from_bv(n); break;
    case node::Kind::FP_TO_FP_FROM_FP: res = rewrite_fp_to_fp_from_fp(n); break;
    case node::Kind::FP_TO_FP_FROM_SBV:
      res = rewrite_fp_to_fp_from_sbv(n);
      break;
    case node::Kind::FP_TO_FP_FROM_UBV:
      res = rewrite_fp_to_fp_from_ubv(n);
      break;

    // No rewrites for FP_TO_(U|S)BV conversion yet
    case node::Kind::FP_TO_SBV:
    case node::Kind::FP_TO_UBV: res = n; break;

    // There are no rewrites for constant arrays.
    case node::Kind::CONST_ARRAY: res = n; break;

    case node::Kind::SELECT: res = rewrite_select(n); break;
    case node::Kind::STORE: res = rewrite_store(n); break;

    case node::Kind::APPLY: res = rewrite_apply(n); break;
    case node::Kind::LAMBDA: res = rewrite_lambda(n); break;

    case node::Kind::FORALL: res = rewrite_forall(n); break;
    case node::Kind::EXISTS: res = rewrite_exists(n); break;

    default: assert(false);
  }

  // Normalize again
  res = normalize_commutative(res);

  assert(!res.is_null());
  assert(res.type() == node.type());

  // Get iterator again in case a recursive call changed the size of d_cache
  // and invalidated the iterator.
  it = d_cache.find(node);
  assert(it != d_cache.end());
  assert(it->second.is_null());

  // Cache result
  it->second = res;

  return it->second;
}

/* Boolean rewrites --------------------------------------------------------- */

Node
Rewriter::rewrite_and(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(AND_EVAL);
    BZLA_APPLY_RW_RULE(AND_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(AND_CONST);
    BZLA_APPLY_RW_RULE(AND_IDEM1);
    BZLA_APPLY_RW_RULE(AND_IDEM2);
    BZLA_APPLY_RW_RULE(AND_IDEM3);
    BZLA_APPLY_RW_RULE(AND_CONTRA1);
    BZLA_APPLY_RW_RULE(AND_CONTRA2);
    BZLA_APPLY_RW_RULE(AND_CONTRA3);
    BZLA_APPLY_RW_RULE(AND_RESOL1);
    BZLA_APPLY_RW_RULE(AND_SUBSUM1);
    BZLA_APPLY_RW_RULE(AND_SUBSUM2);
    BZLA_APPLY_RW_RULE(AND_NOT_AND1);
    BZLA_APPLY_RW_RULE(AND_NOT_AND2);
    BZLA_APPLY_RW_RULE(AND_BV_LT_FALSE);
    BZLA_APPLY_RW_RULE(AND_BV_LT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_distinct(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(DISTINCT_CARD);
  }
  BZLA_APPLY_RW_RULE(DISTINCT_ELIM);
DONE:
  return res;
}

Node
Rewriter::rewrite_not(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(NOT_EVAL);
    BZLA_APPLY_RW_RULE(NOT_NOT);
    BZLA_APPLY_RW_RULE(NOT_XOR);
  }

DONE:
  return res;
}

BZLA_ELIM_KIND_IMPL(implies, IMPLIES_ELIM)
BZLA_ELIM_KIND_IMPL(or, OR_ELIM)
BZLA_ELIM_KIND_IMPL(xor, XOR_ELIM)

/* -------------------------------------------------------------------------- */

Node
Rewriter::rewrite_eq(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(EQUAL_EVAL);
    BZLA_APPLY_RW_RULE(EQUAL_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(EQUAL_CONST);
    BZLA_APPLY_RW_RULE(EQUAL_TRUE);
    BZLA_APPLY_RW_RULE(EQUAL_ITE);
    BZLA_APPLY_RW_RULE(EQUAL_FALSE);
    BZLA_APPLY_RW_RULE(EQUAL_INV);
    BZLA_APPLY_RW_RULE(EQUAL_CONST_BV_ADD);
    BZLA_APPLY_RW_RULE(EQUAL_CONST_BV_MUL);
    BZLA_APPLY_RW_RULE(EQUAL_CONST_BV_NOT);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(EQUAL_BV_ADD);
    BZLA_APPLY_RW_RULE(EQUAL_BV_ADD_ADD);
    BZLA_APPLY_RW_RULE(EQUAL_BV_CONCAT);
    BZLA_APPLY_RW_RULE(EQUAL_BV_SUB);
    BZLA_APPLY_RW_RULE(EQUAL_EQUAL_CONST_BV1);
    BZLA_APPLY_RW_RULE(EQUAL_ITE_SAME);
    BZLA_APPLY_RW_RULE(EQUAL_ITE_INVERTED);
    BZLA_APPLY_RW_RULE(EQUAL_ITE_DIS_BV1);
    BZLA_APPLY_RW_RULE(EQUAL_ITE_LIFT_COND);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_ite(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(ITE_EVAL);
    BZLA_APPLY_RW_RULE(ITE_SAME);
    BZLA_APPLY_RW_RULE(ITE_THEN_ITE1);
    BZLA_APPLY_RW_RULE(ITE_THEN_ITE2);
    BZLA_APPLY_RW_RULE(ITE_THEN_ITE3);
    BZLA_APPLY_RW_RULE(ITE_ELSE_ITE1);
    BZLA_APPLY_RW_RULE(ITE_ELSE_ITE2);
    BZLA_APPLY_RW_RULE(ITE_ELSE_ITE3);
    BZLA_APPLY_RW_RULE(ITE_BOOL);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(ITE_BV_CONCAT);
    BZLA_APPLY_RW_RULE(ITE_BV_OP);
  }

DONE:
  return res;
}

/* BV rewrites -------------------------------------------------------------- */

Node
Rewriter::rewrite_bv_add(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_ADD_EVAL);
    BZLA_APPLY_RW_RULE(BV_ADD_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_ADD_CONST);
    BZLA_APPLY_RW_RULE(BV_ADD_BV1);
    BZLA_APPLY_RW_RULE(BV_ADD_SAME);
    BZLA_APPLY_RW_RULE(BV_ADD_NOT);
    BZLA_APPLY_RW_RULE(BV_ADD_NEG);
    BZLA_APPLY_RW_RULE(BV_ADD_UREM);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_ADD_ITE1);
    BZLA_APPLY_RW_RULE(BV_ADD_ITE2);
    BZLA_APPLY_RW_RULE(BV_ADD_MUL1);
    BZLA_APPLY_RW_RULE(BV_ADD_MUL2);
    BZLA_APPLY_RW_RULE(BV_ADD_SHL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_and(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_AND_EVAL);
    BZLA_APPLY_RW_RULE(BV_AND_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_AND_CONST);
    BZLA_APPLY_RW_RULE(BV_AND_IDEM1);
    BZLA_APPLY_RW_RULE(BV_AND_IDEM2);
    BZLA_APPLY_RW_RULE(BV_AND_IDEM3);
    BZLA_APPLY_RW_RULE(BV_AND_CONTRA1);
    BZLA_APPLY_RW_RULE(BV_AND_CONTRA2);
    BZLA_APPLY_RW_RULE(BV_AND_CONTRA3);
    BZLA_APPLY_RW_RULE(BV_AND_RESOL1);
    BZLA_APPLY_RW_RULE(BV_AND_SUBSUM1);
    BZLA_APPLY_RW_RULE(BV_AND_SUBSUM2);
    BZLA_APPLY_RW_RULE(BV_AND_NOT_AND1);
    BZLA_APPLY_RW_RULE(BV_AND_NOT_AND2);
    BZLA_APPLY_RW_RULE(BV_AND_CONCAT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_ashr(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_ASHR_EVAL);
    BZLA_APPLY_RW_RULE(BV_ASHR_SPECIAL_CONST);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_concat(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_CONCAT_EVAL);
    BZLA_APPLY_RW_RULE(BV_CONCAT_CONST);
    BZLA_APPLY_RW_RULE(BV_CONCAT_EXTRACT);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_CONCAT_AND);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_extract(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_EXTRACT_EVAL);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_FULL);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_EXTRACT);
    if (d_level == 1)
    {
      BZLA_APPLY_RW_RULE(BV_EXTRACT_CONCAT_FULL_LHS);
      BZLA_APPLY_RW_RULE(BV_EXTRACT_CONCAT_FULL_RHS);
    }
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_EXTRACT_CONCAT_LHS_RHS);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_CONCAT);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_AND);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_ITE);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_ADD_MUL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_mul(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_MUL_EVAL);
    BZLA_APPLY_RW_RULE(BV_MUL_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_MUL_CONST);
    BZLA_APPLY_RW_RULE(BV_MUL_BV1);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_MUL_CONST_ADD);
    BZLA_APPLY_RW_RULE(BV_MUL_ONES);
    BZLA_APPLY_RW_RULE(BV_MUL_NEG);
    // rewrites for Noetzli benchmarks
    BZLA_APPLY_RW_RULE(BV_MUL_ITE);
    BZLA_APPLY_RW_RULE(BV_MUL_SHL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_not(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_NOT_EVAL);
    BZLA_APPLY_RW_RULE(BV_NOT_BV_NOT);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_NOT_BV_NEG);
    BZLA_APPLY_RW_RULE(BV_NOT_BV_CONCAT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_shl(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_SHL_EVAL);
    BZLA_APPLY_RW_RULE(BV_SHL_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_SHL_CONST);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_shr(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_SHR_EVAL);
    BZLA_APPLY_RW_RULE(BV_SHR_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_SHR_CONST);
    BZLA_APPLY_RW_RULE(BV_SHR_SAME);
    BZLA_APPLY_RW_RULE(BV_SHR_NOT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_slt(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_SLT_EVAL);
    BZLA_APPLY_RW_RULE(BV_SLT_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_SLT_SAME);
    BZLA_APPLY_RW_RULE(BV_SLT_BV1);
    BZLA_APPLY_RW_RULE(BV_SLT_ITE);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_SLT_CONCAT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_udiv(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_UDIV_EVAL);
    BZLA_APPLY_RW_RULE(BV_UDIV_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_UDIV_BV1);
    BZLA_APPLY_RW_RULE(BV_UDIV_SAME);
    BZLA_APPLY_RW_RULE(BV_UDIV_POW2);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_UDIV_ITE);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_ult(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_ULT_EVAL);
    BZLA_APPLY_RW_RULE(BV_ULT_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_ULT_SAME);
    BZLA_APPLY_RW_RULE(BV_ULT_BV1);
    BZLA_APPLY_RW_RULE(BV_ULT_ITE);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_ULT_CONCAT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_urem(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_UREM_EVAL);
    BZLA_APPLY_RW_RULE(BV_UREM_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_UREM_SAME);
    BZLA_APPLY_RW_RULE(BV_UREM_BV1);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_xor(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_XOR_EVAL);
    BZLA_APPLY_RW_RULE(BV_XOR_SAME);
    BZLA_APPLY_RW_RULE(BV_XOR_SPECIAL_CONST);
  }

DONE:
  return res;
}

/* Eliminated operators */

BZLA_ELIM_KIND_IMPL(bv_dec, BV_DEC_ELIM)
BZLA_ELIM_KIND_IMPL(bv_inc, BV_INC_ELIM)
BZLA_ELIM_KIND_IMPL(bv_nand, BV_NAND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_neg, BV_NEG_ELIM)
BZLA_ELIM_KIND_IMPL(bv_nego, BV_NEGO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_nor, BV_NOR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_or, BV_OR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_redand, BV_REDAND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_redor, BV_REDOR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_redxor, BV_REDXOR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_repeat, BV_REPEAT_ELIM)
BZLA_ELIM_KIND_IMPL(bv_rol, BV_ROL_ELIM)
BZLA_ELIM_KIND_IMPL(bv_roli, BV_ROLI_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ror, BV_ROR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_rori, BV_RORI_ELIM)
BZLA_ELIM_KIND_IMPL(bv_saddo, BV_SADDO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sdiv, BV_SDIV_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sdivo, BV_SDIVO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sge, BV_SGE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sgt, BV_SGT_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sign_extend, BV_SIGN_EXTEND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sle, BV_SLE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_smod, BV_SMOD_ELIM)
BZLA_ELIM_KIND_IMPL(bv_smulo, BV_SMULO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_srem, BV_SREM_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ssubo, BV_SSUBO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sub, BV_SUB_ELIM)
BZLA_ELIM_KIND_IMPL(bv_uaddo, BV_UADDO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_uge, BV_UGE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ugt, BV_UGT_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ule, BV_ULE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_umulo, BV_UMULO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_usubo, BV_USUBO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_xnor, BV_XNOR_ELIM)
// BZLA_ELIM_KIND_IMPL(bv_xor, BV_XOR_ELIM) do not eliminate
BZLA_ELIM_KIND_IMPL(bv_zero_extend, BV_ZERO_EXTEND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_comp, BV_COMP_ELIM)

/* FP rewrites -------------------------------------------------------------- */

Node
Rewriter::rewrite_fp_abs(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_ABS_EVAL);
    BZLA_APPLY_RW_RULE(FP_ABS_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_add(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_ADD_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_div(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_DIV_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_fma(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_FMA_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_inf(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_INF_EVAL);
    BZLA_APPLY_RW_RULE(FP_IS_INF_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_nan(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_NAN_EVAL);
    BZLA_APPLY_RW_RULE(FP_IS_NAN_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_neg(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_NEG_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_normal(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_NORM_EVAL);
    BZLA_APPLY_RW_RULE(FP_IS_NORM_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_pos(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_POS_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_subnormal(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_SUBNORM_EVAL);
    BZLA_APPLY_RW_RULE(FP_IS_SUBNORM_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_zero(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_ZERO_EVAL);
    BZLA_APPLY_RW_RULE(FP_IS_ZERO_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_leq(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_LEQ_EVAL);
    BZLA_APPLY_RW_RULE(FP_LEQ_EQ);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_lt(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_LT_EVAL);
    BZLA_APPLY_RW_RULE(FP_LT_EQ);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_max(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_MAX_EQ);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_min(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_MIN_EQ);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_mul(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_MUL_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_neg(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_NEG_EVAL);
    BZLA_APPLY_RW_RULE(FP_NEG_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_rem(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_REM_EVAL);
    BZLA_APPLY_RW_RULE(FP_REM_SAME_DIV);
    BZLA_APPLY_RW_RULE(FP_REM_ABS_NEG);
    BZLA_APPLY_RW_RULE(FP_REM_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_rti(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_RTI_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_sqrt(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_SQRT_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_bv(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_BV_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_fp(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_FP_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_sbv(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_SBV_EVAL);
    BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_SBV_BV1_ELIM);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_ubv(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_UBV_EVAL);
  }

DONE:
  return res;
}

BZLA_ELIM_KIND_IMPL(fp_equal, FP_EQUAL_ELIM)
BZLA_ELIM_KIND_IMPL(fp_fp, FP_FP_ELIM)
BZLA_ELIM_KIND_IMPL(fp_gt, FP_GT_ELIM)
BZLA_ELIM_KIND_IMPL(fp_geq, FP_GEQ_ELIM)
BZLA_ELIM_KIND_IMPL(fp_sub, FP_SUB_ELIM)

/* Array rewrites ----------------------------------------------------------- */
Node
Rewriter::rewrite_select(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(ARRAY_PROP_SELECT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_store(const Node& node)
{
  // TODO
  return node;
}

/* Function rewrites -------------------------------------------------------- */

Node
Rewriter::rewrite_apply(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_lambda(const Node& node)
{
  // TODO
  return node;
}

/* Quant rewrites ----------------------------------------------------------- */

Node
Rewriter::rewrite_forall(const Node& node)
{
  // TODO
  return node;
}

BZLA_ELIM_KIND_IMPL(exists, EXISTS_ELIM)

/* Normalization ------------------------------------------------------------ */

Node
Rewriter::normalize_commutative(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(NORMALIZE_COMM);
  }

DONE:
  return res;
}

std::ostream&
operator<<(std::ostream& out, RewriteRuleKind kind)
{
  /* Boolean rewrites ---------------------------- */
  switch (kind)
  {
    case RewriteRuleKind::AND_EVAL: out << "AND_EVAL"; break;
    case RewriteRuleKind::AND_SPECIAL_CONST: out << "AND_SPECIAL_CONST"; break;
    case RewriteRuleKind::AND_CONST: out << "AND_CONST"; break;
    case RewriteRuleKind::AND_IDEM1: out << "AND_IDEM1"; break;
    case RewriteRuleKind::AND_IDEM2: out << "AND_IDEM2"; break;
    case RewriteRuleKind::AND_IDEM3: out << "AND_IDEM3"; break;
    case RewriteRuleKind::AND_CONTRA1: out << "AND_CONTRA1"; break;
    case RewriteRuleKind::AND_CONTRA2: out << "AND_CONTRA2"; break;
    case RewriteRuleKind::AND_CONTRA3: out << "AND_CONTRA3"; break;
    case RewriteRuleKind::AND_RESOL1: out << "AND_RESOL1"; break;
    case RewriteRuleKind::AND_SUBSUM1: out << "AND_SUBSUM1"; break;
    case RewriteRuleKind::AND_SUBSUM2: out << "AND_SUBSUM2"; break;
    case RewriteRuleKind::AND_NOT_AND1: out << "AND_NOT_AND1"; break;
    case RewriteRuleKind::AND_NOT_AND2: out << "AND_NOT_AND2"; break;
    case RewriteRuleKind::AND_BV_LT_FALSE: out << "AND_BV_LT_FALSE"; break;
    case RewriteRuleKind::AND_BV_LT: out << "AND_BV_LT"; break;

    case RewriteRuleKind::EQUAL_EVAL: out << "EQUAL_EVAL"; break;
    case RewriteRuleKind::EQUAL_SPECIAL_CONST:
      out << "EQUAL_SPECIAL_CONST";
      break;
    case RewriteRuleKind::EQUAL_CONST: out << "EQUAL_CONST"; break;
    case RewriteRuleKind::EQUAL_EQUAL_CONST_BV1:
      out << "EQUAL_EQUAL_CONST_BV1";
      break;
    case RewriteRuleKind::EQUAL_TRUE: out << "EQUAL_TRUE"; break;
    case RewriteRuleKind::EQUAL_ITE: out << "EQUAL_ITE"; break;
    case RewriteRuleKind::EQUAL_FALSE: out << "EQUAL_FALSE"; break;
    case RewriteRuleKind::EQUAL_INV: out << "EQUAL_INV"; break;
    case RewriteRuleKind::EQUAL_CONST_BV_ADD:
      out << "EQUAL_CONST_BV_ADD";
      break;
    case RewriteRuleKind::EQUAL_CONST_BV_MUL:
      out << "EQUAL_CONST_BV_MUL";
      break;
    case RewriteRuleKind::EQUAL_CONST_BV_NOT:
      out << "EQUAL_CONST_BV_NOT";
      break;
    case RewriteRuleKind::EQUAL_BV_ADD: out << "EQUAL_BV_ADD"; break;
    case RewriteRuleKind::EQUAL_BV_ADD_ADD: out << "EQUAL_BV_ADD_ADD"; break;
    case RewriteRuleKind::EQUAL_BV_CONCAT: out << "EQUAL_BV_CONCAT"; break;
    case RewriteRuleKind::EQUAL_BV_SUB: out << "EQUAL_BV_SUB"; break;
    case RewriteRuleKind::EQUAL_ITE_SAME: out << "EQUAL_ITE_SAME"; break;
    case RewriteRuleKind::EQUAL_ITE_INVERTED:
      out << "EQUAL_ITE_INVERTED";
      break;
    case RewriteRuleKind::EQUAL_ITE_DIS_BV1: out << "EQUAL_ITE_DIS_BV1"; break;
    case RewriteRuleKind::EQUAL_ITE_LIFT_COND:
      out << "EQUAL_ITE_LIFT_COND";
      break;

    case RewriteRuleKind::ITE_EVAL: out << "ITE_EVAL"; break;
    case RewriteRuleKind::ITE_SAME: out << "ITE_SAME"; break;
    case RewriteRuleKind::ITE_THEN_ITE1: out << "ITE_THEN_ITE1"; break;
    case RewriteRuleKind::ITE_THEN_ITE2: out << "ITE_THEN_ITE2"; break;
    case RewriteRuleKind::ITE_THEN_ITE3: out << "ITE_THEN_ITE3"; break;
    case RewriteRuleKind::ITE_ELSE_ITE1: out << "ITE_ELSE_ITE1"; break;
    case RewriteRuleKind::ITE_ELSE_ITE2: out << "ITE_ELSE_ITE2"; break;
    case RewriteRuleKind::ITE_ELSE_ITE3: out << "ITE_ELSE_ITE3"; break;
    case RewriteRuleKind::ITE_BOOL: out << "ITE_BOOL"; break;
    case RewriteRuleKind::ITE_BV_CONCAT: out << "ITE_BV_CONCAT"; break;
    case RewriteRuleKind::ITE_BV_OP: out << "ITE_BV_OP"; break;

    case RewriteRuleKind::NOT_EVAL: out << "NOT_EVAL"; break;
    case RewriteRuleKind::NOT_NOT: out << "NOT_NOT"; break;
    case RewriteRuleKind::NOT_XOR: out << "NOT_XOR"; break;

    case RewriteRuleKind::DISTINCT_CARD: out << "DISTINCT_CARD"; break;
    case RewriteRuleKind::DISTINCT_ELIM: out << "DISTINCT_ELIM"; break;

    case RewriteRuleKind::IMPLIES_ELIM: out << "IMPLIES_ELIM"; break;
    case RewriteRuleKind::OR_ELIM: out << "OR_ELIM"; break;
    case RewriteRuleKind::XOR_ELIM: out << "XOR_ELIM"; break;

    case RewriteRuleKind::BV_ADD_EVAL: out << "BV_ADD_EVAL"; break;
    case RewriteRuleKind::BV_ADD_SPECIAL_CONST:
      out << "BV_ADD_SPECIAL_CONST";
      break;
    case RewriteRuleKind::BV_ADD_CONST: out << "BV_ADD_CONST"; break;
    case RewriteRuleKind::BV_ADD_BV1: out << "BV_ADD_BV1"; break;
    case RewriteRuleKind::BV_ADD_SAME: out << "BV_ADD_SAME"; break;
    case RewriteRuleKind::BV_ADD_NOT: out << "BV_ADD_NOT"; break;
    case RewriteRuleKind::BV_ADD_NEG: out << "BV_ADD_NEG"; break;
    case RewriteRuleKind::BV_ADD_UREM: out << "BV_ADD_UREM"; break;
    case RewriteRuleKind::BV_ADD_ITE1: out << "BV_ADD_ITE1"; break;
    case RewriteRuleKind::BV_ADD_ITE2: out << "BV_ADD_ITE2"; break;
    case RewriteRuleKind::BV_ADD_MUL1: out << "BV_ADD_MUL1"; break;
    case RewriteRuleKind::BV_ADD_MUL2: out << "BV_ADD_MUL2"; break;
    case RewriteRuleKind::BV_ADD_SHL: out << "BV_ADD_SHL"; break;
    case RewriteRuleKind::BV_ADD_NORM_MUL_CONST:
      out << "BV_ADD_NORM_MUL_CONST";
      break;

    case RewriteRuleKind::BV_AND_EVAL: out << "BV_AND_EVAL"; break;
    case RewriteRuleKind::BV_AND_SPECIAL_CONST:
      out << "BV_AND_SPECIAL_CONST";
      break;
    case RewriteRuleKind::BV_AND_CONST: out << "BV_AND_CONST"; break;
    case RewriteRuleKind::BV_AND_IDEM1: out << "BV_AND_IDEM1"; break;
    case RewriteRuleKind::BV_AND_IDEM2: out << "BV_AND_IDEM2"; break;
    case RewriteRuleKind::BV_AND_IDEM3: out << "BV_AND_IDEM3"; break;
    case RewriteRuleKind::BV_AND_CONTRA1: out << "BV_AND_CONTRA1"; break;
    case RewriteRuleKind::BV_AND_CONTRA2: out << "BV_AND_CONTRA2"; break;
    case RewriteRuleKind::BV_AND_CONTRA3: out << "BV_AND_CONTRA3"; break;
    case RewriteRuleKind::BV_AND_SUBSUM1: out << "BV_AND_SUBSUM1"; break;
    case RewriteRuleKind::BV_AND_SUBSUM2: out << "BV_AND_SUBSUM2"; break;
    case RewriteRuleKind::BV_AND_RESOL1: out << "BV_AND_RESOL1"; break;
    case RewriteRuleKind::BV_AND_NOT_AND1: out << "BV_AND_NOT_AND1"; break;
    case RewriteRuleKind::BV_AND_NOT_AND2: out << "BV_AND_NOT_AND2"; break;
    case RewriteRuleKind::BV_AND_CONCAT: out << "BV_AND_CONCAT"; break;

    case RewriteRuleKind::BV_ASHR_EVAL: out << "BV_ASHR_EVAL"; break;
    case RewriteRuleKind::BV_ASHR_SPECIAL_CONST:
      out << "BV_ASHR_SPECIAL_CONST";
      break;

    case RewriteRuleKind::BV_CONCAT_EVAL: out << "BV_CONCAT_EVAL"; break;
    case RewriteRuleKind::BV_CONCAT_CONST: out << "BV_CONCAT_CONST"; break;
    case RewriteRuleKind::BV_CONCAT_EXTRACT: out << "BV_CONCAT_EXTRACT"; break;
    case RewriteRuleKind::BV_CONCAT_AND: out << "BV_CONCAT_AND"; break;

    case RewriteRuleKind::BV_EXTRACT_EVAL: out << "BV_EXTRACT_EVAL"; break;
    case RewriteRuleKind::BV_EXTRACT_FULL: out << "BV_EXTRACT_FULL"; break;
    case RewriteRuleKind::BV_EXTRACT_EXTRACT:
      out << "BV_EXTRACT_EXTRACT";
      break;
    case RewriteRuleKind::BV_EXTRACT_CONCAT_FULL_RHS:
      out << "BV_EXTRACT_CONCAT_FULL_RHS";
      break;
    case RewriteRuleKind::BV_EXTRACT_CONCAT_FULL_LHS:
      out << "BV_EXTRACT_CONCAT_FULL_LHS";
      break;
    case RewriteRuleKind::BV_EXTRACT_CONCAT_LHS_RHS:
      out << "BV_EXTRACT_CONCAT_LHS_RHS";
      break;
    case RewriteRuleKind::BV_EXTRACT_CONCAT: out << "BV_EXTRACT_CONCAT"; break;
    case RewriteRuleKind::BV_EXTRACT_AND: out << "BV_EXTRACT_AND"; break;
    case RewriteRuleKind::BV_EXTRACT_ITE: out << "BV_EXTRACT_ITE"; break;
    case RewriteRuleKind::BV_EXTRACT_ADD_MUL:
      out << "BV_EXTRACT_ADD_MUL";
      break;

    case RewriteRuleKind::BV_MUL_EVAL: out << "BV_MUL_EVAL"; break;
    case RewriteRuleKind::BV_MUL_SPECIAL_CONST:
      out << "BV_MUL_SPECIAL_CONST";
      break;
    case RewriteRuleKind::BV_MUL_CONST: out << "BV_MUL_CONST"; break;
    case RewriteRuleKind::BV_MUL_BV1: out << "BV_MUL_BV1"; break;
    case RewriteRuleKind::BV_MUL_CONST_ADD: out << "BV_MUL_CONST_ADD"; break;
    case RewriteRuleKind::BV_MUL_ITE: out << "BV_MUL_ITE"; break;
    case RewriteRuleKind::BV_MUL_NEG: out << "BV_MUL_NEG"; break;
    case RewriteRuleKind::BV_MUL_ONES: out << "BV_MUL_ONES"; break;
    case RewriteRuleKind::BV_MUL_SHL: out << "BV_MUL_SHL"; break;

    case RewriteRuleKind::BV_NOT_EVAL: out << "BV_NOT_EVAL"; break;
    case RewriteRuleKind::BV_NOT_BV_NOT: out << "BV_NOT_BV_NOT"; break;
    case RewriteRuleKind::BV_NOT_BV_NEG: out << "BV_NOT_BV_NEG"; break;
    case RewriteRuleKind::BV_NOT_BV_CONCAT: out << "BV_NOT_BV_CONCAT"; break;

    case RewriteRuleKind::BV_SHL_EVAL: out << "BV_SHL_EVAL"; break;
    case RewriteRuleKind::BV_SHL_SPECIAL_CONST:
      out << "BV_SHL_SPECIAL_CONST";
      break;
    case RewriteRuleKind::BV_SHL_CONST: out << "BV_SHL_CONST"; break;

    case RewriteRuleKind::BV_SHR_EVAL: out << "BV_SHR_EVAL"; break;
    case RewriteRuleKind::BV_SHR_SPECIAL_CONST:
      out << "BV_SHR_SPECIAL_CONST";
      break;
    case RewriteRuleKind::BV_SHR_CONST: out << "BV_SHR_CONST"; break;
    case RewriteRuleKind::BV_SHR_SAME: out << "BV_SHR_SAME"; break;
    case RewriteRuleKind::BV_SHR_NOT: out << "BV_SHR_NOT"; break;

    case RewriteRuleKind::BV_SLT_EVAL: out << "BV_SLT_EVAL"; break;
    case RewriteRuleKind::BV_SLT_SPECIAL_CONST:
      out << "BV_SLT_SPECIAL_CONST";
      break;
    case RewriteRuleKind::BV_SLT_SAME: out << "BV_SLT_SAME"; break;
    case RewriteRuleKind::BV_SLT_BV1: out << "BV_SLT_BV1"; break;
    case RewriteRuleKind::BV_SLT_ITE: out << "BV_SLT_ITE"; break;
    case RewriteRuleKind::BV_SLT_CONCAT: out << "BV_SLT_CONCAT"; break;

    case RewriteRuleKind::BV_UDIV_EVAL: out << "BV_UDIV_EVAL"; break;
    case RewriteRuleKind::BV_UDIV_SPECIAL_CONST:
      out << "BV_UDIV_SPECIAL_CONST";
      break;
    case RewriteRuleKind::BV_UDIV_BV1: out << "BV_UDIV_BV1"; break;
    case RewriteRuleKind::BV_UDIV_SAME: out << "BV_UDIV_SAME"; break;
    case RewriteRuleKind::BV_UDIV_POW2: out << "BV_UDIV_POW2"; break;
    case RewriteRuleKind::BV_UDIV_ITE: out << "BV_UDIV_ITE"; break;

    case RewriteRuleKind::BV_ULT_EVAL: out << "BV_ULT_EVAL"; break;
    case RewriteRuleKind::BV_ULT_SPECIAL_CONST:
      out << "BV_ULT_SPECIAL_CONST";
      break;
    case RewriteRuleKind::BV_ULT_SAME: out << "BV_ULT_SAME"; break;
    case RewriteRuleKind::BV_ULT_BV1: out << "BV_ULT_BV1"; break;
    case RewriteRuleKind::BV_ULT_ITE: out << "BV_ULT_ITE"; break;
    case RewriteRuleKind::BV_ULT_CONCAT: out << "BV_ULT_CONCAT"; break;

    case RewriteRuleKind::BV_UREM_EVAL: out << "BV_UREM_EVAL"; break;
    case RewriteRuleKind::BV_UREM_SPECIAL_CONST:
      out << "BV_UREM_SPECIAL_CONST";
      break;
    case RewriteRuleKind::BV_UREM_BV1: out << "BV_UREM_BV1"; break;
    case RewriteRuleKind::BV_UREM_SAME: out << "BV_UREM_SAME"; break;

    case RewriteRuleKind::BV_XOR_EVAL: out << "BV_XOR_EVAL"; break;
    case RewriteRuleKind::BV_XOR_SAME: out << "BV_XOR_SAME"; break;
    case RewriteRuleKind::BV_XOR_SPECIAL_CONST:
      out << "BV_XOR_SPECIAL_CONST";
      break;

    case RewriteRuleKind::BV_DEC_ELIM: out << "BV_DEC_ELIM"; break;
    case RewriteRuleKind::BV_INC_ELIM: out << "BV_INC_ELIM"; break;
    case RewriteRuleKind::BV_NAND_ELIM: out << "BV_NAND_ELIM"; break;
    case RewriteRuleKind::BV_NEG_ELIM: out << "BV_NEG_ELIM"; break;
    case RewriteRuleKind::BV_NEGO_ELIM: out << "BV_NEGO_ELIM"; break;
    case RewriteRuleKind::BV_NOR_ELIM: out << "BV_NOR_ELIM"; break;
    case RewriteRuleKind::BV_OR_ELIM: out << "BV_OR_ELIM"; break;
    case RewriteRuleKind::BV_REDAND_ELIM: out << "BV_REDAND_ELIM"; break;
    case RewriteRuleKind::BV_REDOR_ELIM: out << "BV_REDOR_ELIM"; break;
    case RewriteRuleKind::BV_REDXOR_ELIM: out << "BV_REDXOR_ELIM"; break;
    case RewriteRuleKind::BV_REPEAT_ELIM: out << "BV_REPEAT_ELIM"; break;
    case RewriteRuleKind::BV_ROL_ELIM: out << "BV_ROL_ELIM"; break;
    case RewriteRuleKind::BV_ROLI_ELIM: out << "BV_ROLI_ELIM"; break;
    case RewriteRuleKind::BV_ROR_ELIM: out << "BV_ROR_ELIM"; break;
    case RewriteRuleKind::BV_RORI_ELIM: out << "BV_RORI_ELIM"; break;
    case RewriteRuleKind::BV_SADDO_ELIM: out << "BV_SADDO_ELIM"; break;
    case RewriteRuleKind::BV_SDIV_ELIM: out << "BV_SDIV_ELIM"; break;
    case RewriteRuleKind::BV_SDIVO_ELIM: out << "BV_SDIVO_ELIM"; break;
    case RewriteRuleKind::BV_SGE_ELIM: out << "BV_SGE_ELIM"; break;
    case RewriteRuleKind::BV_SGT_ELIM: out << "BV_SGT_ELIM"; break;
    case RewriteRuleKind::BV_SIGN_EXTEND_ELIM:
      out << "BV_SIGN_EXTEND_ELIM";
      break;
    case RewriteRuleKind::BV_SLE_ELIM: out << "BV_SLE_ELIM"; break;
    case RewriteRuleKind::BV_SMOD_ELIM: out << "BV_SMOD_ELIM"; break;
    case RewriteRuleKind::BV_SMULO_ELIM: out << "BV_SMULO_ELIM"; break;
    case RewriteRuleKind::BV_SREM_ELIM: out << "BV_SREM_ELIM"; break;
    case RewriteRuleKind::BV_SSUBO_ELIM: out << "BV_SSUBO_ELIM"; break;
    case RewriteRuleKind::BV_SUB_ELIM: out << "BV_SUB_ELIM"; break;
    case RewriteRuleKind::BV_UADDO_ELIM: out << "BV_UADDO_ELIM"; break;
    case RewriteRuleKind::BV_UGE_ELIM: out << "BV_UGE_ELIM"; break;
    case RewriteRuleKind::BV_UGT_ELIM: out << "BV_UGT_ELIM"; break;
    case RewriteRuleKind::BV_ULE_ELIM: out << "BV_ULE_ELIM"; break;
    case RewriteRuleKind::BV_UMULO_ELIM: out << "BV_UMULO_ELIM"; break;
    case RewriteRuleKind::BV_USUBO_ELIM: out << "BV_USUBO_ELIM"; break;
    case RewriteRuleKind::BV_XNOR_ELIM: out << "BV_XNOR_ELIM"; break;
    case RewriteRuleKind::BV_XOR_ELIM: out << "BV_XOR_ELIM"; break;
    case RewriteRuleKind::BV_ZERO_EXTEND_ELIM:
      out << "BV_ZERO_EXTEND_ELIM";
      break;
    case RewriteRuleKind::BV_COMP_ELIM: out << "BV_COMP_ELIM"; break;

    case RewriteRuleKind::FP_ABS_EVAL: out << "FP_ABS_EVAL"; break;
    case RewriteRuleKind::FP_ABS_ABS_NEG: out << "FP_ABS_ABS_NEG"; break;

    case RewriteRuleKind::FP_ADD_EVAL: out << "FP_ADD_EVAL"; break;
    case RewriteRuleKind::FP_DIV_EVAL: out << "FP_DIV_EVAL"; break;
    case RewriteRuleKind::FP_FMA_EVAL: out << "FP_FMA_EVAL"; break;

    case RewriteRuleKind::FP_IS_INF_EVAL: out << "FP_IS_INF_EVAL"; break;
    case RewriteRuleKind::FP_IS_INF_ABS_NEG: out << "FP_IS_INF_ABS_NEG"; break;

    case RewriteRuleKind::FP_IS_NAN_EVAL: out << "FP_IS_NAN_EVAL"; break;
    case RewriteRuleKind::FP_IS_NAN_ABS_NEG: out << "FP_IS_NAN_ABS_NEG"; break;

    case RewriteRuleKind::FP_IS_NEG_EVAL: out << "FP_IS_NEG_EVAL"; break;

    case RewriteRuleKind::FP_IS_NORM_EVAL: out << "FP_IS_NORM_EVAL"; break;
    case RewriteRuleKind::FP_IS_NORM_ABS_NEG:
      out << "FP_IS_NORM_ABS_NEG";
      break;

    case RewriteRuleKind::FP_IS_POS_EVAL: out << "FP_IS_POS_EVAL"; break;

    case RewriteRuleKind::FP_IS_SUBNORM_EVAL:
      out << "FP_IS_SUBNORM_EVAL";
      break;
    case RewriteRuleKind::FP_IS_SUBNORM_ABS_NEG:
      out << "FP_IS_SUBNORM_ABS_NEG";
      break;

    case RewriteRuleKind::FP_IS_ZERO_EVAL: out << "FP_IS_ZERO_EVAL"; break;
    case RewriteRuleKind::FP_IS_ZERO_ABS_NEG:
      out << "FP_IS_ZERO_ABS_NEG";
      break;

    case RewriteRuleKind::FP_LEQ_EVAL: out << "FP_LEQ_EVAL"; break;
    case RewriteRuleKind::FP_LEQ_EQ: out << "FP_LEQ_EQ"; break;

    case RewriteRuleKind::FP_LT_EVAL: out << "FP_LT_EVAL"; break;
    case RewriteRuleKind::FP_LT_EQ: out << "FP_LT_EQ"; break;

    case RewriteRuleKind::FP_MIN_EVAL: out << "FP_MIN_EVAL"; break;
    case RewriteRuleKind::FP_MIN_EQ: out << "FP_MIN_EQ"; break;

    case RewriteRuleKind::FP_MAX_EVAL: out << "FP_MAX_EVAL"; break;
    case RewriteRuleKind::FP_MAX_EQ: out << "FP_MAX_EQ"; break;

    case RewriteRuleKind::FP_MUL_EVAL: out << "FP_MUL_EVAL"; break;

    case RewriteRuleKind::FP_NEG_EVAL: out << "FP_NEG_EVAL"; break;
    case RewriteRuleKind::FP_NEG_NEG: out << "FP_NEG_NEG"; break;

    case RewriteRuleKind::FP_REM_EVAL: out << "FP_REM_EVAL"; break;
    case RewriteRuleKind::FP_REM_SAME_DIV: out << "FP_REM_SAME_DIV"; break;
    case RewriteRuleKind::FP_REM_ABS_NEG: out << "FP_REM_ABS_NEG"; break;
    case RewriteRuleKind::FP_REM_NEG: out << "FP_REM_NEG"; break;

    case RewriteRuleKind::FP_RTI_EVAL: out << "FP_RTI_EVAL"; break;
    case RewriteRuleKind::FP_SQRT_EVAL: out << "FP_SQRT_EVAL"; break;
    case RewriteRuleKind::FP_TO_FP_FROM_BV_EVAL:
      out << "FP_TO_FP_FROM_BV_EVAL";
      break;
    case RewriteRuleKind::FP_TO_FP_FROM_FP_EVAL:
      out << "FP_TO_FP_FROM_FP_EVAL";
      break;
    case RewriteRuleKind::FP_TO_FP_FROM_SBV_EVAL:
      out << "FP_TO_FP_FROM_SBV_EVAL";
      break;
    case RewriteRuleKind::FP_TO_FP_FROM_SBV_BV1_ELIM:
      out << "FP_TO_FP_FROM_SBV_BV1_ELIM";
      break;
    case RewriteRuleKind::FP_TO_FP_FROM_UBV_EVAL:
      out << "FP_TO_FP_FROM_UBV_EVAL";
      break;

    case RewriteRuleKind::FP_EQUAL_ELIM: out << "FP_EQUAL_ELIM"; break;
    case RewriteRuleKind::FP_FP_ELIM: out << "FP_FP_ELIM"; break;
    case RewriteRuleKind::FP_GEQ_ELIM: out << "FP_GEQ_ELIM"; break;
    case RewriteRuleKind::FP_GT_ELIM: out << "FP_GT_ELIM"; break;
    case RewriteRuleKind::FP_SUB_ELIM: out << "FP_SUB_ELIM"; break;

    case RewriteRuleKind::ARRAY_PROP_SELECT: out << "ARRAY_PROP_SELECT"; break;
    case RewriteRuleKind::NORMALIZE_COMM: out << "NORMALIZE_COMM"; break;
    case RewriteRuleKind::EXISTS_ELIM: out << "EXISTS_ELIM"; break;
  }
  return out;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
