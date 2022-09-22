#include "rewrite/rewriter.h"

#include "node/node_manager.h"
#include "rewrite/rewrites_bv.h"
#include "rewrite/rewrites_fp.h"

#define BZLA_APPLY_RW_RULE(rw_rule)                                \
  do                                                               \
  {                                                                \
    std::tie(res, kind) =                                          \
        RewriteRule<RewriteRuleKind::rw_rule>::apply(*this, node); \
    if (res != node) goto DONE;                                    \
  } while (false);

namespace bzla {

/* === Rewriter public ====================================================== */

const Node&
Rewriter::rewrite(const Node& node)
{
  NodeManager& nm = NodeManager::get();
  std::vector<std::reference_wrapper<const Node>> visit{node};
  do
  {
    const Node& cur = visit.back();
    auto it         = d_cache.find(cur);
    if (it == d_cache.end())
    {
      d_cache.emplace(cur, Node());
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      if (cur.num_children())
      {
        std::vector<Node> children;
        std::vector<uint64_t> indices;
        for (const auto& c : cur)
        {
          children.push_back(d_cache.at(c));
        }
        for (size_t i = 0, n = cur.num_indices(); i < n; ++i)
        {
          indices.push_back(cur.index(i));
        }
        it->second = _rewrite(nm.mk_node(cur.kind(), children, indices));
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

/* === Rewriter private ===================================================== */

Node
Rewriter::_rewrite(const Node& node)
{
  Node res = node;

  switch (node.kind())
  {
    case node::Kind::EQUAL: res = rewrite_eq(node); break;
    case node::Kind::ITE: res = rewrite_ite(node); break;

    case node::Kind::BV_AND: res = rewrite_bv_and(node); break;
    case node::Kind::BV_ADD: res = rewrite_bv_add(node); break;
    case node::Kind::BV_ASHR: res = rewrite_bv_ashr(node); break;
    case node::Kind::BV_CONCAT: res = rewrite_bv_concat(node); break;
    case node::Kind::BV_EXTRACT: res = rewrite_bv_extract(node); break;
    case node::Kind::BV_MUL: res = rewrite_bv_mul(node); break;
    case node::Kind::BV_SHL: res = rewrite_bv_shl(node); break;
    case node::Kind::BV_SHR: res = rewrite_bv_shr(node); break;
    case node::Kind::BV_SLT: res = rewrite_bv_slt(node); break;
    case node::Kind::BV_UDIV: res = rewrite_bv_udiv(node); break;
    case node::Kind::BV_ULT: res = rewrite_bv_ult(node); break;
    case node::Kind::BV_UREM: res = rewrite_bv_urem(node); break;

    case node::Kind::FP_ABS: res = rewrite_fp_abs(node); break;
    case node::Kind::FP_ADD: res = rewrite_fp_add(node); break;
    case node::Kind::FP_DIV: res = rewrite_fp_div(node); break;

    case node::Kind::FP_IS_INF: res = rewrite_fp_is_inf(node); break;
    case node::Kind::FP_IS_NAN: res = rewrite_fp_is_nan(node); break;
    case node::Kind::FP_IS_NEG: res = rewrite_fp_is_neg(node); break;
    case node::Kind::FP_IS_NORM: res = rewrite_fp_is_normal(node); break;
    case node::Kind::FP_IS_POS: res = rewrite_fp_is_pos(node); break;
    case node::Kind::FP_IS_SUBNORM: res = rewrite_fp_is_subnormal(node); break;
    case node::Kind::FP_IS_ZERO: res = rewrite_fp_is_zero(node); break;

    case node::Kind::FP_LE: res = rewrite_fp_le(node); break;
    case node::Kind::FP_LT: res = rewrite_fp_lt(node); break;
    case node::Kind::FP_MAX: res = rewrite_fp_max(node); break;
    case node::Kind::FP_MIN: res = rewrite_fp_min(node); break;
    case node::Kind::FP_MUL: res = rewrite_fp_mul(node); break;
    case node::Kind::FP_NEG: res = rewrite_fp_neg(node); break;
    case node::Kind::FP_REM: res = rewrite_fp_rem(node); break;
    case node::Kind::FP_RTI: res = rewrite_fp_rti(node); break;
    case node::Kind::FP_SQRT: res = rewrite_fp_sqrt(node); break;

    case node::Kind::FP_TO_FP_FROM_BV:
      res = rewrite_fp_to_fp_from_bv(node);
      break;
    case node::Kind::FP_TO_FP_FROM_FP:
      res = rewrite_fp_to_fp_from_fp(node);
      break;
    case node::Kind::FP_TO_FP_FROM_SBV:
      res = rewrite_fp_to_fp_from_sbv(node);
      break;
    case node::Kind::FP_TO_FP_FROM_UBV:
      res = rewrite_fp_to_fp_from_ubv(node);
      break;

    case node::Kind::APPLY: res = rewrite_apply(node); break;
    case node::Kind::LAMBDA: res = rewrite_lambda(node); break;

    case node::Kind::FORALL: res = rewrite_forall(node); break;
    case node::Kind::EXISTS: res = rewrite_exists(node); break;

    default: assert(false);
  }

  return res;
}

/* -------------------------------------------------------------------------- */

Node
Rewriter::rewrite_eq(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_ite(const Node& node)
{
  // TODO
  return node;
}

/* BV rewrites -------------------------------------------------------------- */

Node
Rewriter::rewrite_bv_add(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_ADD_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_and(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_AND_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_ashr(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_ASHR_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_concat(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_CONCAT_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_extract(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_bv_mul(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_MUL_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_shl(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_SHL_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_shr(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_SHR_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_slt(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_SLT_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_udiv(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_UDIV_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_ult(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_ULT_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_urem(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_UREM_EVAL);
  // TODO

DONE:
  return res;
}

/* FP rewrites -------------------------------------------------------------- */

Node
Rewriter::rewrite_fp_abs(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_ABS_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_add(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_ADD_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_div(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_DIV_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_inf(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_INF_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_nan(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_NAN_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_neg(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_NEG_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_normal(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_NORM_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_pos(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_POS_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_subnormal(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_SUBNORM_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_zero(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_IS_ZERO_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_le(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_LE_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_lt(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_LT_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_max(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_fp_min(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_fp_mul(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_MUL_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_neg(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_NEG_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_rem(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_REM_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_rti(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_RTI_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_sqrt(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_SQRT_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_bv(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_BV_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_fp(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_FP_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_sbv(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_SBV_EVAL);
  // TODO

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_ubv(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_UBV_EVAL);
  // TODO

DONE:
  return res;
}

/* Array rewrites ----------------------------------------------------------- */

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

Node
Rewriter::rewrite_exists(const Node& node)
{
  // TODO
  return node;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
