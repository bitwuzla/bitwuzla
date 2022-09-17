#include "rewrite/rewriter.h"

#include "rewrite/rewrites_bv.h"

#define BZLA_APPLY_RW_RULE(rw_rule)                                \
  do                                                               \
  {                                                                \
    std::tie(res, kind) =                                          \
        RewriteRule<RewriteRuleKind::rw_rule>::apply(*this, node); \
    if (res != node) goto DONE;                                    \
  } while (false);

namespace bzla {

/* === Rewriter public ====================================================== */

void
Rewriter::rewrite(const Node& node)
{
  // TODO
}

/* === Rewriter private ===================================================== */

Node
Rewriter::_rewrite(const Node& node)
{
  // query cache
  auto it = d_cache.find(node);
  if (it != d_cache.end())
  {
    return it->second;
  }
  // rewrite
  Node res = node;

  switch (node.get_kind())
  {
    case node::Kind::BV_AND: res = rewrite_bv_and(node); break;

    default: assert(false);
  }
  // cache
  if (res != node)
  {
    d_cache.emplace(node, res);
  }

  return res;
}

/* -------------------------------------------------------------------------- */

Node
rewrite_eq(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_ite(const Node& node)
{
  // TODO
  return node;
}

/* BV rewrites -------------------------------------------------------------- */

Node
Rewriter::rewrite_bv_add(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_bv_and(const Node& node)
{
  RewriteRuleKind kind;
  Node res;

  BZLA_APPLY_RW_RULE(BV_AND_EVAL);
  // TODO

DONE:
  return node;
}

Node
Rewriter::rewrite_bv_ashr(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_bv_concat(const Node& node)
{
  // TODO
  return node;
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
  // TODO
  return node;
}

Node
Rewriter::rewrite_bv_shl(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_bv_shr(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_bv_slt(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_bv_udiv(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_bv_ult(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_bv_urem(const Node& node)
{
  // TODO
  return node;
}

/* FP rewrites -------------------------------------------------------------- */

Node
rewrite_fp_abs(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_add(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_div(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_is_tester(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_le(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_lt(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_max(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_min(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_mul(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_neg(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_rem(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_rti(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_sqrt(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_to_fp_from_bv(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_to_fp_from_fp(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_to_fp_from_sbv(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_fp_to_fp_from_ubv(const Node& node)
{
  // TODO
  return node;
}

/* Array rewrites ----------------------------------------------------------- */

Node
rewrite_apply(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_lambda(const Node& node)
{
  // TODO
  return node;
}

/* Quant rewrites ----------------------------------------------------------- */

Node
rewrite_forall(const Node& node)
{
  // TODO
  return node;
}

Node
rewrite_exists(const Node& node)
{
  // TODO
  return node;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
