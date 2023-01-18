#include "rewrite/rewrites_bv_norm.h"

namespace bzla {

using namespace node;

/**
 * match:  (bvadd (bvnot (bvmul (_ bvX N) a)) b)
 * result: (bvadd (bvdec (bvmul (bvnot (_ bvX N) a))))
 * match:  ~(c * a) + b
 * result: ((-c) * a - 1) + b
 */
namespace {
Node
_rw_bv_add_norm_mul_const(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].is_inverted() && node[idx0][0].kind() == Kind::BV_MUL)
  {
    if (node[idx0][0][0].is_value())
    {
      return rewriter.mk_node(
          Kind::BV_ADD,
          {rewriter.mk_node(
               Kind::BV_DEC,
               {rewriter.mk_node(
                   Kind::BV_MUL,
                   {rewriter.mk_node(Kind::BV_NEG, {node[idx0][0][0]}),
                    node[idx0][0][1]})}),
           node[idx1]});
    }
    else if (node[idx0][0][1].is_value())
    {
      return rewriter.mk_node(
          Kind::BV_ADD,
          {rewriter.mk_node(
               Kind::BV_DEC,
               {rewriter.mk_node(
                   Kind::BV_MUL,
                   {rewriter.mk_node(Kind::BV_NEG, {node[idx0][0][1]}),
                    node[idx0][0][0]})}),
           node[idx1]});
    }
  }
  return node;
}
}  // namespace

template <>
Node
RewriteRule<RewriteRuleKind::BV_ADD_NORM_MUL_CONST>::_apply(Rewriter& rewriter,
                                                            const Node& node)
{
  Node res = _rw_bv_add_norm_mul_const(rewriter, node, 0);
  if (res == node)
  {
    res = _rw_bv_add_norm_mul_const(rewriter, node, 1);
  }
  return res;
}

}  // namespace bzla
