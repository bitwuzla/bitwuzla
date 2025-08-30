/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "rewrite/rewrites_bv_interp.h"

namespace bzla {

using namespace node;

template <>
Node
RewriteRule<RewriteRuleKind::INTERPOLANT_BV_EXTRACT>::_apply(Rewriter& rewriter,
                                                             const Node& node)
{
  assert(node.num_children() == 1);
  assert(node.num_indices() == 2);
  bool inverted     = node[0].is_inverted();
  const Node& node0 = inverted ? node[0][0] : node[0];

  uint64_t u = node.index(0);
  uint64_t l = node.index(1);
  if (node0.kind() == Kind::ITE)
  {
    Node res = rewriter.mk_node(
        Kind::ITE,
        {node0[0],
         rewriter.mk_node(Kind::BV_EXTRACT, {node0[1]}, {u, l}),
         rewriter.mk_node(Kind::BV_EXTRACT, {node0[2]}, {u, l})});
    return rewriter.invert_node_if(inverted, res);
  }
  else if (u < node0.type().bv_size() && node0.num_children() == 2
           && node0.kind() != Kind::BV_ADD && node0.kind() != Kind::BV_MUL
           && node0.kind() != Kind::BV_UDIV && node0.kind() != Kind::BV_UREM)
  {
    assert(node0.kind() != Kind::BV_SUB);
    assert(node0.kind() != Kind::BV_SDIV);
    assert(node0.kind() != Kind::BV_SMOD);
    assert(node0.kind() != Kind::BV_SREM);
    Node res = rewriter.mk_node(
        node0.kind(),
        {rewriter.mk_node(Kind::BV_EXTRACT, {node0[0]}, {u, l}),
         rewriter.mk_node(Kind::BV_EXTRACT, {node0[1]}, {u, l})});
    return rewriter.invert_node_if(inverted, res);
  }
  return node;
}
}  // namespace bzla
