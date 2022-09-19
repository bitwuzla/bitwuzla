#include "rewrite/rewrites_bv.h"

#include "node/node_manager.h"

namespace bzla {

template <>
Node
RewriteRule<RewriteRuleKind::BV_AND_EVAL>::_apply(Rewriter& rewriter,
                                                  const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  return NodeManager::get().mk_value(
      node[0].value<BitVector>().bvand(node[1].value<BitVector>()));
}

}  // namespace bzla
