#include "node/node_manager.h"
#include "rewrite/rewrites_bv.h"

namespace bzla {

using namespace node;

template <>
Node
RewriteRule<RewriteRuleKind::AND_EVAL>::_apply(Rewriter& rewriter,
                                               const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value() || !node[1].is_value()) return node;
  return NodeManager::get().mk_value(node[0].value<bool>()
                                     && node[1].value<bool>());
}

template <>
Node
RewriteRule<RewriteRuleKind::NOT_EVAL>::_apply(Rewriter& rewriter,
                                               const Node& node)
{
  (void) rewriter;
  if (!node[0].is_value()) return node;
  return NodeManager::get().mk_value(!node[0].value<bool>());
}

template <>
Node
RewriteRule<RewriteRuleKind::OR_ELIM>::_apply(Rewriter& rewriter,
                                              const Node& node)
{
  return rewriter.mk_node(
      Kind::NOT,
      {rewriter.mk_node(Kind::AND,
                        {rewriter.mk_node(Kind::NOT, {node[0]}),
                         rewriter.mk_node(Kind::NOT, {node[1]})})});
}

}  // namespace bzla
