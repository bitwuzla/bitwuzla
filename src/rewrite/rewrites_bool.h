#ifndef BZLA_REWRITE_REWRITES_BOOL_H_INCLUDED
#define BZLA_REWRITE_REWRITES_BOOL_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

template <>
Node RewriteRule<RewriteRuleKind::AND_EVAL>::_apply(Rewriter& rewriter,
                                                    const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::NOT_EVAL>::_apply(Rewriter& rewriter,
                                                    const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::OR_ELIM>::_apply(Rewriter& rewriter,
                                                   const Node& node);

}  // namespace bzla

#endif
