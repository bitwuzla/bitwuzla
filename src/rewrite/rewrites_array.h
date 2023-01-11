#ifndef BZLA_REWRITE_REWRITES_ARRAY_H_INCLUDED
#define BZLA_REWRITE_REWRITES_ARRAY_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

template <>
Node RewriteRule<RewriteRuleKind::ARRAY_PROP_SELECT>::_apply(Rewriter& rewriter,
                                                             const Node& node);

}

#endif
