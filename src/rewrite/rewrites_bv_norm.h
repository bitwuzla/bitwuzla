#ifndef BZLA_REWRITE_REWRITES_BV_NORM_H_INCLUDED
#define BZLA_REWRITE_REWRITES_BV_NORM_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

/* bvadd -------------------------------------------------------------------- */

// const_neg_lhs_add
// const_neg_rhs_add
template <>
Node RewriteRule<RewriteRuleKind::BV_ADD_NORM_MUL_CONST>::_apply(
    Rewriter& rewriter, const Node& node);

}  // namespace bzla

#endif
