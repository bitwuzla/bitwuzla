/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_REWRITE_REWRITES_BV_NORM_H_INCLUDED
#define BZLA_REWRITE_REWRITES_BV_NORM_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

template <>
Node RewriteRule<RewriteRuleKind::NORM_BV_ADD_MUL>::_apply(Rewriter& rewriter,
                                                           const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::NORM_BV_CONCAT_BV_NOT>::_apply(Rewriter& rewriter,
                                                           const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::NORM_BV_NOT_OR_SHL>::_apply(
    Rewriter& rewriter, const Node& node);
template <>
Node RewriteRule<RewriteRuleKind::NORM_BV_SHL_NEG>::_apply(Rewriter& rewriter,
                                                           const Node& node);

// Reverse noramlization rules

template <>
Node RewriteRule<RewriteRuleKind::NORM_BV_EXTRACT_ADD_MUL_REV1>::_apply(
    Rewriter& rewriter, const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::NORM_BV_EXTRACT_ADD_MUL_REV2>::_apply(
    Rewriter& rewriter, const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::NORM_BV_EXTRACT_ADD_MUL_REV3>::_apply(
    Rewriter& rewriter, const Node& node);

// Reverse rule for BV_MUL_POW2
template <>
Node RewriteRule<RewriteRuleKind::NORM_BV_MUL_POW2_REV>::_apply(
    Rewriter& rewriter, const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::NORM_FACT_BV_ADD_MUL>::_apply(Rewriter& rewriter,
                                                             const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::NORM_FACT_BV_ADD_SHL>::_apply(Rewriter& rewriter,
                                                             const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::NORM_FACT_BV_SHL_MUL>::_apply(Rewriter& rewriter,
                                                             const Node& node);

template <>
Node RewriteRule<RewriteRuleKind::NORM_FACT_BV_MUL_SHL>::_apply(Rewriter& rewriter,
                                                             const Node& node);

}  // namespace bzla

#endif
