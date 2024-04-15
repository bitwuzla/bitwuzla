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

}  // namespace bzla

#endif
