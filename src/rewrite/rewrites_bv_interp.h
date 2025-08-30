/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_REWRITE_REWRITES_BV_INTERP_H_INCLUDED
#define BZLA_REWRITE_REWRITES_BV_INTERP_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

template <>
Node RewriteRule<RewriteRuleKind::INTERPOLANT_BV_EXTRACT>::_apply(
    Rewriter& rewriter, const Node& node);

}

#endif
