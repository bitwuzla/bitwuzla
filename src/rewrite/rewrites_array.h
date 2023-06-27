/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_REWRITE_REWRITES_ARRAY_H_INCLUDED
#define BZLA_REWRITE_REWRITES_ARRAY_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

template <>
Node RewriteRule<RewriteRuleKind::ARRAY_PROP_SELECT>::_apply(Rewriter& rewriter,
                                                             const Node& node);

}

#endif
