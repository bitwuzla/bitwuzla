/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#if defined(BZLA_USE_CADICAL) || defined(BZLA_USE_CMS) \
    || defined(BZLA_USE_KISSAT)
#ifndef BZLA_CHECK_CHECK_TERM_H_INCLUDED

#include "node/node.h"

namespace bzla::check {

bool check_term_equiv(NodeManager& nm, const Node& t1, const Node& t2);

}  // namespace bzla::check

#endif
#endif
