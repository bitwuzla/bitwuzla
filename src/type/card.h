/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_TYPE_CARD_H_INCLUDED
#define BZLA_TYPE_CARD_H_INCLUDED

#include "type/type.h"
#include "util/integer.h"

namespace bzla::type {

util::Integer compute_cardinality(const Type& type);

}

#endif
