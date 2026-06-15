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

#include <cstdint>

#include "type/type.h"

namespace bzla::type {

/**
 * Determine whether the cardinality of `type` is strictly less than `bound`.
 *
 * The cardinality is computed in a saturating fashion: the computation stops as
 * soon as the cardinality is known to reach `bound`. This avoids constructing
 * the astronomically large (and potentially unrepresentable) cardinalities of
 * array and function types, whose exact value is irrelevant once it exceeds the
 * bound we compare against.
 */
bool cardinality_lt(const Type& type, uint64_t bound);

}  // namespace bzla::type

#endif
