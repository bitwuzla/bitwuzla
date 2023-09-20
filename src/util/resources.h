/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_UTIL_RESOURCES_H_INCLUDED
#define BZLA_UTIL_RESOURCES_H_INCLUDED

#include <cstdint>

namespace bzla::util {

/** Get maximum memory usage in bytes. */
uint64_t maximum_memory_usage();

/** Get current memory usage in bytes. */
uint64_t current_memory_usage();
}

#endif
