/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_MAIN_TIME_LIMIT_H_INCLUDED
#define BZLA_MAIN_TIME_LIMIT_H_INCLUDED

#include <cstdint>

namespace bzla::main {

void set_time_limit(uint64_t time_limit);

void reset_time_limit();

}  // namespace bzla::main

#endif
