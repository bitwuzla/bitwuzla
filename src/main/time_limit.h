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

namespace bitwuzla::parser {
class Parser;
}

namespace bzla::main {

// Sets a time limit of `time_limit` milliseconds by starting a detached thread
// that terminates the process once the limit is reached. A value of 0 disables
// the time limit.
void set_time_limit(uint64_t time_limit);

// Cancels a time limit previously set via set_time_limit(), e.g., once
// solving has finished. Has no effect if no time limit was set.
void reset_time_limit();

// Sets parser instance to print Bitwuzla statistics when time limit is reached.
void print_statistics_time_limit(bitwuzla::parser::Parser* parser);

}  // namespace bzla::main

#endif
