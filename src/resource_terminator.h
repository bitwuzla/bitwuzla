/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_TIMEOUT_TERMINATOR_H_INCLUDED
#define BZLA_TIMEOUT_TERMINATOR_H_INCLUDED

#include <chrono>
#include <cstdint>

#include "terminator.h"

namespace bzla {

/**
 * Timeout terminator class to enforce --time-limit-per option.
 *
 * If a non-timeout terminator was already configured, the existing terminator
 * is wrapped and not overwritten, i.e., both terminators are active.
 */
class ResourceTerminator : public Terminator
{
 public:
  ~ResourceTerminator() override{};
  bool terminate() override;

  void set_terminator(Terminator* terminator);
  void set_time_limit(uint64_t time_limit);
  void set_memory_limit(uint64_t memory_limit);

 private:
  std::chrono::system_clock::time_point d_deadline;
  uint64_t d_time_limit    = 0;
  uint64_t d_memory_limit  = 0;
  Terminator* d_terminator = nullptr;  // Wraps already configured terminator.
};

}  // namespace bzla

#endif
