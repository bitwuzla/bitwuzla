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
class TimeoutTerminator : public Terminator
{
 public:
  ~TimeoutTerminator() override{};
  bool terminate() override;

  void set_terminator(Terminator* terminator);
  void set(uint64_t time_limit);

 private:
  std::chrono::system_clock::time_point d_deadline;
  Terminator* d_terminator = nullptr;  // Wraps already configured terminator.
};

}  // namespace bzla

#endif
