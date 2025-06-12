/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_GIMSATUL
/*------------------------------------------------------------------------*/

#include "sat/gimsatul.h"

extern "C" {
#include <gimsatul.h>
}

#include <cassert>

#include "util/exceptions.h"

/*------------------------------------------------------------------------*/

namespace bzla::sat {

/*------------------------------------------------------------------------*/

Gimsatul::Gimsatul(uint32_t threads) : d_nthreads(threads) {}

Gimsatul::~Gimsatul()
{
  if (d_gimsatul)
  {
    gimsatul_release(d_gimsatul);
  }
}

void
Gimsatul::add(int32_t lit)
{
  int32_t var = std::abs(lit);
  if (var > d_max_var)
  {
    d_max_var = var;
  }
  d_literals.push_back(lit);
  if (lit == 0)
  {
    ++d_num_clauses;
  }
}

void
Gimsatul::assume(int32_t lit)
{
  d_assumptions.push_back(lit);
}

int32_t
Gimsatul::value(int32_t lit)
{
  int32_t val = gimsatul_value(d_gimsatul, lit);
  if (val > 0) return 1;
  if (val < 0) return -1;
  return 0;
}

bool
Gimsatul::failed(int32_t lit)
{
  (void) lit;
  throw Error("Incremental solving not supported in Gimsatul");
  return false;
}

int32_t
Gimsatul::fixed(int32_t lit)
{
  (void) lit;
  throw Error("fixed() not supported in Gimsatul");
  return false;
}

Result
Gimsatul::solve()
{
  if (d_gimsatul)
  {
    gimsatul_release(d_gimsatul);
  }
  size_t size_before_assumptions = d_literals.size();

  int32_t max_var     = d_max_var;
  int32_t num_clauses = d_num_clauses;
  for (const auto a : d_assumptions)
  {
    int32_t abs_a = std::abs(a);
    if (abs_a > max_var)
    {
      max_var = abs_a;
    }
    d_literals.push_back(a);
    d_literals.push_back(0);
    ++num_clauses;
  }
  d_assumptions.clear();

  d_gimsatul = gimsatul_init(d_nthreads, d_max_var);
  gimsatul_add_clauses(
      d_gimsatul, max_var, d_literals.size(), d_literals.data(), num_clauses);
  d_literals.resize(size_before_assumptions);
  int32_t res = gimsatul_solve(d_gimsatul);
  if (res == 10) return Result::SAT;
  if (res == 20) return Result::UNSAT;
  return Result::UNKNOWN;
}

void
Gimsatul::configure_terminator(Terminator* terminator)
{
  if (terminator)
  {
    throw Unsupported("terminator not supported in Gimsatul");
  }
}

const char*
Gimsatul::get_version() const
{
  return gimsatul_version();
}

/*------------------------------------------------------------------------*/

}  // namespace bzla::sat

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
