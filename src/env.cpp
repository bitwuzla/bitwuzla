/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "env.h"

#include "terminator.h"

namespace bzla {

Env::Env(const option::Options& options, const std::string& name)
    : d_options(options),
      d_rewriter(*this, options.rewrite_level()),
      d_logger(options.log_level(),
               options.verbosity(),
               name.empty() ? "" : "(" + name + ")")
{
  d_options.finalize();
}

const option::Options&
Env::options() const
{
  return d_options;
}

util::Statistics&
Env::statistics()
{
  return d_statistics;
}


Rewriter&
Env::rewriter()
{
  return d_rewriter;
}

util::Logger&
Env::logger()
{
  return d_logger;
}

void
Env::configure_terminator(Terminator* terminator)
{
  d_terminator = terminator;
}

bool
Env::terminate() const
{
  if (d_terminator == nullptr) return false;
  return d_terminator->terminate();
}

}  // namespace bzla
