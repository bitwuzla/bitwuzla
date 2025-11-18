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

#include "node/node_manager.h"
#include "sat/sat_solver_factory.h"
#include "terminator.h"
#include "util/exceptions.h"

namespace bzla {

Env::Env(NodeManager& nm,
         const option::Options& options,
         const std::string& name)
    : d_nm(nm),
      d_options(options),
      d_rewriter(*this, options.rewrite_level()),
      d_logger(options.log_level(),
               options.verbosity(),
               options.diagnostic_output_stream(),
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

NodeManager&
Env::nm()
{
  return d_nm;
}

void
Env::configure_terminator(Terminator* terminator)
{
  if (!sat::has_sat_solver_terminator_support(d_options))
  {
    throw Unsupported("terminator not supported in configured SAT solver");
  }
  d_terminator = terminator;
}

bool
Env::terminate() const
{
  if (d_terminator == nullptr) return false;
  return d_terminator->terminate();
}

}  // namespace bzla
