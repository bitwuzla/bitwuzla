#include "env.h"

#include "terminator.h"

namespace bzla {

Env::Env(const option::Options& options, const std::string& name)
    : d_options(options),
      d_rewriter(*this, options.get<uint64_t>(option::Option::REWRITE_LEVEL)),
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
