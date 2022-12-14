#include "env.h"

#include "terminator.h"

namespace bzla {

Env::Env(const option::Options& options)
    : d_options(options),
      d_rewriter(*this, options.get<uint64_t>(option::Option::REWRITE_LEVEL))
{
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
