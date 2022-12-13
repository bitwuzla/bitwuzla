#include "env.h"

namespace bzla {

Env::Env(const option::Options& options) : d_options(options), d_rewriter(*this)
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

}  // namespace bzla
