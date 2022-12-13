#ifndef BZLA_ENV_H_INCLUDED
#define BZLA_ENV_H_INCLUDED

#include "option/option.h"
#include "rewrite/rewriter.h"
#include "util/statistics.h"

namespace bzla {

class Env
{
 public:
  Env(const option::Options& options = option::Options());

  const option::Options& options() const;

  util::Statistics& statistics();

  Rewriter& rewriter();

  //util::Logger& logger() const;

 private:
  const option::Options d_options;
  util::Statistics d_statistics;
  Rewriter d_rewriter;
};

}  // namespace bzla

#endif
