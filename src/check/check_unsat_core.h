#ifndef BZLA_CHECK_CHECK_UNSAT_CORE_H_INCLUDED

#include <unordered_map>
#include <vector>

#include "solving_context.h"
#include "util/logger.h"

namespace bzla::check {

class CheckUnsatCore
{
 public:
  CheckUnsatCore(SolvingContext& ctx);

  bool check();

 private:
  SolvingContext& d_ctx;
  util::Logger& d_logger;
};

}  // namespace bzla::check

#endif
