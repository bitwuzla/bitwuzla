#ifndef BZLA_PREPROCESS_PASS_FLATTEN_AND_H_INCLUDED
#define BZLA_PREPROCESS_PASS_FLATTEN_AND_H_INCLUDED

#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to flatten AND nodes.
 */
class PassFlattenAnd : public PreprocessingPass
{
 public:
  PassFlattenAnd(Env& env);

  void apply(AssertionVector& assertions) override;

 private:
  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_flattened;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
