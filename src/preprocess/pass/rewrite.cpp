#include "preprocess/pass/rewrite.h"

#include "env.h"

namespace bzla::preprocess::pass {

PassRewrite::PassRewrite(Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr), d_stats(env.statistics())
{
}

void
PassRewrite::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);
  auto& rw = d_env.rewriter();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    assertions.replace(i, rw.rewrite(assertions[i]));
  }
}

Node
PassRewrite::process(const Node& term)
{
  return d_env.rewriter().rewrite(term);
}

/* --- PassRewrite private -------------------------------------------------- */

PassRewrite::Statistics::Statistics(util::Statistics& stats)
    : time_apply(
        stats.new_stat<util::TimerStatistic>("preprocess::rewrite::time_apply"))
{
}

}  // namespace bzla::preprocess::pass
