/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/rewrite.h"

#include "env.h"

namespace bzla::preprocess::pass {

PassRewrite::PassRewrite(Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "rw", "rewrite")
{
}

void
PassRewrite::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);
  auto& rw = d_env.rewriter();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (!processed(assertion))
    {
      const Node& rewritten = rw.rewrite(assertion);
      assertions.replace(i, rewritten);
      cache_assertion(rewritten);
    }
  }

#ifndef NDEBUG
  Env env(d_env.nm(), d_env.options());
  auto& rww = env.rewriter();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    const Node& rewritten = rww.rewrite(assertion);
    assert(rewritten == assertion);
  }
#endif
}

Node
PassRewrite::process(const Node& term)
{
  return d_env.rewriter().rewrite(term);
}

}  // namespace bzla::preprocess::pass
