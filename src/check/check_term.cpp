#if defined(BZLA_USE_CADICAL) || defined(BZLA_USE_CMS) \
    || defined(BZLA_USE_KISSAT)
#include "check/check_term.h"

#include "node/node_manager.h"
#include "solving_context.h"

namespace bzla::check {

using namespace node;

bool
check_term_equiv(NodeManager& nm, const Node& t1, const Node& t2)
{
  option::Options opts;
  opts.preprocess.set(false);
  opts.rewrite_level.set(0);
  opts.dbg_check_model.set(false);
  opts.dbg_check_unsat_core.set(false);
  SolvingContext ctx(nm, opts);

  ctx.assert_formula(nm.mk_node(Kind::DISTINCT, {t1, t2}));
  auto res = ctx.solve();
  return res == Result::UNSAT;
}

}  // namespace bzla::check
#endif
