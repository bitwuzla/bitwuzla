#ifndef BZLA_REWRITE_REWRITER_H_INCLUDED
#define BZLA_REWRITE_REWRITER_H_INCLUDED

#include <unordered_map>

#include "node/node.h"

namespace bzla {

/* -------------------------------------------------------------------------- */

class Rewriter
{
 public:
  const Node& rewrite(const Node& node);

 private:
  Node _rewrite(const Node& node);

  Node rewrite_eq(const Node& node);
  Node rewrite_ite(const Node& node);

  Node rewrite_bv_add(const Node& node);
  Node rewrite_bv_and(const Node& node);
  Node rewrite_bv_ashr(const Node& node);
  Node rewrite_bv_concat(const Node& node);
  Node rewrite_bv_extract(const Node& node);
  Node rewrite_bv_mul(const Node& node);
  Node rewrite_bv_shl(const Node& node);
  Node rewrite_bv_shr(const Node& node);
  Node rewrite_bv_slt(const Node& node);
  Node rewrite_bv_udiv(const Node& node);
  Node rewrite_bv_ult(const Node& node);
  Node rewrite_bv_urem(const Node& node);

  Node rewrite_fp_abs(const Node& node);
  Node rewrite_fp_add(const Node& node);
  Node rewrite_fp_div(const Node& node);
  Node rewrite_fp_is_tester(const Node& node);
  Node rewrite_fp_le(const Node& node);
  Node rewrite_fp_lt(const Node& node);
  Node rewrite_fp_max(const Node& node);
  Node rewrite_fp_min(const Node& node);
  Node rewrite_fp_mul(const Node& node);
  Node rewrite_fp_neg(const Node& node);
  Node rewrite_fp_rem(const Node& node);
  Node rewrite_fp_rti(const Node& node);
  Node rewrite_fp_sqrt(const Node& node);
  Node rewrite_fp_to_fp_from_bv(const Node& node);
  Node rewrite_fp_to_fp_from_fp(const Node& node);
  Node rewrite_fp_to_fp_from_sbv(const Node& node);
  Node rewrite_fp_to_fp_from_ubv(const Node& node);

  Node rewrite_apply(const Node& node);
  Node rewrite_lambda(const Node& node);

  Node rewrite_forall(const Node& node);
  Node rewrite_exists(const Node& node);

  std::unordered_map<Node, Node> d_cache;
};

/* -------------------------------------------------------------------------- */

enum class RewriteRuleKind
{
  BV_AND_EVAL,
};

template <RewriteRuleKind K>
class RewriteRule
{
 public:
  static std::pair<Node, RewriteRuleKind> apply(Rewriter& rewriter,
                                                const Node& node)
  {
    return std::make_pair(_apply(rewriter, node), K);
  }

 private:
  static Node _apply(Rewriter& rewriter, const Node& node);
};

/* -------------------------------------------------------------------------- */

}  // namespace bzla

#endif
