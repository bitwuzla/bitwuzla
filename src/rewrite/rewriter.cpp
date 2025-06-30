/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "rewrite/rewriter.h"

#include "env.h"
#include "node/node_kind.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_set.h"
#include "util/logger.h"

#define BZLA_APPLY_RW_RULE(rw_rule)                                \
  do                                                               \
  {                                                                \
    std::tie(res, kind) =                                          \
        RewriteRule<RewriteRuleKind::rw_rule>::apply(*this, node); \
    if (res != node)                                               \
    {                                                              \
      d_stats.rewrites << kind;                                    \
      ++d_stats.num_rewrites;                                      \
      goto DONE;                                                   \
    }                                                              \
  } while (false);

#define BZLA_ELIM_KIND_IMPL(name, rule)           \
  Node Rewriter::rewrite_##name(const Node& node) \
  {                                               \
    RewriteRuleKind kind;                         \
    Node res;                                     \
                                                  \
    BZLA_APPLY_RW_RULE(rule);                     \
                                                  \
  DONE:                                           \
    return res;                                   \
  }

namespace bzla {

using namespace node;

#ifndef NDEBUG
namespace {

std::pair<size_t, size_t>
diff(uint64_t max_id, const Node& rewritten)
{
  node::node_ref_vector visit{rewritten};
  std::vector<size_t> depths{0};
  size_t max_depth = 0;
  node::unordered_node_ref_set cache;
  do
  {
    const Node& cur = visit.back();
    size_t depth    = depths.back();
    visit.pop_back();
    depths.pop_back();
    if (cur.id() < max_id)
    {
      continue;
    }
    if (depth > max_depth)
    {
      max_depth = depth;
    }
    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      for (size_t i = 0; i < cur.num_children(); ++i)
      {
        depths.push_back(depth + 1);
      }
    }
  } while (!visit.empty());
  return std::make_pair(cache.size(), max_depth);
}

}  // namespace
#endif

/* === Rewriter public ====================================================== */

Rewriter::Rewriter(Env& env,
                   preprocess::SimplifyCache& cache,
                   uint8_t level,
                   const std::string& id)
    : d_env(env),
      d_logger(env.logger()),
      d_level(level),
      d_arithmetic(level == LEVEL_ARITHMETIC),
      d_preproc_cache(cache),
      d_stats(env.statistics(),
              "rewriter::" + (id.empty() ? "" : "(" + id + ")::"))
{
  static_assert(Rewriter::LEVEL_ARITHMETIC > Rewriter::LEVEL_MAX);
  assert(d_level <= Rewriter::LEVEL_ARITHMETIC);
  (void) d_env;  // only used in debug mode
}

Node
Rewriter::rewrite(const Node& node)
{
  std::vector<Node> visit{node};
  std::unordered_map<Node, Node> cache;
  do
  {
    Node cur = visit.back();

    if (d_preproc_cache.cached(cur,
                               preprocess::SimplifyCache::Cacher::REWRITER))
    {
      cache.emplace(cur, d_preproc_cache.get(cur));
      visit.pop_back();
      continue;
    }

    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      for (const Node& child : cur)
      {
        visit.push_back(d_preproc_cache.get(child));
      }
      continue;
    }
    else if (it->second.is_null())
    {
      if (cur.num_children())
      {
#ifndef NDEBUG
        // Reset nodes counter
        d_num_nodes = 0;
        // Save current maximum node id
        int64_t max_id = d_env.nm().max_node_id();
#endif
        it->second = _rewrite(d_preproc_cache.rebuild_node(nm(), cur));
#ifndef NDEBUG
        uint64_t thresh = d_env.options().dbg_rw_node_thresh();
        if (thresh > 0 && d_num_nodes > 0)
        {
          auto [new_nodes, depth] = diff(max_id, it->second);
          Warn(new_nodes >= thresh) << "_rewrite() introduced " << new_nodes
                                    << " new nodes up to depth " << depth;
        }
#endif
      }
      else
      {
        it->second = cur;
      }
      d_preproc_cache.add(
          cur, it->second, preprocess::SimplifyCache::Cacher::REWRITER);
    }
    visit.pop_back();
  } while (!visit.empty());
  return d_preproc_cache.get(node);
}

Node
Rewriter::eval(const Node& node)
{
  if (d_level == 0)
  {
    return eval_no_cache(node);
  }

  std::vector<Node> visit{node};
  std::unordered_map<Node, Node> cache;
  do
  {
    Node cur = visit.back();

    if (d_preproc_cache.cached(cur,
                               preprocess::SimplifyCache::Cacher::REWRITER))
    {
      cache.emplace(cur, d_preproc_cache.get(cur));
      visit.pop_back();
      continue;
    }

    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      for (const Node& child : cur)
      {
        visit.push_back(d_preproc_cache.get(child));
      }
      continue;
    }
    else if (it->second.is_null())
    {
      if (cur.num_children())
      {
        it->second = _eval(d_preproc_cache.rebuild_node(nm(), cur));
      }
      else
      {
        it->second = cur;
      }
      d_preproc_cache.add(
          cur, it->second, preprocess::SimplifyCache::Cacher::REWRITER);
    }
    visit.pop_back();
  } while (!visit.empty());
  return d_preproc_cache.get(node);
}

Node
Rewriter::mk_node(node::Kind kind,
                  const std::vector<Node>& children,
                  const std::vector<uint64_t>& indices)
{
#ifndef NDEBUG
  uint64_t max_id = d_env.nm().max_node_id();
#endif
  Node node = d_env.nm().mk_node(kind, children, indices);
  ++d_num_rec_calls;
#ifndef NDEBUG
  auto [it, inserted] = d_rec_cache.insert(node);
  assert(inserted);  // Rewrite cycle detected if this fails.
#endif
  const Node& res = _rewrite(node);
#ifndef NDEBUG
  if (res.id() >= max_id)
  {
    ++d_num_nodes;
  }
  d_rec_cache.erase(node);
#endif
  --d_num_rec_calls;
  return res;
}

Node
Rewriter::invert_node(const Node& node)
{
  assert(node.type().is_bool() || node.type().is_bv());
  if (node.type().is_bool())
  {
    return mk_node(node::Kind::NOT, {node});
  }
  return mk_node(node::Kind::BV_NOT, {node});
}

Node
Rewriter::invert_node_if(bool condition, const Node& node)
{
  assert(node.type().is_bool() || node.type().is_bv());
  return condition ? invert_node(node) : node;
}

bool
Rewriter::is_or(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::OR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.is_inverted() && node[0].kind() == Kind::AND)
  {
    child0 = node[0][0].is_inverted() ? node[0][0][0] : invert_node(node[0][0]);
    child1 = node[0][1].is_inverted() ? node[0][1][0] : invert_node(node[0][1]);
    return true;
  }
  return false;
}

bool
Rewriter::is_xor(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::XOR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  Node or0, or1;
  if (node.kind() == Kind::AND)
  {
    if ((is_or(node[0], or0, or1) && node[1].is_inverted()
         && node[1][0].kind() == Kind::AND
         && (node[1][0][0] == or0 || node[1][0][0] == or1)
         && (node[1][0][1] == or0 || node[1][0][1] == or1))
        || (is_or(node[1], or0, or1) && node[0].is_inverted()
            && node[0][0].kind() == Kind::AND
            && (node[0][0][0] == or0 || node[0][0][0] == or1)
            && (node[0][0][1] == or0 || node[0][0][1] == or1)))
    {
      child0 = or0;
      child1 = or1;
      return true;
    }
  }
  return false;
}

bool
Rewriter::is_xnor(const Node& node, Node& child0, Node& child1)
{
  if (node.is_inverted())
  {
    Node xor0, xor1;
    if (is_xor(node[0], xor0, xor1))
    {
      child0 = xor0;
      child1 = xor1;
      return true;
    }
  }
  return false;
}

bool
Rewriter::is_bv_neg(const Node& node, Node& child)
{
  Node one = d_env.nm().mk_value(BitVector::mk_one(node.type().bv_size()));
  if (node.kind() == Kind::BV_NEG)
  {
    child = node[0];
    return true;
  }
  if (node.kind() == Kind::BV_ADD)
  {
    if (node[0] == one)
    {
      child = invert_node(node[1]);
      return true;
    }
    if (node[1] == one)
    {
      child = invert_node(node[0]);
      return true;
    }
  }
  return false;
}

bool
Rewriter::is_bv_or(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::BV_OR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.is_inverted() && node[0].kind() == Kind::BV_AND)
  {
    child0 = node[0][0].is_inverted() ? node[0][0][0] : invert_node(node[0][0]);
    child1 = node[0][1].is_inverted() ? node[0][1][0] : invert_node(node[0][1]);
    return true;
  }
  return false;
}

bool
Rewriter::is_bv_sub(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::BV_SUB)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.kind() == Kind::BV_ADD)
  {
    if (is_bv_neg(node[0], child1))
    {
      child0 = node[1];
      return true;
    }
    if (is_bv_neg(node[1], child1))
    {
      child0 = node[0];
      return true;
    }
  }
  return false;
}

bool
Rewriter::is_bv_xnor(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::BV_XNOR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.is_inverted() && node[0].kind() == Kind::BV_XOR)
  {
    child0 = node[0][0];
    child1 = node[0][1];
    return true;
  }
  return false;
}

NodeManager&
Rewriter::nm()
{
  return d_env.nm();
}

void
Rewriter::configure_parents_count(
    std::unordered_map<Node, uint64_t>* parents_map)
{
  d_parents_map = parents_map;
}

/* === Rewriter private ===================================================== */

const Node&
Rewriter::_rewrite(const Node& node)
{
  // Lookup rewrite cache
  if (d_preproc_cache.cached(node, preprocess::SimplifyCache::Cacher::REWRITER))
  {
    return d_preproc_cache.get(node);
  }

  // Limit rewrite recursion depth if we run into rewrite cycles in production
  // mode. Ideally, this should not happen, but if it does, we do not crash.
  if (d_num_rec_calls >= RECURSION_LIMIT)
  {
    assert(false);
    d_recursion_limit_reached = true;
    return node;
  }

  // Normalize before rewriting
  Node n = normalize_commutative(node);

  Node res;
  switch (n.kind())
  {
    case node::Kind::AND: res = rewrite_and(n); break;
    case node::Kind::DISTINCT: res = rewrite_distinct(n); break;
    case node::Kind::IMPLIES: res = rewrite_implies(n); break;
    case node::Kind::NOT: res = rewrite_not(n); break;
    case node::Kind::OR: res = rewrite_or(n); break;
    case node::Kind::XOR: res = rewrite_xor(n); break;

    case node::Kind::EQUAL: res = rewrite_eq(n); break;
    case node::Kind::ITE: res = rewrite_ite(n); break;

    case node::Kind::BV_AND: res = rewrite_bv_and(n); break;
    case node::Kind::BV_ADD: res = rewrite_bv_add(n); break;
    case node::Kind::BV_ASHR: res = rewrite_bv_ashr(n); break;
    case node::Kind::BV_CONCAT: res = rewrite_bv_concat(n); break;
    case node::Kind::BV_DEC: res = rewrite_bv_dec(n); break;
    case node::Kind::BV_EXTRACT: res = rewrite_bv_extract(n); break;
    case node::Kind::BV_INC: res = rewrite_bv_inc(n); break;
    case node::Kind::BV_MUL: res = rewrite_bv_mul(n); break;
    case node::Kind::BV_NOT: res = rewrite_bv_not(n); break;
    case node::Kind::BV_SHL: res = rewrite_bv_shl(n); break;
    case node::Kind::BV_SHR: res = rewrite_bv_shr(n); break;
    case node::Kind::BV_SLT: res = rewrite_bv_slt(n); break;
    case node::Kind::BV_UDIV: res = rewrite_bv_udiv(n); break;
    case node::Kind::BV_ULT: res = rewrite_bv_ult(n); break;
    case node::Kind::BV_UREM: res = rewrite_bv_urem(n); break;
    case node::Kind::BV_COMP: res = rewrite_bv_comp(n); break;

    /* Eliminated bit-vector operators */
    case node::Kind::BV_NAND: res = rewrite_bv_nand(n); break;
    case node::Kind::BV_NEG: res = rewrite_bv_neg(n); break;
    case node::Kind::BV_NEGO: res = rewrite_bv_nego(n); break;
    case node::Kind::BV_NOR: res = rewrite_bv_nor(n); break;
    case node::Kind::BV_OR: res = rewrite_bv_or(n); break;
    case node::Kind::BV_REDAND: res = rewrite_bv_redand(n); break;
    case node::Kind::BV_REDOR: res = rewrite_bv_redor(n); break;
    case node::Kind::BV_REDXOR: res = rewrite_bv_redxor(n); break;
    case node::Kind::BV_REPEAT: res = rewrite_bv_repeat(n); break;
    case node::Kind::BV_ROL: res = rewrite_bv_rol(n); break;
    case node::Kind::BV_ROLI: res = rewrite_bv_roli(n); break;
    case node::Kind::BV_ROR: res = rewrite_bv_ror(n); break;
    case node::Kind::BV_RORI: res = rewrite_bv_rori(n); break;
    case node::Kind::BV_SADDO: res = rewrite_bv_saddo(n); break;
    case node::Kind::BV_SDIV: res = rewrite_bv_sdiv(n); break;
    case node::Kind::BV_SDIVO: res = rewrite_bv_sdivo(n); break;
    case node::Kind::BV_SGE: res = rewrite_bv_sge(n); break;
    case node::Kind::BV_SGT: res = rewrite_bv_sgt(n); break;
    case node::Kind::BV_SIGN_EXTEND: res = rewrite_bv_sign_extend(n); break;
    case node::Kind::BV_SLE: res = rewrite_bv_sle(n); break;
    case node::Kind::BV_SMOD: res = rewrite_bv_smod(n); break;
    case node::Kind::BV_SMULO: res = rewrite_bv_smulo(n); break;
    case node::Kind::BV_SREM: res = rewrite_bv_srem(n); break;
    case node::Kind::BV_SSUBO: res = rewrite_bv_ssubo(n); break;
    case node::Kind::BV_SUB: res = rewrite_bv_sub(n); break;
    case node::Kind::BV_UMULO: res = rewrite_bv_umulo(n); break;
    case node::Kind::BV_UADDO: res = rewrite_bv_uaddo(n); break;
    case node::Kind::BV_UGE: res = rewrite_bv_uge(n); break;
    case node::Kind::BV_UGT: res = rewrite_bv_ugt(n); break;
    case node::Kind::BV_ULE: res = rewrite_bv_ule(n); break;
    case node::Kind::BV_USUBO: res = rewrite_bv_usubo(n); break;
    case node::Kind::BV_XNOR: res = rewrite_bv_xnor(n); break;
    case node::Kind::BV_XOR: res = rewrite_bv_xor(n); break;
    case node::Kind::BV_ZERO_EXTEND: res = rewrite_bv_zero_extend(n); break;

    case node::Kind::FP_ABS: res = rewrite_fp_abs(n); break;
    case node::Kind::FP_ADD: res = rewrite_fp_add(n); break;
    case node::Kind::FP_DIV: res = rewrite_fp_div(n); break;
    case node::Kind::FP_EQUAL: res = rewrite_fp_equal(n); break;
    case node::Kind::FP_FMA: res = rewrite_fp_fma(n); break;
    case node::Kind::FP_FP: res = rewrite_fp_fp(n); break;
    case node::Kind::FP_GEQ: res = rewrite_fp_geq(n); break;
    case node::Kind::FP_GT: res = rewrite_fp_gt(n); break;

    case node::Kind::FP_IS_INF: res = rewrite_fp_is_inf(n); break;
    case node::Kind::FP_IS_NAN: res = rewrite_fp_is_nan(n); break;
    case node::Kind::FP_IS_NEG: res = rewrite_fp_is_neg(n); break;
    case node::Kind::FP_IS_NORMAL: res = rewrite_fp_is_normal(n); break;
    case node::Kind::FP_IS_POS: res = rewrite_fp_is_pos(n); break;
    case node::Kind::FP_IS_SUBNORMAL: res = rewrite_fp_is_subnormal(n); break;
    case node::Kind::FP_IS_ZERO: res = rewrite_fp_is_zero(n); break;

    case node::Kind::FP_LEQ: res = rewrite_fp_leq(n); break;
    case node::Kind::FP_LT: res = rewrite_fp_lt(n); break;
    case node::Kind::FP_MAX: res = rewrite_fp_max(n); break;
    case node::Kind::FP_MIN: res = rewrite_fp_min(n); break;
    case node::Kind::FP_MUL: res = rewrite_fp_mul(n); break;
    case node::Kind::FP_NEG: res = rewrite_fp_neg(n); break;
    case node::Kind::FP_REM: res = rewrite_fp_rem(n); break;
    case node::Kind::FP_RTI: res = rewrite_fp_rti(n); break;
    case node::Kind::FP_SQRT: res = rewrite_fp_sqrt(n); break;
    case node::Kind::FP_SUB: res = rewrite_fp_sub(n); break;

    case node::Kind::FP_TO_FP_FROM_BV: res = rewrite_fp_to_fp_from_bv(n); break;
    case node::Kind::FP_TO_FP_FROM_FP: res = rewrite_fp_to_fp_from_fp(n); break;
    case node::Kind::FP_TO_FP_FROM_SBV:
      res = rewrite_fp_to_fp_from_sbv(n);
      break;
    case node::Kind::FP_TO_FP_FROM_UBV:
      res = rewrite_fp_to_fp_from_ubv(n);
      break;

    // No rewrites for FP_TO_(U|S)BV conversion yet
    case node::Kind::FP_TO_SBV:
    case node::Kind::FP_TO_UBV: res = n; break;

    // There are no rewrites for constant arrays.
    case node::Kind::CONST_ARRAY: res = n; break;

    case node::Kind::SELECT: res = rewrite_select(n); break;
    case node::Kind::STORE: res = rewrite_store(n); break;

    case node::Kind::APPLY: res = rewrite_apply(n); break;
    case node::Kind::LAMBDA: res = rewrite_lambda(n); break;

    case node::Kind::FORALL: res = rewrite_forall(n); break;
    case node::Kind::EXISTS: res = rewrite_exists(n); break;

    default: assert(false);
  }

  // Normalize again
  res = normalize_commutative(res);

  assert(!res.is_null());
  assert(res.type() == node.type());

  d_preproc_cache.add(node, res, preprocess::SimplifyCache::Cacher::REWRITER);
  return d_preproc_cache.get(node);
}

Node
Rewriter::eval_no_cache(const Node& node)
{
  assert(d_level == 0);

  std::vector<Node> visit{node};
  std::unordered_map<Node, Node> cache;
  do
  {
    Node cur = visit.back();

    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      if (cur.num_children())
      {
        it->second = _eval(node::utils::rebuild_node(nm(), cur, cache));
      }
      else
      {
        it->second = cur;
      }
    }
    visit.pop_back();
  } while (!visit.empty());
  assert(cache.find(node) != cache.end());
  return cache.at(node);
}

Node
Rewriter::_eval(const Node& node)
{
  // Lookup rewrite cache
  if (d_level > 0
      && d_preproc_cache.cached(node,
                                preprocess::SimplifyCache::Cacher::REWRITER))
  {
    return d_preproc_cache.get(node);
  }

  Node res;
  RewriteRuleKind kind;
  switch (node.kind())
  {
    case node::Kind::AND:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::AND_EVAL>::apply(*this, node);
      break;
    case node::Kind::DISTINCT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::DISTINCT_EVAL>::apply(*this, node);
      break;
    case node::Kind::IMPLIES:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::IMPLIES_EVAL>::apply(*this, node);
      break;
    case node::Kind::NOT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::NOT_EVAL>::apply(*this, node);
      break;
    case node::Kind::OR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::OR_EVAL>::apply(*this, node);
      break;
    case node::Kind::XOR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::XOR_EVAL>::apply(*this, node);
      break;

    case node::Kind::EQUAL:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::EQUAL_EVAL>::apply(*this, node);
      break;
    case node::Kind::ITE:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::ITE_EVAL>::apply(*this, node);
      break;

    case node::Kind::BV_AND:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_AND_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_ADD:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_ADD_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_ASHR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_ASHR_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_CONCAT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_CONCAT_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_DEC:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_DEC_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_EXTRACT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_EXTRACT_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_INC:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_INC_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_MUL:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_MUL_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_NOT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_NOT_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SHL:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SHL_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SHR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SHR_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SLT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SLT_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_UDIV:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_UDIV_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_ULT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_ULT_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_UREM:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_UREM_EVAL>::apply(*this, node);
      break;

    /* Eliminated bit-vector operators */
    case node::Kind::BV_COMP:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_COMP_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_NAND:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_NAND_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_NEG:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_NEG_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_NEGO:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_NEGO_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_NOR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_NOR_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_OR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_OR_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_REDAND:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_REDAND_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_REDOR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_REDOR_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_REDXOR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_REDXOR_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_REPEAT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_REPEAT_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_ROL:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_ROL_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_ROLI:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_ROLI_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_ROR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_ROR_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_RORI:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_RORI_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SADDO:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SADDO_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SDIV:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SDIV_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SDIVO:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SDIVO_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SGE:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SGE_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SGT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SGT_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SIGN_EXTEND:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SIGN_EXTEND_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SLE:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SLE_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SMOD:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SMOD_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SMULO:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SMULO_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SREM:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SREM_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SSUBO:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SSUBO_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_SUB:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_SUB_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_UMULO:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_UMULO_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_UADDO:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_UADDO_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_UGE:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_UGE_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_UGT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_UGT_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_ULE:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_ULE_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_USUBO:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_USUBO_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_XNOR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_XNOR_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_XOR:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_XOR_EVAL>::apply(*this, node);
      break;
    case node::Kind::BV_ZERO_EXTEND:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::BV_ZERO_EXTEND_EVAL>::apply(*this, node);
      break;

    case node::Kind::FP_ABS:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_ABS_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_ADD:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_ADD_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_DIV:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_DIV_EVAL>::apply(*this, node);
      break;
    // case node::Kind::FP_EQUAL:
    //   std::tie(res, kind) =
    //       RewriteRule<RewriteRuleKind::FP_EQUAL_EVAL>::apply(*this, node);
    //   break;
    case node::Kind::FP_FMA:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_FMA_EVAL>::apply(*this, node);
      break;
    // case node::Kind::FP_FP:
    //   std::tie(res, kind) =
    //       RewriteRule<RewriteRuleKind::FP_FP_EVAL>::apply(*this, node);
    //   break;
    // case node::Kind::FP_GEQ:
    //   std::tie(res, kind) =
    //       RewriteRule<RewriteRuleKind::FP_GEQ_EVAL>::apply(*this, node);
    //   break;
    // case node::Kind::FP_GT:
    //   std::tie(res, kind) =
    //       RewriteRule<RewriteRuleKind::FP_GT_EVAL>::apply(*this, node);
    //   break;

    case node::Kind::FP_IS_INF:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_IS_INF_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_IS_NAN:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_IS_NAN_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_IS_NEG:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_IS_NEG_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_IS_NORMAL:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_IS_NORM_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_IS_POS:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_IS_POS_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_IS_SUBNORMAL:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_IS_SUBNORM_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_IS_ZERO:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_IS_ZERO_EVAL>::apply(*this, node);
      break;

    case node::Kind::FP_LEQ:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_LEQ_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_LT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_LT_EVAL>::apply(*this, node);
      break;
    // case node::Kind::FP_MAX:
    //   std::tie(res, kind) =
    //       RewriteRule<RewriteRuleKind::FP_MAX_EVAL>::apply(*this, node);
    //   break;
    // case node::Kind::FP_MIN:
    //   std::tie(res, kind) =
    //       RewriteRule<RewriteRuleKind::FP_MIN_EVAL>::apply(*this, node);
    //   break;
    case node::Kind::FP_MUL:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_MUL_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_NEG:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_NEG_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_REM:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_REM_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_RTI:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_RTI_EVAL>::apply(*this, node);
      break;
    case node::Kind::FP_SQRT:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_SQRT_EVAL>::apply(*this, node);
      break;
    // case node::Kind::FP_SUB:
    //   std::tie(res, kind) =
    //       RewriteRule<RewriteRuleKind::FP_SUB_EVAL>::apply(*this, node);
    //   break;

    case node::Kind::FP_TO_FP_FROM_BV:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_BV_EVAL>::apply(*this,
                                                                     node);
      break;
    case node::Kind::FP_TO_FP_FROM_FP:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_FP_EVAL>::apply(*this,
                                                                     node);
      break;
    case node::Kind::FP_TO_FP_FROM_SBV:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_SBV_EVAL>::apply(*this,
                                                                      node);
      break;
    case node::Kind::FP_TO_FP_FROM_UBV:
      std::tie(res, kind) =
          RewriteRule<RewriteRuleKind::FP_TO_FP_FROM_UBV_EVAL>::apply(*this,
                                                                      node);
      break;

    // No rewrites for FP_TO_(U|S)BV conversion yet
    // case node::Kind::FP_TO_SBV:
    // case node::Kind::FP_TO_UBV:

    // There are no rewrites for constant arrays.
    // case node::Kind::CONST_ARRAY: res = n; break;

    // case node::Kind::SELECT:
    // case node::Kind::STORE:

    // case node::Kind::APPLY:
    // case node::Kind::LAMBDA:

    // case node::Kind::FORALL:
    // case node::Kind::EXISTS:

    default: assert(false);
  }
  d_stats.evals << kind;
  ++d_stats.num_evals;

  assert(!res.is_null());
  assert(res.type() == node.type());

  if (d_level > 0)
  {
    d_preproc_cache.add(node, res, preprocess::SimplifyCache::Cacher::REWRITER);
    return d_preproc_cache.get(node);
  }
  return res;
}

/* Boolean rewrites --------------------------------------------------------- */

Node
Rewriter::rewrite_and(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(AND_EVAL);
    BZLA_APPLY_RW_RULE(AND_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(AND_CONST);
    BZLA_APPLY_RW_RULE(AND_IDEM1);
    BZLA_APPLY_RW_RULE(AND_IDEM2);
    BZLA_APPLY_RW_RULE(AND_IDEM3);
    BZLA_APPLY_RW_RULE(AND_CONTRA1);
    BZLA_APPLY_RW_RULE(AND_CONTRA2);
    BZLA_APPLY_RW_RULE(AND_CONTRA3);
    BZLA_APPLY_RW_RULE(AND_RESOL1);
    BZLA_APPLY_RW_RULE(AND_SUBSUM1);
    BZLA_APPLY_RW_RULE(AND_SUBSUM2);
    BZLA_APPLY_RW_RULE(AND_NOT_AND1);
    BZLA_APPLY_RW_RULE(AND_NOT_AND2);
    BZLA_APPLY_RW_RULE(AND_BV_LT_FALSE);
    BZLA_APPLY_RW_RULE(AND_BV_LT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_distinct(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(DISTINCT_CARD);
  }
  BZLA_APPLY_RW_RULE(DISTINCT_ELIM);
DONE:
  return res;
}

Node
Rewriter::rewrite_not(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(NOT_EVAL);
    BZLA_APPLY_RW_RULE(NOT_NOT);
    BZLA_APPLY_RW_RULE(NOT_XOR);
    BZLA_APPLY_RW_RULE(NOT_EQUAL_BV1_BOOL)
  }

DONE:
  return res;
}

BZLA_ELIM_KIND_IMPL(implies, IMPLIES_ELIM)
BZLA_ELIM_KIND_IMPL(or, OR_ELIM)
BZLA_ELIM_KIND_IMPL(xor, XOR_ELIM)

/* -------------------------------------------------------------------------- */

Node
Rewriter::rewrite_eq(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(EQUAL_EVAL);
    BZLA_APPLY_RW_RULE(EQUAL_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(EQUAL_CONST);
    BZLA_APPLY_RW_RULE(EQUAL_TRUE);
    BZLA_APPLY_RW_RULE(EQUAL_ITE);
    BZLA_APPLY_RW_RULE(EQUAL_FALSE);
    BZLA_APPLY_RW_RULE(EQUAL_INV);
    BZLA_APPLY_RW_RULE(EQUAL_CONST_BV_ADD);
    BZLA_APPLY_RW_RULE(EQUAL_CONST_BV_MUL);
    BZLA_APPLY_RW_RULE(EQUAL_CONST_BV_NOT);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(EQUAL_BV_ADD);
    BZLA_APPLY_RW_RULE(EQUAL_BV_ADD_ADD);
    // this is important for the Sage benchmark TODO
    //BZLA_APPLY_RW_RULE(EQUAL_BV_CONCAT);
    BZLA_APPLY_RW_RULE(EQUAL_BV_SUB);
    BZLA_APPLY_RW_RULE(EQUAL_BV_MUL_UDIV_ZERO);
    BZLA_APPLY_RW_RULE(EQUAL_EQUAL_CONST_BV1);
    BZLA_APPLY_RW_RULE(EQUAL_ITE_SAME);
    BZLA_APPLY_RW_RULE(EQUAL_ITE_INVERTED);
    BZLA_APPLY_RW_RULE(EQUAL_ITE_DIS_BV1);
    BZLA_APPLY_RW_RULE(EQUAL_ITE_LIFT_COND);
    BZLA_APPLY_RW_RULE(EQUAL_BV_UDIV1);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_ite(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(ITE_EVAL);
    BZLA_APPLY_RW_RULE(ITE_SAME);
    BZLA_APPLY_RW_RULE(ITE_THEN_ITE1);
    BZLA_APPLY_RW_RULE(ITE_THEN_ITE2);
    BZLA_APPLY_RW_RULE(ITE_THEN_ITE3);
    BZLA_APPLY_RW_RULE(ITE_ELSE_ITE1);
    BZLA_APPLY_RW_RULE(ITE_ELSE_ITE2);
    BZLA_APPLY_RW_RULE(ITE_ELSE_ITE3);
    BZLA_APPLY_RW_RULE(ITE_BOOL);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(ITE_BV_CONCAT);
    BZLA_APPLY_RW_RULE(ITE_BV_OP);
  }

DONE:
  return res;
}

/* BV rewrites -------------------------------------------------------------- */

Node
Rewriter::rewrite_bv_add(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_ADD_EVAL);
    BZLA_APPLY_RW_RULE(BV_ADD_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_ADD_CONST);
    BZLA_APPLY_RW_RULE(BV_ADD_BV1);
    BZLA_APPLY_RW_RULE(BV_ADD_SAME);
    BZLA_APPLY_RW_RULE(BV_ADD_NOT);
    BZLA_APPLY_RW_RULE(BV_ADD_NEG);
    BZLA_APPLY_RW_RULE(BV_ADD_UREM);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_ADD_ITE1);
    BZLA_APPLY_RW_RULE(BV_ADD_ITE2);
    // BZLA_APPLY_RW_RULE(BV_ADD_SHL);
    BZLA_APPLY_RW_RULE(BV_ADD_NEG_MUL);
  }
  if (d_arithmetic)
  {
    // BZLA_APPLY_RW_RULE(NORM_BV_ADD_MUL);
    BZLA_APPLY_RW_RULE(NORM_BV_ADD_CONCAT);
    BZLA_APPLY_RW_RULE(NORM_BV_EXTRACT_ADD_MUL_REV2);
    BZLA_APPLY_RW_RULE(NORM_FACT_BV_ADD_MUL);
    BZLA_APPLY_RW_RULE(NORM_FACT_BV_ADD_SHL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_and(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_AND_EVAL);
    BZLA_APPLY_RW_RULE(BV_AND_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_AND_CONST);
    BZLA_APPLY_RW_RULE(BV_AND_IDEM1);
    BZLA_APPLY_RW_RULE(BV_AND_IDEM2);
    BZLA_APPLY_RW_RULE(BV_AND_IDEM3);
    BZLA_APPLY_RW_RULE(BV_AND_CONTRA1);
    BZLA_APPLY_RW_RULE(BV_AND_CONTRA2);
    BZLA_APPLY_RW_RULE(BV_AND_CONTRA3);
    BZLA_APPLY_RW_RULE(BV_AND_RESOL1);
    BZLA_APPLY_RW_RULE(BV_AND_SUBSUM1);
    BZLA_APPLY_RW_RULE(BV_AND_SUBSUM2);
    BZLA_APPLY_RW_RULE(BV_AND_NOT_AND1);
    BZLA_APPLY_RW_RULE(BV_AND_NOT_AND2);
    BZLA_APPLY_RW_RULE(BV_AND_CONCAT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_ashr(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_ASHR_EVAL);
    BZLA_APPLY_RW_RULE(BV_ASHR_SPECIAL_CONST);
    // BZLA_APPLY_RW_RULE(BV_ASHR_CONST);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_concat(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_CONCAT_EVAL);
    BZLA_APPLY_RW_RULE(BV_CONCAT_CONST);
    BZLA_APPLY_RW_RULE(BV_CONCAT_EXTRACT);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_CONCAT_AND);
    BZLA_APPLY_RW_RULE(NORM_BV_CONCAT_BV_NOT);
  }
  if (d_arithmetic)
  {
    BZLA_APPLY_RW_RULE(NORM_BV_MUL_POW2_REV);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_extract(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_EXTRACT_EVAL);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_FULL);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_EXTRACT);
    if (d_level == 1)
    {
      BZLA_APPLY_RW_RULE(BV_EXTRACT_CONCAT_FULL_LHS);
      BZLA_APPLY_RW_RULE(BV_EXTRACT_CONCAT_FULL_RHS);
    }
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_EXTRACT_CONCAT_LHS_RHS);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_CONCAT);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_AND);
    BZLA_APPLY_RW_RULE(BV_EXTRACT_ITE);
  }

  if (!d_arithmetic)
  {
    BZLA_APPLY_RW_RULE(BV_EXTRACT_ADD_MUL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_mul(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_MUL_EVAL);
    BZLA_APPLY_RW_RULE(BV_MUL_ZERO);
    BZLA_APPLY_RW_RULE(BV_MUL_ONE);
    BZLA_APPLY_RW_RULE(BV_MUL_ONES);
    if (!d_arithmetic)
    {
      BZLA_APPLY_RW_RULE(BV_MUL_POW2);
    }
    BZLA_APPLY_RW_RULE(BV_MUL_CONST);
    BZLA_APPLY_RW_RULE(BV_MUL_BV1);
  }
  if (d_level >= 2)
  {
    if (!d_arithmetic)
    {
      BZLA_APPLY_RW_RULE(BV_MUL_CONST_ADD);
    }
    BZLA_APPLY_RW_RULE(BV_MUL_CONST_SHL);
    BZLA_APPLY_RW_RULE(BV_MUL_NEG);
    // rewrites for Noetzli benchmarks
    BZLA_APPLY_RW_RULE(BV_MUL_ITE);
  }

  if (d_arithmetic)
  {
    BZLA_APPLY_RW_RULE(NORM_BV_EXTRACT_ADD_MUL_REV3);
    BZLA_APPLY_RW_RULE(NORM_FACT_BV_MUL_SHL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_not(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_NOT_EVAL);
    BZLA_APPLY_RW_RULE(BV_NOT_BV_NOT);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_NOT_BV_NEG);
    //BZLA_APPLY_RW_RULE(BV_NOT_BV_CONCAT);
  }
  if (d_arithmetic)
  {
    BZLA_APPLY_RW_RULE(NORM_BV_NOT_OR_SHL);
    BZLA_APPLY_RW_RULE(NORM_BV_EXTRACT_ADD_MUL_REV1);
  }
DONE:
  return res;
}

Node
Rewriter::rewrite_bv_shl(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_SHL_EVAL);
    BZLA_APPLY_RW_RULE(BV_SHL_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_SHL_CONST);
  }
  if (d_arithmetic)
  {
    BZLA_APPLY_RW_RULE(NORM_BV_SHL_NEG);
    BZLA_APPLY_RW_RULE(NORM_FACT_BV_SHL_MUL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_shr(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_SHR_EVAL);
    BZLA_APPLY_RW_RULE(BV_SHR_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_SHR_CONST);
    BZLA_APPLY_RW_RULE(BV_SHR_SAME);
    BZLA_APPLY_RW_RULE(BV_SHR_NOT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_slt(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_SLT_EVAL);
    BZLA_APPLY_RW_RULE(BV_SLT_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_SLT_SAME);
    BZLA_APPLY_RW_RULE(BV_SLT_BV1);
    BZLA_APPLY_RW_RULE(BV_SLT_ITE);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_SLT_CONCAT);
    BZLA_APPLY_RW_RULE(BV_SLT_BV_UDIV1);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_udiv(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_UDIV_EVAL);
    BZLA_APPLY_RW_RULE(BV_UDIV_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_UDIV_BV1);
    BZLA_APPLY_RW_RULE(BV_UDIV_SAME);
    BZLA_APPLY_RW_RULE(BV_UDIV_POW2);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_UDIV_ITE);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_ult(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_ULT_EVAL);
    BZLA_APPLY_RW_RULE(BV_ULT_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_ULT_SAME);
    BZLA_APPLY_RW_RULE(BV_ULT_BV1);
    BZLA_APPLY_RW_RULE(BV_ULT_ITE);
  }
  if (d_level >= 2)
  {
    BZLA_APPLY_RW_RULE(BV_ULT_CONCAT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_urem(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_UREM_EVAL);
    BZLA_APPLY_RW_RULE(BV_UREM_SPECIAL_CONST);
    BZLA_APPLY_RW_RULE(BV_UREM_SAME);
    BZLA_APPLY_RW_RULE(BV_UREM_BV1);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_bv_xor(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(BV_XOR_EVAL);
    BZLA_APPLY_RW_RULE(BV_XOR_SAME);
    BZLA_APPLY_RW_RULE(BV_XOR_SPECIAL_CONST);
  }

DONE:
  return res;
}

/* Eliminated operators */

BZLA_ELIM_KIND_IMPL(bv_dec, BV_DEC_ELIM)
BZLA_ELIM_KIND_IMPL(bv_inc, BV_INC_ELIM)
BZLA_ELIM_KIND_IMPL(bv_nand, BV_NAND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_neg, BV_NEG_ELIM)
BZLA_ELIM_KIND_IMPL(bv_nego, BV_NEGO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_nor, BV_NOR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_or, BV_OR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_redand, BV_REDAND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_redor, BV_REDOR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_redxor, BV_REDXOR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_repeat, BV_REPEAT_ELIM)
BZLA_ELIM_KIND_IMPL(bv_rol, BV_ROL_ELIM)
BZLA_ELIM_KIND_IMPL(bv_roli, BV_ROLI_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ror, BV_ROR_ELIM)
BZLA_ELIM_KIND_IMPL(bv_rori, BV_RORI_ELIM)
BZLA_ELIM_KIND_IMPL(bv_saddo, BV_SADDO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sdiv, BV_SDIV_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sdivo, BV_SDIVO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sge, BV_SGE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sgt, BV_SGT_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sign_extend, BV_SIGN_EXTEND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sle, BV_SLE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_smod, BV_SMOD_ELIM)
BZLA_ELIM_KIND_IMPL(bv_smulo, BV_SMULO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_srem, BV_SREM_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ssubo, BV_SSUBO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_sub, BV_SUB_ELIM)
BZLA_ELIM_KIND_IMPL(bv_uaddo, BV_UADDO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_uge, BV_UGE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ugt, BV_UGT_ELIM)
BZLA_ELIM_KIND_IMPL(bv_ule, BV_ULE_ELIM)
BZLA_ELIM_KIND_IMPL(bv_umulo, BV_UMULO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_usubo, BV_USUBO_ELIM)
BZLA_ELIM_KIND_IMPL(bv_xnor, BV_XNOR_ELIM)
// BZLA_ELIM_KIND_IMPL(bv_xor, BV_XOR_ELIM) do not eliminate
BZLA_ELIM_KIND_IMPL(bv_zero_extend, BV_ZERO_EXTEND_ELIM)
BZLA_ELIM_KIND_IMPL(bv_comp, BV_COMP_ELIM)

/* FP rewrites -------------------------------------------------------------- */

Node
Rewriter::rewrite_fp_abs(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_ABS_EVAL);
    BZLA_APPLY_RW_RULE(FP_ABS_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_add(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_ADD_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_div(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_DIV_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_fma(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_FMA_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_inf(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_INF_EVAL);
    BZLA_APPLY_RW_RULE(FP_IS_INF_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_nan(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_NAN_EVAL);
    BZLA_APPLY_RW_RULE(FP_IS_NAN_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_neg(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_NEG_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_normal(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_NORM_EVAL);
    BZLA_APPLY_RW_RULE(FP_IS_NORM_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_pos(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_POS_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_subnormal(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_SUBNORM_EVAL);
    BZLA_APPLY_RW_RULE(FP_IS_SUBNORM_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_is_zero(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_IS_ZERO_EVAL);
    BZLA_APPLY_RW_RULE(FP_IS_ZERO_ABS_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_leq(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_LEQ_EVAL);
    BZLA_APPLY_RW_RULE(FP_LEQ_EQ);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_lt(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_LT_EVAL);
    BZLA_APPLY_RW_RULE(FP_LT_EQ);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_max(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_MAX_EQ);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_min(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_MIN_EQ);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_mul(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_MUL_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_neg(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_NEG_EVAL);
    BZLA_APPLY_RW_RULE(FP_NEG_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_rem(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_REM_EVAL);
    BZLA_APPLY_RW_RULE(FP_REM_SAME_DIV);
    BZLA_APPLY_RW_RULE(FP_REM_ABS_NEG);
    BZLA_APPLY_RW_RULE(FP_REM_NEG);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_rti(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_RTI_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_sqrt(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_SQRT_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_bv(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_BV_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_fp(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_FP_EVAL);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_sbv(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_SBV_EVAL);
    BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_SBV_BV1_ELIM);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_fp_to_fp_from_ubv(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(FP_TO_FP_FROM_UBV_EVAL);
  }

DONE:
  return res;
}

BZLA_ELIM_KIND_IMPL(fp_equal, FP_EQUAL_ELIM)
BZLA_ELIM_KIND_IMPL(fp_fp, FP_FP_ELIM)
BZLA_ELIM_KIND_IMPL(fp_gt, FP_GT_ELIM)
BZLA_ELIM_KIND_IMPL(fp_geq, FP_GEQ_ELIM)
BZLA_ELIM_KIND_IMPL(fp_sub, FP_SUB_ELIM)

/* Array rewrites ----------------------------------------------------------- */
Node
Rewriter::rewrite_select(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(ARRAY_PROP_SELECT);
  }

DONE:
  return res;
}

Node
Rewriter::rewrite_store(const Node& node)
{
  // TODO
  return node;
}

/* Function rewrites -------------------------------------------------------- */

Node
Rewriter::rewrite_apply(const Node& node)
{
  // TODO
  return node;
}

Node
Rewriter::rewrite_lambda(const Node& node)
{
  // TODO
  return node;
}

/* Quant rewrites ----------------------------------------------------------- */

Node
Rewriter::rewrite_forall(const Node& node)
{
  // TODO
  return node;
}

BZLA_ELIM_KIND_IMPL(exists, EXISTS_ELIM)

/* Normalization ------------------------------------------------------------ */

Node
Rewriter::normalize_commutative(const Node& node)
{
  RewriteRuleKind kind;
  Node res = node;

  if (d_level >= 1)
  {
    BZLA_APPLY_RW_RULE(NORMALIZE_COMM);
  }

DONE:
  return res;
}

#define CASE(eval) \
  case RewriteRuleKind::eval: out << #eval; break

std::ostream&
operator<<(std::ostream& out, RewriteRuleKind kind)
{
  switch (kind)
  {
    CASE(AND_SPECIAL_CONST);
    CASE(AND_CONST);
    CASE(AND_IDEM1);
    CASE(AND_IDEM2);
    CASE(AND_IDEM3);
    CASE(AND_CONTRA1);
    CASE(AND_CONTRA2);
    CASE(AND_CONTRA3);
    CASE(AND_RESOL1);
    CASE(AND_SUBSUM1);
    CASE(AND_SUBSUM2);
    CASE(AND_NOT_AND1);
    CASE(AND_NOT_AND2);
    CASE(AND_BV_LT_FALSE);
    CASE(AND_BV_LT);
    CASE(EQUAL_SPECIAL_CONST);
    CASE(EQUAL_CONST);
    CASE(EQUAL_EQUAL_CONST_BV1);
    CASE(EQUAL_TRUE);
    CASE(EQUAL_ITE);
    CASE(EQUAL_FALSE);
    CASE(EQUAL_INV);
    CASE(EQUAL_CONST_BV_ADD);
    CASE(EQUAL_CONST_BV_MUL);
    CASE(EQUAL_CONST_BV_NOT);
    CASE(EQUAL_BV_ADD);
    CASE(EQUAL_BV_ADD_ADD);
    CASE(EQUAL_BV_CONCAT);
    CASE(EQUAL_BV_SUB);
    CASE(EQUAL_BV_MUL_UDIV_ZERO);
    CASE(EQUAL_ITE_SAME);
    CASE(EQUAL_ITE_INVERTED);
    CASE(EQUAL_ITE_DIS_BV1);
    CASE(EQUAL_ITE_LIFT_COND);
    CASE(EQUAL_BV_UDIV1);
    CASE(ITE_SAME);
    CASE(ITE_THEN_ITE1);
    CASE(ITE_THEN_ITE2);
    CASE(ITE_THEN_ITE3);
    CASE(ITE_ELSE_ITE1);
    CASE(ITE_ELSE_ITE2);
    CASE(ITE_ELSE_ITE3);
    CASE(ITE_BOOL);
    CASE(ITE_BV_CONCAT);
    CASE(ITE_BV_OP);
    CASE(NOT_NOT);
    CASE(NOT_XOR);
    CASE(NOT_EQUAL_BV1_BOOL);
    CASE(DISTINCT_CARD);
    CASE(DISTINCT_ELIM);
    CASE(IMPLIES_ELIM);
    CASE(OR_ELIM);
    CASE(XOR_ELIM);
    CASE(BV_ADD_SPECIAL_CONST);
    CASE(BV_ADD_CONST);
    CASE(BV_ADD_BV1);
    CASE(BV_ADD_SAME);
    CASE(BV_ADD_NOT);
    CASE(BV_ADD_NEG);
    CASE(BV_ADD_UREM);
    CASE(BV_ADD_ITE1);
    CASE(BV_ADD_ITE2);
    CASE(BV_ADD_SHL);
    CASE(BV_ADD_NEG_MUL);
    CASE(NORM_BV_ADD_MUL);
    CASE(NORM_BV_ADD_CONCAT);
    CASE(BV_AND_SPECIAL_CONST);
    CASE(BV_AND_CONST);
    CASE(BV_AND_IDEM1);
    CASE(BV_AND_IDEM2);
    CASE(BV_AND_IDEM3);
    CASE(BV_AND_CONTRA1);
    CASE(BV_AND_CONTRA2);
    CASE(BV_AND_CONTRA3);
    CASE(BV_AND_SUBSUM1);
    CASE(BV_AND_SUBSUM2);
    CASE(BV_AND_RESOL1);
    CASE(BV_AND_NOT_AND1);
    CASE(BV_AND_NOT_AND2);
    CASE(BV_AND_CONCAT);
    CASE(BV_ASHR_SPECIAL_CONST);
    CASE(BV_ASHR_CONST);
    CASE(BV_CONCAT_CONST);
    CASE(BV_CONCAT_EXTRACT);
    CASE(BV_CONCAT_AND);
    CASE(NORM_BV_CONCAT_BV_NOT);
    CASE(BV_EXTRACT_FULL);
    CASE(BV_EXTRACT_EXTRACT);
    CASE(BV_EXTRACT_CONCAT_FULL_RHS);
    CASE(BV_EXTRACT_CONCAT_FULL_LHS);
    CASE(BV_EXTRACT_CONCAT_LHS_RHS);
    CASE(BV_EXTRACT_CONCAT);
    CASE(BV_EXTRACT_AND);
    CASE(BV_EXTRACT_ITE);
    CASE(BV_EXTRACT_ADD_MUL);
    CASE(NORM_BV_EXTRACT_ADD_MUL_REV1);
    CASE(NORM_BV_EXTRACT_ADD_MUL_REV2);
    CASE(NORM_BV_EXTRACT_ADD_MUL_REV3);
    CASE(BV_MUL_CONST);
    CASE(BV_MUL_BV1);
    CASE(BV_MUL_CONST_SHL);
    CASE(BV_MUL_CONST_ADD);
    CASE(BV_MUL_ITE);
    CASE(BV_MUL_NEG);
    CASE(BV_MUL_ZERO);
    CASE(BV_MUL_ONE);
    CASE(BV_MUL_ONES);
    CASE(BV_MUL_POW2);
    CASE(NORM_BV_MUL_POW2_REV);
    CASE(NORM_FACT_BV_ADD_MUL);
    CASE(NORM_FACT_BV_ADD_SHL);
    CASE(NORM_FACT_BV_SHL_MUL);
    CASE(NORM_FACT_BV_MUL_SHL);
    CASE(BV_NOT_BV_NOT);
    CASE(BV_NOT_BV_NEG);
    CASE(BV_NOT_BV_CONCAT);
    CASE(NORM_BV_NOT_OR_SHL);
    CASE(BV_SHL_SPECIAL_CONST);
    CASE(BV_SHL_CONST);
    CASE(NORM_BV_SHL_NEG);
    CASE(BV_SHR_SPECIAL_CONST);
    CASE(BV_SHR_CONST);
    CASE(BV_SHR_SAME);
    CASE(BV_SHR_NOT);
    CASE(BV_SLT_SPECIAL_CONST);
    CASE(BV_SLT_SAME);
    CASE(BV_SLT_BV1);
    CASE(BV_SLT_ITE);
    CASE(BV_SLT_CONCAT);
    CASE(BV_SLT_BV_UDIV1);
    CASE(BV_UDIV_SPECIAL_CONST);
    CASE(BV_UDIV_BV1);
    CASE(BV_UDIV_SAME);
    CASE(BV_UDIV_POW2);
    CASE(BV_UDIV_ITE);
    CASE(BV_ULT_SPECIAL_CONST);
    CASE(BV_ULT_SAME);
    CASE(BV_ULT_BV1);
    CASE(BV_ULT_ITE);
    CASE(BV_ULT_CONCAT);
    CASE(BV_UREM_SPECIAL_CONST);
    CASE(BV_UREM_BV1);
    CASE(BV_UREM_SAME);
    CASE(BV_XOR_SAME);
    CASE(BV_XOR_SPECIAL_CONST);
    CASE(AND_EVAL);
    CASE(BV_ADD_EVAL);
    CASE(BV_AND_EVAL);
    CASE(BV_ASHR_EVAL);
    CASE(BV_COMP_EVAL);
    CASE(BV_CONCAT_EVAL);
    CASE(BV_DEC_EVAL);
    CASE(BV_EXTRACT_EVAL);
    CASE(BV_INC_EVAL);
    CASE(BV_MUL_EVAL);
    CASE(BV_NAND_EVAL);
    CASE(BV_NEGO_EVAL);
    CASE(BV_NEG_EVAL);
    CASE(BV_NOR_EVAL);
    CASE(BV_NOT_EVAL);
    CASE(BV_OR_EVAL);
    CASE(BV_REDAND_EVAL);
    CASE(BV_REDOR_EVAL);
    CASE(BV_REDXOR_EVAL);
    CASE(BV_REPEAT_EVAL);
    CASE(BV_ROLI_EVAL);
    CASE(BV_ROL_EVAL);
    CASE(BV_RORI_EVAL);
    CASE(BV_ROR_EVAL);
    CASE(BV_SADDO_EVAL);
    CASE(BV_SDIVO_EVAL);
    CASE(BV_SDIV_EVAL);
    CASE(BV_SGE_EVAL);
    CASE(BV_SGT_EVAL);
    CASE(BV_SHL_EVAL);
    CASE(BV_SHR_EVAL);
    CASE(BV_SIGN_EXTEND_EVAL);
    CASE(BV_SLE_EVAL);
    CASE(BV_SLT_EVAL);
    CASE(BV_SMOD_EVAL);
    CASE(BV_SMULO_EVAL);
    CASE(BV_SREM_EVAL);
    CASE(BV_SSUBO_EVAL);
    CASE(BV_SUB_EVAL);
    CASE(BV_UADDO_EVAL);
    CASE(BV_UDIV_EVAL);
    CASE(BV_UGE_EVAL);
    CASE(BV_UGT_EVAL);
    CASE(BV_ULE_EVAL);
    CASE(BV_ULT_EVAL);
    CASE(BV_UMULO_EVAL);
    CASE(BV_UREM_EVAL);
    CASE(BV_USUBO_EVAL);
    CASE(BV_XNOR_EVAL);
    CASE(BV_XOR_EVAL);
    CASE(BV_ZERO_EXTEND_EVAL);
    CASE(DISTINCT_EVAL);
    CASE(EQUAL_EVAL);
    CASE(IMPLIES_EVAL);
    CASE(ITE_EVAL);
    CASE(NOT_EVAL);
    CASE(OR_EVAL);
    CASE(XOR_EVAL);
    CASE(BV_DEC_ELIM);
    CASE(BV_INC_ELIM);
    CASE(BV_NAND_ELIM);
    CASE(BV_NEG_ELIM);
    CASE(BV_NEGO_ELIM);
    CASE(BV_NOR_ELIM);
    CASE(BV_OR_ELIM);
    CASE(BV_REDAND_ELIM);
    CASE(BV_REDOR_ELIM);
    CASE(BV_REDXOR_ELIM);
    CASE(BV_REPEAT_ELIM);
    CASE(BV_ROL_ELIM);
    CASE(BV_ROLI_ELIM);
    CASE(BV_ROR_ELIM);
    CASE(BV_RORI_ELIM);
    CASE(BV_SADDO_ELIM);
    CASE(BV_SDIV_ELIM);
    CASE(BV_SDIVO_ELIM);
    CASE(BV_SGE_ELIM);
    CASE(BV_SGT_ELIM);
    CASE(BV_SIGN_EXTEND_ELIM);
    CASE(BV_SLE_ELIM);
    CASE(BV_SMOD_ELIM);
    CASE(BV_SMULO_ELIM);
    CASE(BV_SREM_ELIM);
    CASE(BV_SSUBO_ELIM);
    CASE(BV_SUB_ELIM);
    CASE(BV_UADDO_ELIM);
    CASE(BV_UGE_ELIM);
    CASE(BV_UGT_ELIM);
    CASE(BV_ULE_ELIM);
    CASE(BV_UMULO_ELIM);
    CASE(BV_USUBO_ELIM);
    CASE(BV_XNOR_ELIM);
    CASE(BV_XOR_ELIM);
    CASE(BV_ZERO_EXTEND_ELIM);
    CASE(BV_COMP_ELIM);
    CASE(FP_ABS_EVAL);
    CASE(FP_ABS_ABS_NEG);
    CASE(FP_ADD_EVAL);
    CASE(FP_DIV_EVAL);
    CASE(FP_FMA_EVAL);
    CASE(FP_IS_INF_EVAL);
    CASE(FP_IS_INF_ABS_NEG);
    CASE(FP_IS_NAN_EVAL);
    CASE(FP_IS_NAN_ABS_NEG);
    CASE(FP_IS_NEG_EVAL);
    CASE(FP_IS_NORM_EVAL);
    CASE(FP_IS_NORM_ABS_NEG);
    CASE(FP_IS_POS_EVAL);
    CASE(FP_IS_SUBNORM_EVAL);
    CASE(FP_IS_SUBNORM_ABS_NEG);
    CASE(FP_IS_ZERO_EVAL);
    CASE(FP_IS_ZERO_ABS_NEG);
    CASE(FP_LEQ_EVAL);
    CASE(FP_LEQ_EQ);
    CASE(FP_LT_EVAL);
    CASE(FP_LT_EQ);
    CASE(FP_MIN_EVAL);
    CASE(FP_MIN_EQ);
    CASE(FP_MAX_EVAL);
    CASE(FP_MAX_EQ);
    CASE(FP_MUL_EVAL);
    CASE(FP_NEG_EVAL);
    CASE(FP_NEG_NEG);
    CASE(FP_REM_EVAL);
    CASE(FP_REM_SAME_DIV);
    CASE(FP_REM_ABS_NEG);
    CASE(FP_REM_NEG);
    CASE(FP_RTI_EVAL);
    CASE(FP_SQRT_EVAL);
    CASE(FP_TO_FP_FROM_BV_EVAL);
    CASE(FP_TO_FP_FROM_FP_EVAL);
    CASE(FP_TO_FP_FROM_SBV_EVAL);
    CASE(FP_TO_FP_FROM_SBV_BV1_ELIM);
    CASE(FP_TO_FP_FROM_UBV_EVAL);
    CASE(FP_EQUAL_ELIM);
    CASE(FP_FP_ELIM);
    CASE(FP_GEQ_ELIM);
    CASE(FP_GT_ELIM);
    CASE(FP_SUB_ELIM);
    CASE(ARRAY_PROP_SELECT);
    CASE(NORMALIZE_COMM);
    CASE(EXISTS_ELIM);
  }
  return out;
}

#undef CASE

Rewriter::Statistics::Statistics(util::Statistics& stats,
                                 const std::string& prefix)
    : rewrites(stats.new_stat<util::HistogramStatistic>(prefix + "rewrite")),
      evals(stats.new_stat<util::HistogramStatistic>(prefix + "eval")),
      num_rewrites(stats.new_stat<uint64_t>(prefix + "num_rewrites")),
      num_evals(stats.new_stat<uint64_t>(prefix + "num_evals"))
{
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla
