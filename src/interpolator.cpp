/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "interpolator.h"

#include <unordered_map>

#include "bv/bitvector.h"
#include "node/node.h"
#include "node/node_utils.h"
#include "preprocess/pass/variable_substitution.h"
#include "rewrite/rewriter.h"
#include "sat/sat_solver_factory.h"
#include "solver/bv/aig_bitblaster.h"
#include "util/hash.h"

namespace bzla {

using namespace node;

Interpolator::Interpolator(SolvingContext& ctx)
    : d_ctx(ctx),
      d_env(ctx.env()),
      d_logger(d_env.logger()),
      d_rewriter(ctx.env(), ctx.rewriter().level()),
      d_original_assertions(ctx.original_assertions()),
      d_pp_assertions(ctx.assertions()),
      d_compute_stats(d_env.options().interpolants_stats()),
      d_stats(d_env.statistics(), "interpolator::")
{
}

Interpolator::Rewriter::Rewriter(Env& env, uint8_t level, const std::string& id)
    : bzla::Rewriter(env, level, id)
{
}
Node
Interpolator::Rewriter::rewrite_bv_comp(const Node& node)
{
  Node res = bzla::Rewriter::rewrite_bv_comp(node);

  RewriteRuleKind kind;
  BZLA_APPLY_RW_RULE(BV_COMP_EVAL);
  BZLA_APPLY_RW_RULE(BV_COMP_BV1_CONST);
DONE:
  return res;
}

namespace {

uint64_t
gate_size(const Node& node)
{
  bv::AigBitblaster bb;
  bb.bitblast(node);
  return bb.num_aig_ands();
}

uint64_t
node_size(const Node& node)
{
  std::vector<Node> visit{node};
  std::unordered_set<Node> cache;
  uint64_t num_nodes = 0;
  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();
    if (cache.insert(cur).second)
    {
      if (cur.num_children() > 0)
      {
        ++num_nodes;
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  }
  return num_nodes;
}

Node
invert_node(NodeManager& nm, const Node& node)
{
  assert(node.type().is_bool() || node.type().is_bv());

  if (node.is_inverted())
  {
    return node[0];
  }
  if (node.type().is_bool())
  {
    return nm.mk_node(Kind::NOT, {node});
  }
  return nm.mk_node(Kind::BV_NOT, {node});
}

Node
invert_node_if(NodeManager& nm, bool cond, const Node& node)
{
  if (cond)
  {
    return invert_node(nm, node);
  }
  return node;
}

Node
ensure_bool(NodeManager& nm, const Node& n)
{
  if (n.type().is_bool())
  {
    return n;
  }
  assert(n.type().is_bv());
  assert(n.type().bv_size() == 1);
  return utils::bv1_to_bool(nm, n);
}

bool
is_bv1(const Node& n)
{
  return n.type().is_bv() && n.type().bv_size() == 1;
}

bool
is_bv1_bool(const Node& n)
{
  return n.type().is_bool() || is_bv1(n);
}

Node
bool_to_bv1(NodeManager& nm, const Node& node)
{
  return nm.mk_node(Kind::ITE,
                    {node,
                     nm.mk_value(BitVector::mk_true()),
                     nm.mk_value(BitVector::mk_false())});
}

std::unordered_map<Node, uint64_t>
compute_parents(const Node& node)
{
  std::vector<Node> visit{node};
  std::unordered_set<Node> cache;
  std::unordered_map<Node, uint64_t> parents;

  parents[node] = 0;
  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();

    if (cache.insert(cur).second)
    {
      for (const auto& c : cur)
      {
        ++parents[c];
        visit.push_back(c);
      }
    }
  }
  return parents;
}

}  // namespace

Node
Interpolator::get_interpolant(const std::unordered_set<Node>& A,
                              const std::unordered_set<Node>& A_part,
                              const Node& prev_itp)
{
  util::Timer timer(d_stats.time_get_interpolant);

  Log(1);
  Log(1) << "*** interpolant";
  Log(1);
  Log(1) << "expected assertion partitioning:";
  if (d_logger.is_log_enabled(1))
  {
    for (size_t i = 0, ia = 0, ib = 0, n = d_original_assertions.size(); i < n;
         ++i)
    {
      if (A.find(d_original_assertions[i]) != A.end())
      {
        Log(1) << "A[" << ia++ << "]: " << d_original_assertions[i];
      }
      else
      {
        Log(1) << "B[" << ib++ << "]: " << d_original_assertions[i];
      }
    }
  }
  Log(1);

  Node ipol;
  NodeManager& nm = d_env.nm();

  // Workaround until tracking is properly backtrackable
  std::unordered_set<Node> active_asserts;
  const auto& ctx_asserts = d_ctx.assertions();
  for (size_t i = 0; i < ctx_asserts.size(); ++i)
  {
    active_asserts.insert(ctx_asserts[i]);
  }

  // Partition preprocessed assertions into A and B
  std::unordered_set<Node> B, ppA, ppB, ppA_part, ppB_part;
  for (const auto& orig : d_original_assertions)
  {
    std::vector<Node> pp_asserts;
    auto _pp_asserts = d_ctx.preprocessor().preprocessed_assertions(orig);
    // Filter out inactive tracked assertions.
    for (const auto& a : _pp_asserts)
    {
      if (active_asserts.find(a) != active_asserts.end())
      {
        pp_asserts.push_back(a);
      }
    }
    if (pp_asserts.empty())
    {
      // If no active assertions were tracked, then orig is the preprocessed
      // assertion.
      assert(active_asserts.find(orig) != active_asserts.end());
      pp_asserts.push_back(orig);
    }
    if (A.find(orig) != A.end())
    {
      ppA.insert(pp_asserts.begin(), pp_asserts.end());
      if (A_part.find(orig) != A_part.end())
      {
        ppA_part.insert(pp_asserts.begin(), pp_asserts.end());
      }
    }
    else
    {
      B.insert(orig);
      ppB.insert(pp_asserts.begin(), pp_asserts.end());
    }
  }

  Log(1) << "actual assertion partitioning:";
  if (d_logger.is_log_enabled(1))
  {
    for (const auto& a : A)
    {
      Log(1) << "A: " << a;
    }
    for (const auto& a : B)
    {
      Log(1) << "B: " << a;
    }
    size_t i = 0;
    for (const auto& a : ppA)
    {
      Log(1) << "ppA[" << i++ << "]: " << a;
    }
    i = 0;
    for (const auto& a : ppB)
    {
      Log(1) << "ppB[" << i++ << "]: " << a;
    }
    i = 0;
    for (const auto& a : ppA_part)
    {
      Log(1) << "ppA_part[" << i++ << "]: " << a;
    }
    i = 0;
  }

  // Preprocessor determined unsat, so we can make a shortcut.
  if (d_ctx.sat_state_pp() == Result::UNSAT)
  {
    for (const auto& a : ppA)
    {
      if (a.is_value() && !a.value<bool>())
      {
        ipol = nm.mk_value(false);
        break;
      }
    }
    for (const auto& a : ppB)
    {
      if (a.is_value() && !a.value<bool>())
      {
        ipol = nm.mk_value(true);
        break;
      }
    }
  }

  if (ipol.is_null())
  {
    if (d_env.options().interpolants_subst())
    {
      ipol = interpolant_by_substitution(A, B, ppA_part, ppB, prev_itp);
      if (!ipol.is_null() && d_compute_stats)
      {
        d_stats.aig_size_eq_subst  = gate_size(ipol);
        d_stats.node_size_eq_subst = node_size(ipol);
      }
    }

    // Generate interpolant from bit-level proof.
    if (ipol.is_null())
    {
      {
        util::Timer timer(d_stats.time_bit_level);
        ipol = d_ctx.solver_engine().interpolant(ppA, ppB);
        ++d_stats.interpolant_bitlevel;
        if (d_compute_stats)
        {
          d_stats.aig_size_bit_level  = gate_size(ipol);
          d_stats.node_size_bit_level = node_size(ipol);
        }
      }

      if (d_env.options().interpolants_simp())
      {
        ipol = post_process_bit_level(ipol);
      }
    }
  }

  Log(1) << "I: " << ipol;
  return ipol;
}

std::vector<Node>
Interpolator::get_interpolants(
    const std::vector<std::unordered_set<Node>>& partitions)
{
  std::vector<Node> res;
  std::unordered_set<Node> A;

  d_is_sequence = partitions.size() > 1;
  Node prev_itp;
  for (size_t i = 0, size = partitions.size(); i < size; ++i)
  {
    const auto& A_part = partitions[i];
    A.insert(A_part.begin(), A_part.end());
    res.push_back(get_interpolant(A, A_part, prev_itp));
    prev_itp = res.back();
  }
  return res;
}

Node
Interpolator::interpolant_by_substitution(
    const std::unordered_set<Node>& A,
    const std::unordered_set<Node>& B,
    const std::unordered_set<Node>& ppA_part,
    const std::unordered_set<Node>& ppB,
    const Node& prev_itp)
{
  std::unordered_set<Node> shared = shared_consts(A, B);
  if (d_logger.is_log_enabled(2))
  {
    Log(2) << "shared symbols";
    for (const auto& s : shared)
    {
      Log(2) << "  " << s;
    }
  }

  std::unordered_set<Node> ppA = ppA_part;
  if (!prev_itp.is_null())
  {
    ppA.insert(prev_itp);
  }

  // Check if all A-local symbols were eliminated and return A as
  // interpolant.
  Node ipol = apply_substs(ppA, shared);
  if (!ipol.is_null())
  {
    ++d_stats.interpolant_substA;
    Log(1) << "substitution-based interpolant A";
    return d_env.rewriter().rewrite(ipol);
  }

  // Check if all B-local symbols were eliminated and return ~B as
  // interpolant.
  if (!d_is_sequence)
  {
    ipol = apply_substs(ppB, shared);
    if (!ipol.is_null())
    {
      Log(1) << "substitution-based interpolant ~B";
      ++d_stats.interpolant_substB;
      return d_env.rewriter().rewrite(d_env.nm().mk_node(Kind::NOT, {ipol}));
    }
  }

  return Node();
}

std::unordered_set<Node>
Interpolator::get_consts(const std::unordered_set<Node>& nodes)
{
  std::vector<Node> visit;
  std::unordered_set<Node> cache, consts;

  visit.insert(visit.end(), nodes.begin(), nodes.end());
  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();

    if (cache.insert(cur).second)
    {
      if (cur.is_const())
      {
        consts.insert(cur);
      }

      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  }

  return consts;
}

std::unordered_set<Node>
Interpolator::shared_consts(const std::unordered_set<Node>& A,
                            const std::unordered_set<Node>& B)
{
  std::unordered_set<Node> shared;

  auto constsA = get_consts(A);
  auto constsB = get_consts(B);

  for (const auto& c : constsA)
  {
    if (constsB.find(c) != constsB.end())
    {
      shared.insert(c);
    }
  }
  return shared;
}

Node
Interpolator::apply_substs(const std::unordered_set<Node>& assertions,
                           const std::unordered_set<Node>& shared)
{
  if (assertions.empty())
  {
    return Node();
  }

  option::Options opts;
  opts.pp_elim_bv_extracts.set(false);
  SolvingContext ctx(d_env.nm(), opts, d_env.sat_factory(), "", true);

  auto& pp = ctx.preprocessor();
  pp.set_early_terminate(false);  // Fully preprocess assertions
  pp.exclude(shared);             // Do not eliminate shared symbols

  for (const auto& a : assertions)
  {
    ctx.assert_formula(a);
  }

  ctx.preprocess();

  const auto& asserts = ctx.assertions();
  std::unordered_set<Node> subst;
  for (size_t i = 0; i < asserts.size(); ++i)
  {
    subst.insert(asserts[i]);
  }

  bool is_itp  = true;
  auto constsA = get_consts(subst);
  for (const auto& c : constsA)
  {
    if (shared.find(c) == shared.end())
    {
      is_itp = false;
      break;
    }
  }
  if (is_itp)
  {
    std::vector<Node> nodes;
    for (size_t i = 0; i < asserts.size(); ++i)
    {
      nodes.push_back(asserts[i]);
    }
    return d_env.rewriter().rewrite(
        utils::mk_nary(d_env.nm(), Kind::AND, nodes));
  }
  return Node();
}

Node
Interpolator::post_process_bit_level(const Node& ipol)
{
  util::Timer timer(d_stats.time_post_process);

  Node res = ipol;

  res = simplify(res);
  if (d_compute_stats)
  {
    d_stats.aig_size_post_simplify  = gate_size(res);
    d_stats.node_size_post_simplify = node_size(res);
  }

  Node a = res;
  res    = lower_bv1(res);

  a   = res;
  res = extract_gates(res);
  if (d_compute_stats)
  {
    d_stats.aig_size_post_extract_gates  = gate_size(res);
    d_stats.node_size_post_extract_gates = node_size(res);
  }

  a   = res;
  res = lift_bv1_bool(res);

  return res;
}

std::vector<Node>
Interpolator::flatten_and(const Node& node)
{
  assert(node.kind() == Kind::AND || node.kind() == Kind::BV_AND);
  std::vector<Node> visit{node}, leafs;
  std::unordered_set<Node> cache;
  std::unordered_set<uint64_t> contr;

  bool contradiction = false;
  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();

    if (cache.insert(cur).second)
    {
      auto [it, inserted] =
          contr.insert(cur.is_inverted() ? cur[0].id() : cur.id());
      if (!inserted)
      {
        contradiction = true;
        break;
      }

      if (cur.kind() == node.kind())
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      else
      {
        leafs.push_back(cur);
      }
    }
  }
  if (contradiction)
  {
    if (node.kind() == Kind::AND)
    {
      return {d_env.nm().mk_value(false)};
    }
    return {d_env.nm().mk_value(BitVector::mk_zero(node.type().bv_size()))};
  }
  std::sort(leafs.begin(), leafs.end());
  return leafs;
}

std::vector<Node>
Interpolator::share_aware_flatten_and(const Node& node)
{
  assert(node.kind() == Kind::AND || node.kind() == Kind::BV_AND);
  std::vector<Node> visit{node[0], node[1]}, leafs;
  std::unordered_set<Node> cache;
  std::unordered_set<uint64_t> contr;

  bool contradiction = false;
  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();

    if (cache.insert(cur).second)
    {
      auto [it, inserted] =
          contr.insert(cur.is_inverted() ? cur[0].id() : cur.id());
      if (!inserted)
      {
        contradiction = true;
        break;
      }

      auto itp     = d_parents.find(cur);
      bool flatten = itp == d_parents.end() || itp->second <= 1;
      if (cur.kind() == node.kind() && flatten)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      else
      {
        leafs.push_back(cur);
      }
    }
  }
  if (contradiction)
  {
    if (node.kind() == Kind::AND)
    {
      return {d_env.nm().mk_value(false)};
    }
    return {d_env.nm().mk_value(BitVector::mk_zero(node.type().bv_size()))};
  }
  std::sort(leafs.begin(), leafs.end());
  return leafs;
}

Node
Interpolator::lower_bv1(const Node& node)
{
  util::Timer timer(d_stats.time_lower_bv1);
  NodeManager& nm = d_env.nm();
  bzla::Rewriter& rw = d_env.rewriter();
  Node rw_node    = rw.rewrite(node);

  std::vector<Node> visit{rw_node};
  std::unordered_map<Node, Node> cache;
  while (!visit.empty())
  {
    Node cur = visit.back();
    Kind k   = cur.kind();

    auto [it, inserted] = cache.try_emplace(cur);
    if (inserted)
    {
      if (is_bv1(cur)
          || (cur.type().is_bool()
              && (k == Kind::NOT || k == Kind::AND || k == Kind::XOR
                  || (k == Kind::EQUAL && is_bv1_bool(cur[0]))
                  || (k == Kind::ITE && is_bv1_bool(cur[1])))))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      else
      {
        assert(cur.type().is_bv() || cur.type().is_bool());
        it->second = cur.type().is_bv() ? cur : bool_to_bv1(nm, cur);
      }
      continue;
    }
    else if (it->second.is_null())
    {
      std::vector<Node> children;
      for (const Node& c : cur)
      {
        children.push_back(cache.at(c));
        assert(children.back().type().is_bv());
      }

      Node res;
      if (cur.kind() == Kind::EQUAL)
      {
        assert(children[0].type().is_bv());
        assert(children[0].type().bv_size() == 1);
        res =
            nm.mk_node(Kind::BV_NOT,
                       {nm.mk_node(Kind::BV_XOR, {children[0], children[1]})});
      }
      else if (cur.kind() == Kind::ITE)
      {
        assert(children[0].type().is_bv());
        assert(children[0].type().bv_size() == 1);
        assert(children[1].type().is_bv());
        assert(children[1].type().bv_size() == 1);
        if (children[1].is_value() && children[2].is_value())
        {
          if (children[1].value<BitVector>().is_one()
              && children[2].value<BitVector>().is_zero())
          {
            res = children[0];
          }
          else if (children[1].value<BitVector>().is_zero()
                   && children[2].value<BitVector>().is_one())
          {
            res = nm.mk_node(Kind::BV_NOT, {children[0]});
          }
        }
        if (res.is_null())
        {
          children[0] = nm.mk_node(
              Kind::EQUAL, {children[0], nm.mk_value(BitVector::mk_true())});
          res = nm.mk_node(cur.kind(), children);
        }
      }
      else
      {
        if (children.empty())
        {
          res = cur;
        }
        else
        {
          Kind k = cur.kind();
          if (k == Kind::NOT)
          {
            k = Kind::BV_NOT;
          }
          else if (k == Kind::AND)
          {
            k = Kind::BV_AND;
          }
          else if (k == Kind::XOR)
          {
            k = Kind::BV_XOR;
          }
          res = nm.mk_node(k, children, cur.indices());
        }
      }
      it->second = rw.rewrite(res);
    }
    visit.pop_back();
  }

  return cache.at(rw_node);
}

std::vector<Node>
Interpolator::and_distrib(Rewriter& rw, const std::vector<Node>& args)
{
  NodeManager& nm = d_env.nm();

  Kind kind;
  Node _true;
  if (args[0].type().is_bool())
  {
    kind  = Kind::AND;
    _true = nm.mk_value(true);
  }
  else
  {
    kind  = Kind::BV_AND;
    _true = nm.mk_value(BitVector::mk_true());
  }

  std::vector<Node> candidates, _args;
  std::unordered_map<Node, uint64_t> occs;
  for (const auto& n : args)
  {
    if (n.is_inverted() && n[0].kind() == kind)
    {
      candidates.push_back(n);
      ++occs[n[0][0]];
      ++occs[n[0][1]];
    }
    else
    {
      _args.push_back(n);
    }
  }

  for (size_t i = 0, size = candidates.size(); i < size; ++i)
  {
    Node a = candidates[i];
    if (a.is_value())
    {
      continue;
    }
    assert(a.is_inverted());
    assert(a[0].kind() == kind);
    const Node& n1 = a[0];
    bool merged    = false;
    for (size_t i1 = 0; i1 < 2; ++i1)
    {
      Node p = n1[i1];
      // Nothing to merge
      if (occs[p] <= 1)
      {
        continue;
      }
      std::vector<Node> terms{invert_node(nm, n1[1 - i1])};
      for (size_t k = i + 1; k < size; ++k)
      {
        Node b = candidates[k];
        if (b.is_value())
        {
          continue;
        }
        assert(b.is_inverted());
        assert(b[0].kind() == kind);
        Node n2 = b[0];

        if (p == n2[0])
        {
          terms.push_back(invert_node(nm, n2[1]));
          candidates[k] = _true;
        }
        else if (p == n2[1])
        {
          terms.push_back(invert_node(nm, n2[0]));
          candidates[k] = _true;
        }
      }
      // (not (and x t1))
      // (not (and x ...))
      // (not (and x tn))
      //
      // into
      //
      // (not (and x (not (and (not t1) ... (not tn)))
      if (terms.size() > 1)
      {
        d_stats.num_merged_and += terms.size();
        Node m = mk_node(
            rw, kind, {p, invert_node(nm, utils::mk_nary(nm, kind, terms))});
        _args.push_back(rw.rewrite(invert_node(nm, m)));
        candidates[i] = _true;
        merged        = true;
        break;
      }
    }
    if (!merged)
    {
      _args.push_back(a);
    }
  }
  return _args;
}

std::vector<Node>
Interpolator::extract_xor(const std::vector<Node>& args)
{
  NodeManager& nm = d_env.nm();

  std::vector<Node> _args;
  std::unordered_map<std::pair<uint64_t, uint64_t>, size_t> xor_candidates;
  std::unordered_map<std::pair<uint64_t, uint64_t>, size_t> xnor_candidates;
  for (size_t i = 0, size = args.size(); i < size; ++i)
  {
    const Node cur = args[i];
    if (cur.kind() == Kind::BV_NOT && cur[0].kind() == Kind::BV_AND)
    {
      const Node& a  = cur[0][0];
      const Node& b  = cur[0][1];
      const Node& ra = a.is_inverted() ? a[0] : a;
      const Node& rb = b.is_inverted() ? b[0] : b;

      std::pair<uint64_t, uint64_t> k{ra.id(), rb.id()};
      if (k.first > k.second)
      {
        std::swap(k.first, k.second);
      }

      bool is_xnor     = a.is_inverted() != b.is_inverted();
      auto& candidates = is_xnor ? xnor_candidates : xor_candidates;

      auto [it, inserted] = candidates.emplace(k, _args.size());
      if (!inserted)
      {
        size_t pos = it->second;
        assert(_args[pos].is_inverted());
        assert(_args[pos][0].kind() == Kind::BV_AND);
        if (a.is_inverted() != _args[pos][0][0].is_inverted()
            || a.is_inverted() != _args[pos][0][1].is_inverted())
        {
          _args[pos] = invert_node_if(
              nm, is_xnor, mk_node(d_rewriter, Kind::BV_XOR, {ra, rb}));
          candidates.erase(it);
          if (is_xnor)
          {
            ++d_stats.num_extracted_xnor;
          }
          else
          {
            ++d_stats.num_extracted_xor;
          }
          continue;
        }
      }
    }
    _args.push_back(cur);
  }
  return _args;
}

Node
Interpolator::mk_bv_and(Rewriter& rw, const std::vector<Node>& nodes)
{
  NodeManager& nm = d_env.nm();

  std::vector<Node> args;
  std::vector<Node> to_flatten;
  for (const Node& n : nodes)
  {
    assert(n.type().is_bv());
    assert(n.type().bv_size() == 1);
    to_flatten.push_back(rw.rewrite(n));
  }

  // Flatten AND
  {
    std::unordered_set<Node> cache;
    while (!to_flatten.empty())
    {
      Node cur = to_flatten.back();
      to_flatten.pop_back();

      auto [it, inserted] = cache.insert(cur);
      if (inserted)
      {
        assert(!cur.is_inverted() || !cur[0].is_inverted());
        // Found contradicting children
        if (cache.find(invert_node(nm, cur)) != cache.end())
        {
          return nm.mk_value(BitVector::mk_false());
        }

        auto itp     = d_parents.find(cur);
        bool flatten = itp == d_parents.end() || itp->second <= 1;
        if (cur.kind() == Kind::BV_AND && flatten)
        {
          to_flatten.insert(to_flatten.end(), cur.begin(), cur.end());
        }
        else
        {
          args.push_back(cur);
        }
      }
    }
  }

  // Extract XOR/XNOR gates
  args = extract_xor(args);

  // Extract bvcomp operators
  args = extract_cmp(args);

  // Filter true, duplicates and find contradiction.
  {
    std::unordered_set<Node> cache;
    std::vector<Node> _args;
    std::vector<Node> comps;
    for (const auto& a : args)
    {
      assert(a == rw.rewrite(a));
      if (a.is_value() && a.value<BitVector>().is_true())
      {
        continue;
      }
      // Contradiction found
      if (cache.find(invert_node(nm, a)) != cache.end())
      {
        return nm.mk_value(BitVector::mk_false());
      }
      if (a.kind() == Kind::BV_COMP)
      {
        comps.push_back(a);
      }
      // Filter duplicates
      auto [it, inserted] = cache.insert(a);
      if (inserted)
      {
        _args.push_back(a);
      }
    }

    // Find contradiction w.r.t. equalities
    for (const auto& c : comps)
    {
      if (cache.find(c[0]) != cache.end()
          && cache.find(invert_node(nm, c[1])) != cache.end())
      {
        return nm.mk_value(BitVector::mk_false());
      }
      else if (cache.find(c[1]) != cache.end()
               && cache.find(invert_node(nm, c[0])) != cache.end())
      {
        return nm.mk_value(BitVector::mk_false());
      }
    }

    args = std::move(_args);
  }

  if (args.empty())
  {
    return nm.mk_value(BitVector::mk_true());
  }

  std::sort(args.begin(), args.end());
  Node res = utils::mk_nary(nm, Kind::BV_AND, args);
  return rw.rewrite(res);
}

Node
Interpolator::extract_gates(const Node& node)
{
  util::Timer timer(d_stats.time_extract_gates);
  Node rw_node = d_rewriter.rewrite(node);

  d_parents = compute_parents(rw_node);

  std::vector<Node> visit{rw_node};
  std::unordered_map<Node, Node> cache;
  std::unordered_map<Node, std::vector<Node>> flattened;
  while (!visit.empty())
  {
    Node cur = visit.back();
    assert(cur == d_rewriter.rewrite(cur));
    auto [it, inserted] = cache.try_emplace(cur);
    if (inserted)
    {
      if (cur.kind() == Kind::BV_AND && cur.type().bv_size() == 1)
      {
        auto args = share_aware_flatten_and(cur);
        args      = and_distrib(d_rewriter, args);
        visit.insert(visit.end(), args.begin(), args.end());
        flattened.emplace(cur, std::move(args));
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.is_null())
    {
      Node res;
      if (cur.kind() == Kind::BV_AND && cur.type().bv_size() == 1)
      {
        std::vector<Node> children;
        for (const auto& leaf : flattened.at(cur))
        {
          children.push_back(cache.at(leaf));
          assert(!children.back().is_null());
        }
        res = mk_bv_and(d_rewriter, children);
      }
      else
      {
        std::vector<Node> children;
        for (const Node& c : cur)
        {
          children.push_back(cache.at(c));
        }

        if (children.empty())
        {
          assert(cur.is_const() || cur.is_value());
          res = cur;
        }
        else
        {
          res = mk_node(d_rewriter, cur.kind(), children, cur.indices());
          assert(res == d_rewriter.rewrite(res));
          if (res.kind() == Kind::BV_AND && res.type().bv_size() == 1)
          {
            res = mk_bv_and(d_rewriter, flatten_and(res));
          }
        }
      }
      assert(res == d_rewriter.rewrite(res));
      it->second = res;

      auto itp       = d_parents.find(cur);
      d_parents[res] = itp == d_parents.end() ? 1 : itp->second;
    }
    visit.pop_back();
  }

  return d_env.rewriter().rewrite(cache.at(rw_node));
}

Node
Interpolator::lift_bv1_bool(const Node& node)
{
  util::Timer timer(d_stats.time_bv1_bool);

  NodeManager& nm = d_env.nm();
  std::vector<Node> visit{node};
  std::unordered_map<Node, Node> cache;
  while (!visit.empty())
  {
    Node cur            = visit.back();
    auto [it, inserted] = cache.try_emplace(cur);
    if (inserted)
    {
      Kind k           = cur.kind();
      const Type& type = cur.type();
      if (type.is_bv() && type.bv_size() == 1
          && (k == Kind::BV_NOT || k == Kind::BV_AND || k == Kind::BV_XOR
              || k == Kind::BV_COMP))
      {
        if (k == Kind::BV_COMP && cur[0].type().bv_size() > 1)
        {
          it->second = nm.mk_node(Kind::EQUAL, {cur[0], cur[1]});
        }
        else
        {
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
      }
      else
      {
        it->second = cur;
      }
      continue;
    }
    else if (it->second.is_null())
    {
      std::vector<Node> children;
      for (const Node& c : cur)
      {
        children.push_back(ensure_bool(nm, cache.at(c)));
      }

      if (cur.kind() == Kind::BV_NOT)
      {
        Node res = nm.mk_node(Kind::NOT, children);
        // Maybe add as rewrite?
        if (res[0].kind() == Kind::EQUAL)
        {
          if (res[0][0].type().is_bv() && res[0][0].type().bv_size() == 1)
          {
            if (res[0][0].is_value())
            {
              Node flipped = nm.mk_value(res[0][0].value<BitVector>().bvnot());
              res          = nm.mk_node(Kind::EQUAL, {flipped, res[0][1]});
            }
            else if (res[0][1].is_value())
            {
              Node flipped = nm.mk_value(res[0][1].value<BitVector>().bvnot());
              res          = nm.mk_node(Kind::EQUAL, {res[0][0], flipped});
            }
          }
        }
        it->second = res;
      }
      else if (cur.kind() == Kind::BV_AND)
      {
        it->second = nm.mk_node(Kind::AND, children);
      }
      else if (cur.kind() == Kind::BV_COMP)
      {
        it->second = nm.mk_node(Kind::EQUAL, {children[0], children[1]});
      }
      else
      {
        assert(cur.kind() == Kind::BV_XOR);
        it->second = nm.mk_node(Kind::XOR, children);
      }
    }
    visit.pop_back();
  }
  Node res = cache.at(node);
  if (res.type().is_bv())
  {
    res = utils::bv1_to_bool(nm, res);
  }
  return d_env.rewriter().rewrite(res);
}

std::vector<Node>
Interpolator::extract_cmp(const std::vector<Node>& nodes)
{
  std::unordered_map<Node, std::vector<std::pair<Node, Node>>> eqs;
  // Merge equalities over extracts
  std::vector<Node> args;
  std::unordered_map<Node, uint64_t> occs;
  for (const auto& n : nodes)
  {
    if (n.is_inverted() && n[0].kind() == Kind::BV_XOR)
    {
      if (n[0][0].kind() == Kind::BV_EXTRACT)
      {
        ++occs[n[0][0][0]];
      }
      else if (n[0][1].kind() == Kind::BV_EXTRACT)
      {
        ++occs[n[0][1][0]];
      }
    }
    else if (n.kind() == Kind::BV_COMP)
    {
      if (n[0].kind() == Kind::BV_EXTRACT)
      {
        ++occs[n[0][0]];
      }
      else if (n[1].kind() == Kind::BV_EXTRACT)
      {
        ++occs[n[1][0]];
      }
    }
    else if (n.kind() == Kind::BV_EXTRACT)
    {
      ++occs[n[0]];
      continue;
    }
    else if (n.is_inverted() && n[0].kind() == Kind::BV_EXTRACT)
    {
      ++occs[n[0][0]];
      continue;
    }
  }

  NodeManager& nm = d_env.nm();

  Node bv1 = nm.mk_value(BitVector::mk_true());
  Node bv0 = nm.mk_value(BitVector::mk_false());
  for (const auto& n : nodes)
  {
    assert(n == d_rewriter.rewrite(n));
    if (n.is_inverted() && n[0].kind() == Kind::BV_XOR)
    {
      bool first = true;
      // If both are extracts, pick the one with the most occurrences to
      // maximize merging.
      if (n[0][0].kind() == Kind::BV_EXTRACT
          && n[0][1].kind() == Kind::BV_EXTRACT)
      {
        first = occs[n[0][0][0]] > occs[n[0][1][0]];
      }
      if (first && n[0][0].kind() == Kind::BV_EXTRACT)
      {
        const Node& ext = n[0][0];
        const Node& t   = n[0][1];
        const Node& x   = n[0][0][0];
        eqs[x].emplace_back(ext, t);
        continue;
      }
      else if (n[0][1].kind() == Kind::BV_EXTRACT)
      {
        const Node& ext = n[0][1];
        const Node& t   = n[0][0];
        const Node& x   = n[0][1][0];
        eqs[x].emplace_back(ext, t);
        continue;
      }
    }
    else if (n.kind() == Kind::BV_COMP)
    {
      bool first = true;
      // If both are extracts, pick the one with the most occurrences to
      // maximize merging.
      if (n[0].kind() == Kind::BV_EXTRACT && n[1].kind() == Kind::BV_EXTRACT)
      {
        first = occs[n[0][0]] > occs[n[1][0]];
      }
      if (first && n[0].kind() == Kind::BV_EXTRACT)
      {
        const Node& ext = n[0];
        const Node& t   = n[1];
        const Node& x   = n[0][0];
        eqs[x].emplace_back(ext, t);
        continue;
      }
      else if (n[1].kind() == Kind::BV_EXTRACT)
      {
        const Node& ext = n[1];
        const Node& t   = n[0];
        const Node& x   = n[1][0];
        eqs[x].emplace_back(ext, t);
        continue;
      }
    }
    else if (n.kind() == Kind::BV_EXTRACT)
    {
      eqs[n[0]].emplace_back(n, bv1);
      continue;
    }
    else if (n.is_inverted() && n[0].kind() == Kind::BV_EXTRACT)
    {
      eqs[n[0][0]].emplace_back(n[0], bv0);
      continue;
    }
    args.push_back(d_rewriter.rewrite(n));
  }

  for (auto& [c, exts] : eqs)
  {
    std::sort(exts.begin(), exts.end(), [](const auto& e1, const auto& e2) {
      return e1.first.index(0) < e2.first.index(0);
    });

    bool merged             = false;
    std::pair<Node, Node> p = exts[0];
    for (size_t i = 1, size = exts.size(); i < size; ++i)
    {
      const auto& cur_p = exts[i];

      // Rewrites applied to concats below may also yield something other than
      // extracts.
      if (p.first.kind() == Kind::BV_EXTRACT
          && cur_p.first.kind() == Kind::BV_EXTRACT
          && p.first.index(0) + 1 == cur_p.first.index(1))
      {
        p.first = mk_node(d_rewriter, Kind::BV_CONCAT, {cur_p.first, p.first});
        p.second =
            mk_node(d_rewriter, Kind::BV_CONCAT, {cur_p.second, p.second});
        ++d_stats.num_merged_eq;
        if (!merged)
        {
          ++d_stats.num_merged_eq;
        }
        merged = true;
      }
      else
      {
        args.push_back(mk_node(d_rewriter, Kind::BV_COMP, {p.first, p.second}));
        p = cur_p;
      }
    }
    args.push_back(mk_node(d_rewriter, Kind::BV_COMP, {p.first, p.second}));
  }

  return args;
}

Node
Interpolator::mk_and_eq(Rewriter& rw, const std::vector<Node>& nodes)
{
  std::unordered_map<Node, std::vector<std::pair<Node, Node>>> eqs;

  NodeManager& nm = d_env.nm();

  // Merge equalities over extracts
  std::vector<Node> args;
  {
    std::unordered_map<Node, uint64_t> occs;
    for (const auto& n : nodes)
    {
      if (n.kind() == Kind::EQUAL)
      {
        if (n[0].kind() == Kind::BV_EXTRACT)
        {
          ++occs[n[0][0]];
        }
        else if (n[1].kind() == Kind::BV_EXTRACT)
        {
          ++occs[n[1][0]];
        }
      }
    }

    for (const auto& n : nodes)
    {
      // assert(n.kind() != Kind::AND);
      assert(n == rw.rewrite(n));
      if (n.kind() == Kind::EQUAL)
      {
        bool first = true;
        // If both are extracts, pick the one with the most occurrences to
        // maximize merging.
        if (n[0].kind() == Kind::BV_EXTRACT && n[1].kind() == Kind::BV_EXTRACT)
        {
          first = occs[n[0][0]] > occs[n[1][0]];
        }
        if (first && n[0].kind() == Kind::BV_EXTRACT)
        {
          const Node& ext = n[0];
          const Node& t   = n[1];
          const Node& x   = n[0][0];
          eqs[x].emplace_back(ext, t);
          continue;
        }
        else if (n[1].kind() == Kind::BV_EXTRACT)
        {
          const Node& ext = n[1];
          const Node& t   = n[0];
          const Node& x   = n[1][0];
          eqs[x].emplace_back(ext, t);
          continue;
        }
      }
      args.push_back(rw.rewrite(n));
    }

    for (auto& [c, exts] : eqs)
    {
      std::sort(exts.begin(), exts.end(), [](const auto& e1, const auto& e2) {
        return e1.first.index(0) < e2.first.index(0);
      });

      bool merged             = false;
      std::pair<Node, Node> p = exts[0];
      for (size_t i = 1, size = exts.size(); i < size; ++i)
      {
        const auto& cur_p = exts[i];

        // Rewrites applied to concats below may also yield something other than
        // extracs.
        if (p.first.kind() == Kind::BV_EXTRACT
            && cur_p.first.kind() == Kind::BV_EXTRACT
            && p.first.index(0) + 1 == cur_p.first.index(1))
        {
          p.first  = mk_node(rw, Kind::BV_CONCAT, {cur_p.first, p.first});
          p.second = mk_node(rw, Kind::BV_CONCAT, {cur_p.second, p.second});
          ++d_stats.num_merged_eq;
          if (!merged)
          {
            ++d_stats.num_merged_eq;
          }
          merged = true;
        }
        else
        {
          args.push_back(mk_node(rw, Kind::EQUAL, {p.first, p.second}));
          p = cur_p;
        }
      }
      args.push_back(mk_node(rw, Kind::EQUAL, {p.first, p.second}));
    }
  }

  args = and_distrib(rw, args);

  if (args.size() == 1)
  {
    return args[0];
  }
  std::sort(args.begin(), args.end());
  return rw.rewrite(utils::mk_nary(nm, Kind::AND, args));
}

std::vector<Node>
Interpolator::apply_substs_local(const std::vector<Node>& nodes)
{
  assert(!nodes.empty());

  option::Options opts;
  Env vs_env(d_env.nm(), d_env.sat_factory(), opts);
  backtrack::BacktrackManager mgr;
  preprocess::pass::PassVariableSubstitution vs(vs_env, &mgr);

  backtrack::AssertionStack as;
  for (const auto& a : nodes)
  {
    as.push_back(a);
  }

  preprocess::AssertionVector av(as.view());
  vs.apply(av);

  const auto& substs = vs.substitutions();
  if (!substs.empty())
  {
    std::vector<Node> args;
    for (size_t i = 0; i < av.size(); ++i)
    {
      args.push_back(av[i]);
    }
    // Keep substitution assertions
    for (const auto& [v, t] : substs)
    {
      args.push_back(vs.substitution_assertion(v));
    }
    return args;
  }
  return nodes;
}

Node
Interpolator::simplify(const Node& node)
{
  util::Timer timer(d_stats.time_simplify);
  option::Options opts;
  opts.pp_elim_bv_extracts.set(false);
  SolvingContext ctx(d_env.nm(), opts, d_env.sat_factory(), "", true);

  ctx.assert_formula(node.is_inverted() ? node[0] : node);
  ctx.preprocess();

  const auto& assertions = ctx.assertions();
  std::vector<Node> _asserts;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    if (assertions[i].is_value() && assertions[i].value<bool>())
    {
      continue;
    }
    _asserts.push_back(assertions[i]);
  }

  NodeManager& nm    = d_env.nm();
  auto& pp           = ctx.preprocessor();
  const auto& substs = pp.substitutions();
  for (const auto& [v, t] : substs)
  {
    _asserts.push_back(nm.mk_node(Kind::EQUAL, {v, pp.process(t)}));
  }

  Node res;
  if (_asserts.empty())
  {
    res = d_env.nm().mk_value(true);
  }
  else
  {
    res = utils::mk_nary(d_env.nm(), Kind::AND, _asserts);
  }

  if (node.is_inverted())
  {
    res = d_env.nm().mk_node(Kind::NOT, {res});
  }

  return d_env.rewriter().rewrite(res);
}

Node
Interpolator::mk_node(Rewriter& rw,
                      node::Kind k,
                      const std::vector<Node>& children,
                      const std::vector<uint64_t>& indices)
{
  return rw.rewrite(d_env.nm().mk_node(k, children, indices));
}

Interpolator::Statistics::Statistics(util::Statistics& stats,
                                     const std::string& prefix)
    : time_get_interpolant(stats.new_stat<util::TimerStatistic>(
          prefix + "time_get_interpolant")),
      interpolant_substA(
          stats.new_stat<uint64_t>(prefix + "interpolant_substA")),
      interpolant_substB(
          stats.new_stat<uint64_t>(prefix + "interpolant_substB")),
      interpolant_bitlevel(
          stats.new_stat<uint64_t>(prefix + "interpolant_bitlevel")),
      time_bit_level(
          stats.new_stat<util::TimerStatistic>(prefix + "time_bit_level")),
      time_post_process(
          stats.new_stat<util::TimerStatistic>(prefix + "post::time_total")),
      time_simplify(
          stats.new_stat<util::TimerStatistic>(prefix + "post::time_simplify")),
      time_lower_bv1(stats.new_stat<util::TimerStatistic>(
          prefix + "post::time_lower_bv1")),
      time_extract_gates(stats.new_stat<util::TimerStatistic>(
          prefix + "post::time_extract_gates")),
      time_bv1_bool(
          stats.new_stat<util::TimerStatistic>(prefix + "post::time_bv1_bool")),
      num_merged_eq(stats.new_stat<uint64_t>(prefix + "post::merged_eq")),
      num_extracted_xor(
          stats.new_stat<uint64_t>(prefix + "post::extracted_xor")),
      num_extracted_xnor(
          stats.new_stat<uint64_t>(prefix + "post::extracted_xnor")),
      num_merged_and(stats.new_stat<uint64_t>(prefix + "post::merged_and")),
      aig_size_bit_level(
          stats.new_stat<uint64_t>(prefix + "size::aig::0_bit_level")),
      aig_size_eq_subst(
          stats.new_stat<uint64_t>(prefix + "size::aig::eq_subst")),
      aig_size_post_extract_gates(
          stats.new_stat<uint64_t>(prefix + "size::aig::3_post_extract_gates")),
      aig_size_post_simplify(
          stats.new_stat<uint64_t>(prefix + "size::aig::1_post_simplify")),
      node_size_bit_level(
          stats.new_stat<uint64_t>(prefix + "size::node::0_bit_level")),
      node_size_eq_subst(
          stats.new_stat<uint64_t>(prefix + "size::node::eq_subst")),
      node_size_post_extract_gates(stats.new_stat<uint64_t>(
          prefix + "size::node::3_post_extract_gates")),
      node_size_post_simplify(
          stats.new_stat<uint64_t>(prefix + "size::node::1_post_simplify"))
{
}
}  // namespace bzla
