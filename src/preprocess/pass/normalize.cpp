#include "preprocess/pass/normalize.h"

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_set.h"

namespace bzla::preprocess::pass {

using namespace bzla::node;

/* --- PassNormalize public ------------------------------------------------- */

PassNormalize::PassNormalize(Env& env,
                             backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr), d_stats(env.statistics())
{
}

unordered_node_ref_map<uint64_t>
PassNormalize::compute_factors(const Node& node)
{
  Kind kind = node.kind();
  unordered_node_ref_map<uint64_t> factors;

  // compute reference count as initial factors
  node_ref_vector visit{node};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = factors.emplace(cur, 1);
    visit.pop_back();
    if (inserted)
    {
      if (cur.kind() == kind)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else
    {
      it->second += 1;
    }
  } while (!visit.empty());
  // compute factors by pushing initial factors to leafs
  visit.push_back(node);
  unordered_node_ref_set cache;
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.insert(cur);
    visit.pop_back();
    if (inserted && cur.kind() == kind)
    {
      auto fit = factors.find(cur);
      assert(fit != factors.end());
      for (auto& child : cur)
      {
        assert(factors.find(child) != factors.end());
        factors[child] = fit->second + factors[child] - 1;
        if (cur.kind() == kind)
        {
          visit.push_back(child);
        }
      }
    }
  } while (!visit.empty());
  return factors;
}

namespace {
std::unordered_map<Node, uint64_t>
_count_parents(const node_ref_vector& nodes, Kind kind)
{
  std::unordered_map<Node, uint64_t> parents;
  node::unordered_node_ref_set cache;
  for (size_t i = 0, size = nodes.size(); i < size; ++i)
  {
    node::node_ref_vector visit{nodes[i]};
    parents.emplace(nodes[i], 1);
    do
    {
      const Node& cur     = visit.back();
      auto [it, inserted] = cache.insert(cur);
      visit.pop_back();
      if (inserted && cur.kind() == kind)
      {
        for (auto& child : cur)
        {
          parents[child] += 1;
          visit.push_back(child);
        }
      }
    } while (!visit.empty());
  }
  return parents;
}
}  // namespace

std::tuple<unordered_node_ref_map<uint64_t>,
           unordered_node_ref_map<uint64_t>,
           bool>
PassNormalize::get_normalized_factors(const Node& node0,
                                      const Node& node1,
                                      bool share_aware)
{
  assert(node0.kind() == node1.kind());
  bool normalized = false;
  Kind kind       = node0.kind();
  auto factors0   = compute_factors(node0);
  auto factors1   = compute_factors(node1);
  auto parents    = _count_parents({node0, node1}, kind);
  unordered_node_ref_map<uint64_t> res0, res1;
  // normalize common factors and record entries that are not in factors1
  for (auto& f : factors0)
  {
    if (f.first.get().kind() == kind)
    {
      if (share_aware)
      {
        // do not normalize if node of given kind has parent references
        // from outside the 'kind' chain starting with node0, node1
        assert(d_parents.find(f.first) != d_parents.end());
        assert(parents.find(f.first) != parents.end());
        if (parents[f.first] < d_parents[f.first])
        {
          return {{}, {}, false};
        }
      }
      continue;
    }
    auto fit = factors1.find(f.first);
    if (fit == factors1.end())
    {
      res0.insert(f);
      continue;
    }
    if (f.second == fit->second) continue;
    if (f.second > fit->second)
    {
      assert(res0.find(f.first) == res0.end());
      res0.emplace(f.first, f.second - fit->second);
      normalized = true;
    }
    else
    {
      assert(res1.find(f.first) == res1.end());
      res1.emplace(f.first, fit->second - f.second);
      normalized = true;
    }
  }
  // check factors1 for entries that are not in factors0
  for (auto& f : factors1)
  {
    if (f.first.get().kind() == kind)
    {
      if (share_aware)
      {
        // do not normalize if node of given kind has parent references
        // from outside the 'kind' chain starting with node1
        assert(d_parents.find(f.first) != d_parents.end());
        assert(parents.find(f.first) != parents.end());
        if (parents[f.first] < d_parents[f.first])
        {
          return {{}, {}, false};
        }
      }
      continue;
    }
    auto fit = factors0.find(f.first);
    if (fit == factors0.end())
    {
      res1.insert(f);
    }
  }

  // factors on both sides cancelled out
  if (res0.empty() && res1.empty())
  {
    return {{}, {}, true};
  }

  return {res0, res1, normalized};
}

std::pair<Node, bool>
PassNormalize::normalize_eq_add_mul(const Node& node0,
                                    const Node& node1,
                                    bool share_aware)
{
  assert(node0.kind() == node1.kind());
  assert(node0.kind() == Kind::BV_MUL || node0.kind() == Kind::BV_ADD);

  NodeManager& nm = NodeManager::get();
  Kind kind       = node0.kind();
  Node dflt       = nm.mk_value(kind == Kind::BV_ADD
                              ? BitVector::mk_zero(node0.type().bv_size())
                              : BitVector::mk_one(node0.type().bv_size()));

  auto [factors0, factors1, normalized] =
      get_normalized_factors(node0, node1, share_aware);

  if (factors0.empty() && factors1.empty())
  {
    if (normalized)
    {
      return {nm.mk_value(true), true};
    }
    return {nm.mk_node(Kind::EQUAL, {node0, node1}), false};
  }

  std::vector<Node> lhs, rhs;
  if (normalized)
  {
    if (factors0.empty())
    {
      lhs.push_back(dflt);
    }
    if (factors1.empty())
    {
      rhs.push_back(dflt);
    }
    for (auto& f : factors0)
    {
      assert(f.second);
      for (size_t i = 0, n = f.second; i < n; ++i)
      {
        lhs.push_back(f.first);
      }
    }
    for (auto& f : factors1)
    {
      assert(f.second);
      for (size_t i = 0, n = f.second; i < n; ++i)
      {
        rhs.push_back(f.first);
      }
    }
  }
  assert(lhs.empty() == rhs.empty());

  if (lhs.empty())
  {
    return {nm.mk_node(Kind::EQUAL, {node0, node1}), false};
  }

  std::sort(lhs.begin(), lhs.end(), [](const Node& a, const Node& b) {
    return a.id() < b.id();
  });
  std::sort(rhs.begin(), rhs.end(), [](const Node& a, const Node& b) {
    return a.id() < b.id();
  });

  Node l, r;
  size_t n = lhs.size();
  l        = lhs[n - 1];
  for (size_t i = 1; i < n; ++i)
  {
    l = nm.mk_node(kind, {lhs[n - i - 1], l});
  }
  n = rhs.size();
  r = rhs[n - 1];
  for (size_t i = 1; i < n; ++i)
  {
    r = nm.mk_node(kind, {rhs[n - i - 1], r});
  }
  return {nm.mk_node(Kind::EQUAL, {l, r}), true};
}

void
PassNormalize::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);

  d_cache.clear();
  assert(d_parents.empty());
  d_parents = count_parents(assertions);

  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (cache_assertion(assertion))
    {
      const Node& processed = process(assertion);
      assertions.replace(i, processed);
      cache_assertion(processed);
    }
  }
  d_parents.clear();
  d_cache.clear();
}

Node
PassNormalize::process(const Node& node)
{
  bool share_aware = d_env.options().pp_normalize_share_aware();
  node_ref_vector visit{node};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = d_cache.emplace(cur, Node());
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      std::vector<Node> children;
      for (const Node& child : cur)
      {
        auto itc = d_cache.find(child);
        assert(itc != d_cache.end());
        assert(!itc->second.is_null());
        children.push_back(itc->second);
      }
      if (cur.kind() == Kind::EQUAL && children[0].kind() == children[1].kind()
          && (children[0].kind() == Kind::BV_ADD
              || children[0].kind() == Kind::BV_MUL))
      {
        auto [res, normalized] =
            normalize_eq_add_mul(children[0], children[1], share_aware);
        it->second             = res;
        if (normalized) d_stats.num_normalizations += 1;
      }
      else
      {
        it->second = node::utils::rebuild_node(cur, children);
      }
    }
    visit.pop_back();
  } while (!visit.empty());
  auto it = d_cache.find(node);
  assert(it != d_cache.end());
  return d_env.rewriter().rewrite(it->second);
}

/* --- PassEmbeddedConstraints private -------------------------------------- */

PassNormalize::Statistics::Statistics(util::Statistics& stats)
    : time_apply(stats.new_stat<util::TimerStatistic>(
        "preprocess::normalize::time_apply")),
      num_normalizations(
          stats.new_stat<uint64_t>("preprocess::normalize::num_normalizations"))
{
}

}  // namespace bzla::preprocess::pass
