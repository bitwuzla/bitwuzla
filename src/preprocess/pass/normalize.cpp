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
    : PreprocessingPass(env), d_cache(backtrack_mgr), d_stats(env.statistics())
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

std::pair<Node, bool>
PassNormalize::normalize_eq_mul(const Node& node0, const Node& node1)
{
  assert(node0.kind() == Kind::BV_MUL);
  assert(node1.kind() == Kind::BV_MUL);

  bool normalized = false;
  auto factors0   = compute_factors(node0);
  auto factors1   = compute_factors(node1);
  unordered_node_ref_map<uint64_t> res0, res1;
  // normalize common factors and record entries that are not in factors1
  for (auto& f : factors0)
  {
    if (f.first.get().kind() == Kind::BV_MUL)
    {
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
    if (f.first.get().kind() == Kind::BV_MUL)
    {
      continue;
    }
    auto fit = factors0.find(f.first);
    if (fit == factors0.end())
    {
      res1.insert(f);
    }
  }
  NodeManager& nm = NodeManager::get();
  if (res0.empty() && res1.empty())
  {
    return {nm.mk_value(true), true};
  }
  std::vector<Node> vlhs, vrhs;
  if (res0.empty())
  {
    vlhs.push_back(nm.mk_value(BitVector::mk_one(node0.type().bv_size())));
  }
  if (res1.empty())
  {
    vrhs.push_back(nm.mk_value(BitVector::mk_one(node1.type().bv_size())));
  }
  if (normalized)
  {
    for (auto& f : res0)
    {
      assert(f.second);
      for (size_t i = 0, n = f.second; i < n; ++i)
      {
        vlhs.push_back(f.first);
      }
    }
    for (auto& f : res1)
    {
      assert(f.second);
      for (size_t i = 0, n = f.second; i < n; ++i)
      {
        vrhs.push_back(f.first);
      }
    }
  }
  assert(vlhs.empty() == vrhs.empty());

  Node lhs, rhs;
  if (vlhs.empty())
  {
    lhs = node0;
    rhs = node1;
  }
  else
  {
    std::sort(vlhs.begin(), vlhs.end(), [](const Node& a, const Node& b) {
      return a.id() < b.id();
    });
    std::sort(vrhs.begin(), vrhs.end(), [](const Node& a, const Node& b) {
      return a.id() < b.id();
    });
    size_t n = vlhs.size();
    lhs      = vlhs[n - 1];
    for (size_t i = 1; i < n; ++i)
    {
      lhs = nm.mk_node(Kind::BV_MUL, {vlhs[n - i - 1], lhs});
    }
    n   = vrhs.size();
    rhs = vrhs[n - 1];
    for (size_t i = 1; i < n; ++i)
    {
      rhs = nm.mk_node(Kind::BV_MUL, {vrhs[n - i - 1], rhs});
    }
  }
  return {nm.mk_node(Kind::EQUAL, {lhs, rhs}), normalized};
}

void
PassNormalize::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);

  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    assertions.replace(i, process(assertions[i]));
  }
}

Node
PassNormalize::process(const Node& node)
{
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
      if (cur.kind() == Kind::EQUAL && children[0].kind() == Kind::BV_MUL
          && children[1].kind() == Kind::BV_MUL)
      {
        auto [res, normalized] = normalize_eq_mul(children[0], children[1]);
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
