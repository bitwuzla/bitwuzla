#include "preprocess/pass/normalize.h"

#include <cmath>

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "util/logger.h"

namespace bzla::preprocess::pass {

using namespace bzla::node;

/* -------------------------------------------------------------------------- */

namespace {
void
_count_parents(const node_ref_vector& nodes,
               Kind kind,
               PassNormalize::ParentsMap& parents)
{
  node::unordered_node_ref_set cache;
  for (size_t i = 0, size = nodes.size(); i < size; ++i)
  {
    node::node_ref_vector visit{nodes[i]};
    parents[nodes[i]] += 1;
    do
    {
      const Node& cur     = visit.back();
      auto [it, inserted] = cache.insert(cur);
      visit.pop_back();
      if (inserted
          && (cur.kind() == kind
              || (kind == Kind::BV_ADD && cur.is_inverted()
                  && cur[0].kind() == kind)))
      {
        for (auto& child : cur)
        {
          parents[child] += 1;
          visit.push_back(child);
        }
      }
    } while (!visit.empty());
  }
}

void
push_factorized(Kind kind,
                const Node& node,
                const BitVector& occs,
                std::vector<Node>& nodes)
{
  if (kind == Kind::BV_ADD)
  {
    if (!occs.is_zero())
    {
      NodeManager& nm = NodeManager::get();
      nodes.push_back(nm.mk_node(Kind::BV_MUL, {nm.mk_value(occs), node}));
    }
  }
  else
  {
    assert(kind == Kind::BV_MUL || kind == Kind::BV_XOR
           || kind == Kind::BV_AND);
    assert(BitVector::fits_in_size(64, occs.str(), 2));
    nodes.insert(nodes.end(), occs.to_uint64(true), node);
  }
}

#ifndef NDEBUG
void
print_coefficients(PassNormalize::CoefficientsMap& coeff)
{
  for (const auto& c : coeff)
  {
    std::cout << c.first << ": " << c.second << std::endl;
  }
}
#endif
}  // namespace

/* === PassNormalize public ================================================= */

PassNormalize::PassNormalize(Env& env,
                             backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr),
      d_share_aware(d_env.options().pp_normalize_share_aware()),
      d_stats(env.statistics())
{
}

/* -------------------------------------------------------------------------- */

namespace {
bool
is_leaf(Kind kind,
        const Node& node,
        const PassNormalize::ParentsMap& parents,
        const PassNormalize::ParentsMap& parents_in_chain)
{
  if (node.kind() != kind)
  {
    return true;
  }
  auto p = parents.find(node);
  if (p == parents.end()) return false;
  auto pp = parents_in_chain.find(node);
  if (pp == parents_in_chain.end()) return false;
  return pp->second < p->second;
}
}  // namespace

void
PassNormalize::compute_coefficients(const Node& node,
                                    const ParentsMap& parents,
                                    CoefficientsMap& coeffs)
{
  Kind kind        = node.kind();
  BitVector zero   = BitVector::mk_zero(node.type().bv_size());

  node_ref_vector nodes;
  unordered_node_ref_set intermediate;
  unordered_node_ref_map<BitVector> cfs;  // all coefficients

  // Collect all traversed nodes (intermediate nodes of specified kind and
  // leafs) and initialize coefficients for each node to zero.
  node_ref_vector visit{node};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cfs.emplace(cur, zero);
    visit.pop_back();
    if (inserted)
    {
      nodes.push_back(cur);
      if (cur.kind() == kind)
      {
        if (d_share_aware)
        {
          // treat as leaf if node of given kind has parent references
          // from outside the current 'kind' chain
          assert(d_parents.find(cur) != d_parents.end());
          assert(parents.find(cur) != parents.end());
          if (is_leaf(kind, cur, d_parents, parents))
          {
            continue;
          }
        }
        intermediate.insert(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());

  // Compute leaf coefficients by pushing initial top node coefficient to leafs.
  //
  // Note: We have to ensure that parents are fully processed before we compute
  //       the coefficient for its children. Hence, we sort the nodes in
  //       ascending order and process the nodes with the higher IDs first.
  std::sort(nodes.begin(), nodes.end());
  assert(nodes.back() == node);
  cfs[node].ibvinc();  // Set initial coefficient of top node
  for (auto it = nodes.rbegin(), rend = nodes.rend(); it != rend; ++it)
  {
    const Node& cur = *it;
    auto fit        = cfs.find(cur);
    assert(fit != cfs.end());

    // If it's an intermediate node, push coefficient down to children
    if (intermediate.find(cur) != intermediate.end())
    {
      assert(cur.kind() == kind);
      for (const auto& child : cur)
      {
        assert(cfs.find(child) != cfs.end());
        cfs[child].ibvadd(fit->second);
      }
    }
    // If it's a leaf, just copy the result
    else
    {
      auto [it, inserted] = coeffs.emplace(cur, cfs[cur]);
      if (!inserted)
      {
        it->second.ibvadd(cfs[cur]);
      }
    }
  }
}

Node
PassNormalize::compute_common_coefficients(Kind kind,
                                           PassNormalize::CoefficientsMap& lhs,
                                           PassNormalize::CoefficientsMap& rhs)
{
  assert(kind == Kind::BV_ADD || kind == Kind::BV_MUL);

  // We factor out common combinations of common leafs to maximize sharing.
  // For example,
  //         lhs = {a: 1, b: 1}
  //         rhs = {a: 2, b: 2}
  // results in
  //         lhs = {a: 0, b: 0}
  //         rhs = {a: 1, b: 1}
  //         common = (a * b).
  // A more complex example,
  //         lhs = {a: 6, b: 3, c: 2, d: 1}
  //         rhs = {a: 7, b: 5, c: 3}
  // results in
  //         lhs = {a: 0, b: 0, c: 0, d: 1}
  //         rhs = {a: 1, b: 2, c: 1}
  //         common = (aaabc * (aaabc * ab))

  std::vector<std::pair<Node, BitVector>> common_coeff;
  for (auto it0 = lhs.begin(), end = lhs.end(); it0 != end; ++it0)
  {
    auto it1 = rhs.find(it0->first);
    if (it1 != rhs.end())
    {
      BitVector occs =
          it0->second.compare(it1->second) <= 0 ? it0->second : it1->second;
      if (occs.is_zero())
      {
        continue;
      }
      it0->second.ibvsub(occs);
      it1->second.ibvsub(occs);
      common_coeff.emplace_back(it0->first, occs);
    }
  }

  Node res;
  if (common_coeff.size())
  {
    NodeManager& nm = NodeManager::get();
    // combine common subterms
    if (kind == Kind::BV_ADD)
    {
      assert(!common_coeff[0].second.is_zero());
      res = common_coeff[0].second.is_one()
                ? common_coeff[0].first
                : nm.mk_node(Kind::BV_MUL,
                             {nm.mk_value(common_coeff[0].second),
                              common_coeff[0].first});
      for (size_t i = 1, n = common_coeff.size(); i < n; ++i)
      {
        res = nm.mk_node(Kind::BV_ADD,
                         {res,
                          common_coeff[i].second.is_one()
                              ? common_coeff[i].first
                              : nm.mk_node(Kind::BV_MUL,
                                           {nm.mk_value(common_coeff[i].second),
                                            common_coeff[i].first})});
      }
    }
    else
    {
      assert(kind == Kind::BV_MUL);
      while (common_coeff.size() > 1)
      {
        std::sort(common_coeff.begin(),
                  common_coeff.end(),
                  [](const auto& a, const auto& b) {
                    return a.second.compare(b.second) > 0;
                  });
        while (common_coeff.back().second.is_zero())
        {
          common_coeff.pop_back();
        }
        for (size_t i = 1, n = common_coeff.size(); i < n; ++i)
        {
          assert(common_coeff[i - 1].second.compare(common_coeff[i].second)
                 >= 0);
          const BitVector& occs = common_coeff[i].second;
          common_coeff[i].first = nm.mk_node(
              kind, {common_coeff[i - 1].first, common_coeff[i].first});
          common_coeff[i - 1].second.ibvsub(occs);
        }
      }
      assert(common_coeff.back().second.is_one());
      res = common_coeff.back().first;
    }
  }
  return res;
}

/* -------------------------------------------------------------------------- */

BitVector
PassNormalize::normalize_add(const Node& node,
                             CoefficientsMap& coeffs,
                             ParentsMap& parents)
{
  assert(node.kind() == Kind::BV_ADD);

  uint64_t bv_size = node.type().bv_size();
  BitVector bvzero = BitVector::mk_zero(bv_size);
  BitVector value  = bvzero;

  bool progress;
  node_ref_vector visit;
  do
  {
    progress = false;
    for (auto& [cur, cur_coeff] : coeffs)
    {
      // summarize values
      if (cur.is_value())
      {
        value.ibvadd(cur.value<BitVector>().bvmul(cur_coeff));
        cur_coeff = bvzero;
      }
      // normalize inverted adders
      // ~x = ~(x + 1) + 1 = - x - 1
      else if (cur.is_inverted() && cur[0].kind() == Kind::BV_ADD
               && cur_coeff != bvzero)
      {
        progress = true;
        CoefficientsMap cfs;
        BitVector coeff = coeffs.at(cur).bvneg();
        cur_coeff       = bvzero;
        compute_coefficients(cur[0], parents, cfs);
        for (auto& [c, cf] : cfs)
        {
          cf.ibvmul(coeff);
          if (c.is_value())
          {
            value.ibvadd(c.value<BitVector>().bvmul(cf));
          }
          else
          {
            auto [it, inserted] = coeffs.emplace(c, cf);
            if (!inserted)
            {
              it->second.ibvadd(cf);
            }
          }
        }
        value.ibvadd(coeff);
        break;
      }
    }
  } while (progress);

  return value;
}

/* -------------------------------------------------------------------------- */

BitVector
PassNormalize::normalize_and(const Node& node,
                             PassNormalize::CoefficientsMap& coeffs)
{
  BitVector bvzero = BitVector::mk_zero(node.type().bv_size());
  BitVector bvone  = BitVector::mk_one(node.type().bv_size());
  BitVector value  = bvone;

  for (auto& f : coeffs)
  {
    const Node& cur = f.first;
    // constant fold values
    if (cur.is_value())
    {
      value.ibvand(f.second);
      f.second = bvzero;
    }
    // normalize coefficient to 1
    else if (f.second.compare(bvone) > 0)
    {
      f.second = bvone;
    }
  }
  return value;
}

/* -------------------------------------------------------------------------- */

BitVector
PassNormalize::normalize_mul(const Node& node,
                             PassNormalize::CoefficientsMap& coeffs)
{
  assert(node.kind() == Kind::BV_MUL);

  uint64_t bv_size = node.type().bv_size();
  BitVector bvzero = BitVector::mk_zero(bv_size);
  BitVector value  = BitVector::mk_one(bv_size);

  for (auto& f : coeffs)
  {
    const Node& cur = f.first;

    // constant fold values
    if (cur.is_value())
    {
      value.ibvmul(cur.value<BitVector>().bvmul(f.second));
      f.second = bvzero;
    }
  }
  return value;
}

/* -------------------------------------------------------------------------- */

void
PassNormalize::normalize_coefficients_eq_add(
    PassNormalize::CoefficientsMap& coeffs0,
    PassNormalize::CoefficientsMap& coeffs1,
    BitVector& value)
{
  // Note: Coefficients must already be normalized in the sense that they only
  //       either appear on the left or right hand side (this function must
  //       be called with coefficients determined by
  //       normalize_coefficients_eq()).
  //       We also assume that the adders have been normalized via
  //       normalize_add(), thus both coeffs maps doe not contain values
  //       with coefficients > 0.

  // (a - b + c = -d + e) is normalized to (a + c + d = b + e)

  // ~x = ~(x + 1) + 1
  // -x = ~x + 1

  uint64_t bv_size = value.size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(bv_size));
  BitVector bvzero = BitVector::mk_zero(bv_size);

  // move negated occurrences to other side
  for (auto& f : coeffs0)
  {
    const Node& cur = f.first;
    BitVector coeff = f.second;
    assert(!cur.is_value() || coeff.is_zero());
    if (coeff.is_zero())
    {
      continue;
    }
    if (cur.is_inverted())
    {
      Node neg;
      if (cur[0].kind() == Kind::BV_ADD)
      {
        if (cur[0][0] == one)
        {
          neg = cur[0][1];
          value.ibvsub(coeff);
          f.second = bvzero;
        }
        else if (cur[0][1] == one)
        {
          neg = cur[0][0];
          value.ibvsub(coeff);
          f.second = bvzero;
        }
      }
      else
      {
        neg = cur[0];
        f.second = bvzero;
      }
      if (!neg.is_null())
      {
        if (neg.is_value())
        {
          value.ibvsub(neg.value<BitVector>().bvmul(coeff));
        }
        else
        {
          auto it = coeffs1.find(neg);
          if (it == coeffs1.end())
          {
            coeffs1.emplace(neg, coeff);
          }
          else
          {
            it->second.ibvadd(coeff);
          }
        }
        value.ibvsub(coeff);
      }
    }
  }
}

void
PassNormalize::normalize_coefficients_eq(
    const Node& node0,
    const Node& node1,
    PassNormalize::CoefficientsMap& coeffs0,
    PassNormalize::CoefficientsMap& coeffs1)
{
  assert(node0.kind() == node1.kind());
  assert(node0.kind() == Kind::BV_ADD || node0.kind() == Kind::BV_MUL);

  Kind kind = node0.kind();

  ParentsMap parents;
  if (d_share_aware)
  {
    _count_parents({node0, node1}, kind, parents);
  }

  compute_coefficients(node0, parents, coeffs0);
  compute_coefficients(node1, parents, coeffs1);

  if (kind == Kind::BV_ADD)
  {
    auto value0 = normalize_add(node0, coeffs0, parents);
    auto value1 = normalize_add(node1, coeffs1, parents);
    normalize_coefficients_eq_add(coeffs0, coeffs1, value0);
    normalize_coefficients_eq_add(coeffs1, coeffs0, value1);
    value0.ibvsub(value1);
    // add normalized value to lhs coefficients map
    if (!value0.is_zero())
    {
      Node val = NodeManager::get().mk_value(value0);
      auto it  = coeffs0.find(val);
      if (it == coeffs0.end())
      {
        coeffs0.emplace(val, BitVector::mk_one(value0.size()));
      }
      else
      {
        assert(it->second.is_zero());
        it->second.ibvinc();
      }
    }
  }
  else
  {
    assert(kind == Kind::BV_MUL);
    auto value0 = normalize_mul(node0, coeffs0);
    auto value1 = normalize_mul(node1, coeffs1);
    if (!value0.is_one())
    {
      Node val = NodeManager::get().mk_value(value0);
      auto it  = coeffs0.find(val);
      if (it == coeffs0.end())
      {
        coeffs0.emplace(val, BitVector::mk_one(value0.size()));
      }
      else
      {
        assert(it->second.is_zero());
        it->second.ibvinc();
      }
    }
    if (!value1.is_one())
    {
      Node val = NodeManager::get().mk_value(value1);
      auto it  = coeffs1.find(val);
      if (it == coeffs1.end())
      {
        coeffs1.emplace(val, BitVector::mk_one(value1.size()));
      }
      else
      {
        assert(it->second.is_zero());
        it->second.ibvinc();
      }
    }
  }

  Node common = compute_common_coefficients(kind, coeffs0, coeffs1);
  if (kind == Kind::BV_MUL && !common.is_null())
  {
    BitVector bvone = BitVector::mk_one(node0.type().bv_size());
    {
      auto [it, inserted] = coeffs0.emplace(common, bvone);
      if (!inserted)
      {
        coeffs0[common].ibvinc();
      }
    }
    {
      auto [it, inserted] = coeffs1.emplace(common, bvone);
      if (!inserted)
      {
        coeffs1[common].ibvinc();
      }
    }
  }
}

std::pair<Node, Node>
PassNormalize::_normalize_eq_mul(const CoefficientsMap& coeffs0,
                                 const CoefficientsMap& coeffs1)
{
  assert(!coeffs0.empty());
  assert(!coeffs1.empty());

  NodeManager& nm = NodeManager::get();
  std::vector<Node> lhs, rhs;
  for (const auto& f : coeffs0)
  {
    if (f.second.is_zero())
    {
      continue;
    }
    assert(BitVector::fits_in_size(64, f.second.str(), 2));
    lhs.insert(lhs.end(), f.second.to_uint64(true), f.first);
  }
    for (const auto& f : coeffs1)
    {
      if (f.second.is_zero())
      {
        continue;
      }
      assert(BitVector::fits_in_size(64, f.second.str(), 2));
      rhs.insert(rhs.end(), f.second.to_uint64(true), f.first);
    }

    if (lhs.empty())
    {
      lhs.push_back(nm.mk_value(
          BitVector::mk_one(coeffs0.begin()->first.type().bv_size())));
    }
    if (rhs.empty())
    {
      rhs.push_back(nm.mk_value(
          BitVector::mk_one(coeffs1.begin()->first.type().bv_size())));
    }

  std::sort(lhs.begin(), lhs.end());
  std::sort(rhs.begin(), rhs.end());

  Node left, right;
  size_t n = lhs.size();
  left     = lhs[n - 1];
  for (size_t i = 1; i < n; ++i)
  {
    left = nm.mk_node(Kind::BV_MUL, {lhs[n - i - 1], left});
  }
  n = rhs.size();
  right = rhs[n - 1];
  for (size_t i = 1; i < n; ++i)
  {
    right = nm.mk_node(Kind::BV_MUL, {rhs[n - i - 1], right});
  }
  return {left, right};
}

namespace {
Node
get_factorized_add(const Node& node, const BitVector& coeff)
{
  assert(!node.is_null());
  NodeManager& nm = NodeManager::get();
  assert(!coeff.is_zero());
  if (coeff.is_one())
  {
    return node;
  }
  if (coeff.is_ones())
  {
    return nm.mk_node(Kind::BV_NEG, {node});
  }
  return nm.mk_node(Kind::BV_MUL, {nm.mk_value(coeff), node});
}
}  // namespace

std::pair<Node, Node>
PassNormalize::_normalize_eq_add(PassNormalize::CoefficientsMap& coeffs0,
                                 PassNormalize::CoefficientsMap& coeffs1,
                                 uint64_t bv_size)
{
  NodeManager& nm = NodeManager::get();

  BitVector lvalue = BitVector::mk_zero(bv_size);
  BitVector rvalue = BitVector::mk_zero(bv_size);

  std::vector<Node> lhs, rhs;

  for (const auto& f : coeffs0)
  {
    const Node& cur         = f.first;
    const BitVector& coeff  = f.second;
    if (coeff.is_zero())
    {
      continue;
    }
    if (cur.is_value())
    {
      assert(coeff.is_one());
      lvalue.ibvadd(cur.value<BitVector>());
    }
    else
    {
      lhs.push_back(get_factorized_add(cur, coeff));
    }
  }
  for (const auto& f : coeffs1)
  {
    const Node& cur         = f.first;
    const BitVector& coeff  = f.second;
    if (coeff.is_zero())
    {
      continue;
    }
    assert(!cur.is_value());
    rhs.push_back(get_factorized_add(cur, coeff));
  }

  // normalize values, e.g., (a + 2 = b + 3) -> (a - 1 = b)
  if (!lvalue.is_zero())
  {
    lvalue.ibvsub(rvalue);
    if (!lvalue.is_zero())
    {
      lhs.push_back(nm.mk_value(lvalue));
    }
  }
  else if (!rvalue.is_zero())
  {
    rhs.push_back(nm.mk_value(rvalue));
  }

  std::sort(lhs.begin(), lhs.end());
  std::sort(rhs.begin(), rhs.end());

  Node left  = lhs.empty() ? nm.mk_value(BitVector::mk_zero(bv_size))
                           : node::utils::mk_nary(Kind::BV_ADD, lhs);
  Node right = rhs.empty() ? nm.mk_value(BitVector::mk_zero(bv_size))
                           : node::utils::mk_nary(Kind::BV_ADD, rhs);
  return {left, right};
}

std::pair<Node, bool>
PassNormalize::normalize_eq_add_mul(const Node& node0, const Node& node1)
{
  assert(node0.kind() == node1.kind());
  assert(node0.kind() == Kind::BV_MUL || node0.kind() == Kind::BV_ADD);

  NodeManager& nm = NodeManager::get();

  CoefficientsMap coeffs0, coeffs1;
  normalize_coefficients_eq(node0, node1, coeffs0, coeffs1);

  assert(!coeffs0.empty() && !coeffs1.empty());

  auto [left, right] =
      node0.kind() == Kind::BV_ADD
          ? _normalize_eq_add(coeffs0, coeffs1, node0.type().bv_size())
          : _normalize_eq_mul(coeffs0, coeffs1);

  if (left == right)
  {
    return {nm.mk_value(true), true};
  }

  if (left == node0 && right == node1)
  {
    return {nm.mk_node(Kind::EQUAL, {node0, node1}), false};
  }

  return {nm.mk_node(Kind::EQUAL, {left, right}), true};
}

/* -------------------------------------------------------------------------- */

namespace {

}  // namespace

std::pair<Node, Node>
PassNormalize::normalize_common(Kind kind,
                                PassNormalize::CoefficientsMap& lhs,
                                PassNormalize::CoefficientsMap& rhs)
{
  std::vector<Node> lhs_norm, rhs_norm;
  assert(!lhs.empty());
  assert(!rhs.empty());

  BitVector one = BitVector::mk_one(lhs.begin()->first.type().bv_size());

  Node common = compute_common_coefficients(kind, lhs, rhs);

  for (const auto& [n, occs] : lhs)
  {
    push_factorized(kind, n, occs, lhs_norm);
  }
  for (const auto& [n, occs] : rhs)
  {
    push_factorized(kind, n, occs, rhs_norm);
  }

  if (!common.is_null())
  {
    lhs_norm.push_back(common);
    rhs_norm.push_back(common);
  }

  assert(!lhs_norm.empty());
  assert(!rhs_norm.empty());

  std::sort(lhs_norm.begin(), lhs_norm.end());
  std::sort(rhs_norm.begin(), rhs_norm.end());

  Node left  = utils::mk_nary(kind, lhs_norm);
  Node right = utils::mk_nary(kind, rhs_norm);

  return {left, right};
}

std::pair<Node, bool>
PassNormalize::normalize_comm_assoc(Kind parent_kind,
                                    const Node& node0,
                                    const Node& node1)
{
  NodeManager& nm = NodeManager::get();

  Node top_lhs = get_top(node0);
  Node top_rhs = get_top(node1);

  Kind kind = top_lhs.kind();
  if (kind != top_rhs.kind()
      || (kind != Kind::BV_ADD && kind != Kind::BV_MUL))
    // && kind != Kind::BV_AND && kind != Kind::BV_XOR))
  {
    return {nm.mk_node(parent_kind, {node0, node1}), false};
  }

  // Note: parents could also be computed based on node0 and node1, but
  //       get_top() and rebuild_top() do not handle this case yet.
  ParentsMap parents;
  if (d_share_aware)
  {
    _count_parents({top_lhs, top_rhs}, kind, parents);
  }

  CoefficientsMap lhs, rhs;
  compute_coefficients(top_lhs, parents, lhs);
  compute_coefficients(top_rhs, parents, rhs);
  auto [left, right] = normalize_common(kind, lhs, rhs);
  auto rebuilt_left  = rebuild_top(node0, top_lhs, left);
  auto rebuilt_right = rebuild_top(node1, top_rhs, right);
  return {nm.mk_node(parent_kind, {rebuilt_left, rebuilt_right}), false};
}

Node
PassNormalize::get_top(const Node& node)
{
  Node cur = node;
  Kind k;
  while (true)
  {
    k = cur.kind();
    if (k == Kind::BV_NOT || k == Kind::BV_SHL || k == Kind::BV_SHR
        || k == Kind::BV_EXTRACT)
    {
      cur = cur[0];
    }
    else
    {
      break;
    }
  }
  return cur;
}

Node
PassNormalize::rebuild_top(const Node& node,
                           const Node& top,
                           const Node& normalized)
{
  (void) top;

  node_ref_vector visit{node};
  std::unordered_map<Node, Node> cache;

  Kind k;
  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = cache.emplace(cur, Node());

    if (inserted)
    {
      k = cur.kind();
      if (k == Kind::BV_NOT || k == Kind::BV_SHL || k == Kind::BV_SHR
          || k == Kind::BV_EXTRACT)
      {
        visit.push_back(cur[0]);
        // Other children stay the same
        for (size_t i = 1, size = cur.num_children(); i < size; ++i)
        {
          cache.emplace(cur[i], cur[i]);
        }
        continue;
      }
      else
      {
        assert(cur == top);
        it->second = normalized;
      }
    }
    else if (it->second.is_null())
    {
      it->second = utils::rebuild_node(cur, cache);
    }
    visit.pop_back();
  } while (!visit.empty());
  return cache.at(node);
}

void
PassNormalize::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);
  Log(1) << "Apply normalization";

  d_cache.clear();
  assert(d_parents.empty());
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    count_parents(assertions[i], d_parents, d_parents_cache);
  }

  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (!processed(assertion))
    {
      const Node& processed = process(assertion);
      if (assertions[i] != processed)
      {
        assertions.replace(i, processed);
        cache_assertion(processed);
        Log(2) << "Found normalization: " << assertions[i] << " -> "
               << processed;
      }
    }
  }
  d_parents.clear();
  d_parents_cache.clear();
  d_cache.clear();
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

      Kind k = cur.kind();
      if (k == Kind::EQUAL && children[0].kind() == children[1].kind()
          && (children[0].kind() == Kind::BV_ADD
              || children[0].kind() == Kind::BV_MUL))
      {
        auto [res, normalized] = normalize_eq_add_mul(children[0], children[1]);
        it->second = res;
        if (normalized) d_stats.num_normalizations += 1;
      }
      else if (k == Kind::EQUAL || k == Kind::BV_ULT || k == Kind::BV_SLT)
      {
        auto [res, normalized] =
            normalize_comm_assoc(k, children[0], children[1]);
        it->second = res;
        if (normalized) d_stats.num_normalizations += 1;
      }
#if 0
      else if ((k == Kind::BV_AND || k == Kind::BV_ADD || k == Kind::BV_MUL)
               && (cur[0].kind() == cur[1].kind() && cur[0].kind() != k))
      {
        auto [res, normalized] =
            normalize_comm_assoc(k, children[0], children[1]);
        it->second = res;
        if (normalized) d_stats.num_normalizations += 1;
      }
#endif
      else
      {
        it->second = node::utils::rebuild_node(cur, children);
      }

      // Count parents for newly constructed nodes
      count_parents(it->second, d_parents, d_parents_cache);
    }
    visit.pop_back();
  } while (!visit.empty());
  auto it = d_cache.find(node);
  assert(it != d_cache.end());
  return d_env.rewriter().rewrite(it->second);
}

/* --- PassNormalize private ------------------------------------------------ */

PassNormalize::Statistics::Statistics(util::Statistics& stats)
    : time_apply(stats.new_stat<util::TimerStatistic>(
        "preprocess::normalize::time_apply")),
      num_normalizations(
          stats.new_stat<uint64_t>("preprocess::normalize::num_normalizations"))
{
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::preprocess::pass
