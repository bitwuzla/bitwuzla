#include "bitblast/aig/aig_cnf.h"

#include <functional>

namespace bzla::bb {

void
AigCnfEncoder::encode(const AigNode& node, bool top_level)
{
  if (top_level)
  {
    std::unordered_set<int64_t> cache;
    std::vector<std::reference_wrapper<const AigNode>> visit;
    std::vector<std::reference_wrapper<const AigNode>> children;
    if (node.is_and())
    {
      visit.push_back(node[1]);
      visit.push_back(node[0]);
    }
    else
    {
      visit.push_back(node);
    }

    do
    {
      const AigNode& cur = visit.back();
      visit.pop_back();

      auto [it, inserted] = cache.insert(cur.get_id());
      if (!inserted)
      {
        continue;
      }

      if (cur.is_and() && !cur.is_negated())
      {
        visit.push_back(cur[1]);
        visit.push_back(cur[0]);
      }
      else
      {
        children.push_back(cur);
        _encode(cur);
      }
    } while (!visit.empty());
    assert(!children.empty());

    // Top-level or
    if (node.is_and() && node.is_negated())
    {
      for (const AigNode& child : children)
      {
        d_sat_solver.add(-child.get_id());
      }
      d_sat_solver.add(0);
    }
    // Top-level and
    else
    {
      for (const AigNode& child : children)
      {
        d_sat_solver.add_clause({child.get_id()});
      }
    }
  }
  else
  {
    _encode(node);
  }
}

int32_t
AigCnfEncoder::value(const AigNode& aig)
{
  if (aig.is_true())
  {
    return 1;
  }
  else if (aig.is_false())
  {
    return -1;
  }

  int32_t val = -1;
  if (is_encoded(aig))
  {
    val = d_sat_solver.value(std::abs(aig.get_id())) ? 1 : -1;
  }

  return aig.is_negated() ? -val : val;
}

void
AigCnfEncoder::_encode(const AigNode& aig)
{
  std::vector<const AigNode*> visit;
  std::unordered_set<const AigNode*> cache;
  visit.push_back(&aig);
  do
  {
    auto cur = visit.back();
    resize(*cur);

    if (is_encoded(*cur))
    {
      visit.pop_back();
      continue;
    }

    if (cur->is_true() || cur->is_false() || cur->is_const())
    {
      visit.pop_back();
      set_encoded(*cur);
      if (cur->is_true() || cur->is_false())
      {
        d_sat_solver.add_clause({std::abs(cur->get_id())});
      }
    }
    else
    {
      assert(cur->is_and());

      auto [it, inserted] = cache.insert(cur);

      if (inserted)
      {
        visit.push_back(&(*cur)[0]);
        visit.push_back(&(*cur)[1]);
      }
      else
      {
        visit.pop_back();
        set_encoded(*cur);

        // TODO: and optimization: collect all children and encode one big and
        // TODO: xor optimization: use native xor encoding
        // TODO: ite optimization: use native ite encoding

        // Encode binary AND
        //
        // x <-> a /\ b --> (~x \/ a) /\ (~x \/ b) /\ (x \/ ~a \/ ~b)

        auto x = std::abs(cur->get_id());
        auto a = (*cur)[0].get_id();
        auto b = (*cur)[1].get_id();

        d_sat_solver.add_clause({-x, a});
        d_sat_solver.add_clause({-x, b});
        d_sat_solver.add_clause({x, -a, -b});
      }
    }
  } while (!visit.empty());
}

void
AigCnfEncoder::resize(const AigNode& aig)
{
  size_t pos = std::abs(aig.get_id()) - 1;
  if (pos < d_aig_encoded.size())
  {
    return;
  }
  d_aig_encoded.resize(pos + 1, false);
}

bool
AigCnfEncoder::is_encoded(const AigNode& aig) const
{
  size_t pos = std::abs(aig.get_id()) - 1;
  if (pos < d_aig_encoded.size())
  {
    return d_aig_encoded[pos];
  }
  return false;
}

void
AigCnfEncoder::set_encoded(const AigNode& aig)
{
  size_t pos = std::abs(aig.get_id()) - 1;
  assert(pos < d_aig_encoded.size());
  d_aig_encoded[pos] = true;
}
}  // namespace bzla::bb
