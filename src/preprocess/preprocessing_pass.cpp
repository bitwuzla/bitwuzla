#include "preprocess/preprocessing_pass.h"

#include "backtrack/assertion_stack.h"
#include "backtrack/unordered_map.h"
#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"

namespace bzla::preprocess {

/* --- AssertionVector public ----------------------------------------------- */

AssertionVector::AssertionVector(backtrack::AssertionView& view)
    : d_view(view),
      d_level(view.level(view.begin())),
      d_begin(view.begin()),
      d_modified(0)
{
#ifndef NDEBUG
  // Assertion should all be from one level.
  assert(view.begin(d_level) <= view.begin());
  assert(size() > 0);
  for (size_t i = d_begin; i < d_view.end(d_level); ++i)
  {
    assert(d_view.level(i) == d_level);
  }
#endif
}

void
AssertionVector::push_back(const Node& assertion)
{
  if (d_view.insert_at_level(d_level, assertion))
  {
    ++d_modified;
  }
}

size_t
AssertionVector::size() const
{
  return d_view.end(d_level) - d_begin;
}

const Node&
AssertionVector::operator[](std::size_t index) const
{
  assert(index < size());
  return d_view[d_begin + index];
}

void
AssertionVector::replace(size_t index, const Node& assertion)
{
  assert(index < size());
  size_t real_index = d_begin + index;
  if (d_view[real_index] != assertion)
  {
    ++d_modified;
    d_view.replace(real_index, assertion);
  }
}

bool
AssertionVector::initial_assertions() const
{
  return d_begin == 0;
}

/* --- AssertionVector private ---------------------------------------------- */

void
AssertionVector::reset_modified()
{
  d_modified = 0;
}

size_t
AssertionVector::num_modified() const
{
  return d_modified;
}

bool
AssertionVector::modified() const
{
  return d_modified > 0;
}

/* --- PreprocessingPass public --------------------------------------------- */

PreprocessingPass::PreprocessingPass(Env& env)
    : d_env(env), d_logger(env.logger())
{
}

/* --- PreprocessingPass protected ------------------------------------------ */

std::pair<Node, uint64_t>
PreprocessingPass::substitute(const Node& node,
                              const SubstitutionMap& substitutions,
                              SubstitutionMap& cache) const
{
  node::node_ref_vector visit{node};
  uint64_t num_substs = 0;

  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      auto its = substitutions.find(cur);
      if (its != substitutions.end())
      {
        it->second = its->second;
        num_substs += 1;
      }
      else
      {
        std::vector<Node> children;
        for (const Node& child : cur)
        {
          auto itc = cache.find(child);
          assert(itc != cache.end());
          assert(!itc->second.is_null());
          children.push_back(itc->second);
        }
        it->second = node::utils::rebuild_node(cur, children);
      }
    }
    visit.pop_back();
  } while (!visit.empty());
  auto it = cache.find(node);
  assert(it != cache.end());
  return std::make_pair(it->second, num_substs);
}

}  // namespace bzla::preprocess
