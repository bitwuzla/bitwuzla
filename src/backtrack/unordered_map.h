#ifndef BZLA_BACKTRACK_UNORDERED_MAP_H_INCLUDED
#define BZLA_BACKTRACK_UNORDERED_MAP_H_INCLUDED

#include <cassert>
#include <unordered_map>
#include <vector>

#include "backtrack/backtrackable.h"

namespace bzla::backtrack {

template <class K, class V>
class unordered_map : public Backtrackable
{
 public:
  unordered_map() = default;
  unordered_map(BacktrackManager* mgr) : Backtrackable(mgr) {}

  /* --- std::unordered_map interface --------------------------------------- */

  std::size_t size() const { return d_data.size(); }

  bool empty() const { return d_data.empty(); }

  auto find(const K& key) { return d_data.find(key); }

  template <class... Args>
  auto emplace(Args&&... args)
  {
    auto [it, inserted] = d_data.emplace(std::forward<Args>(args)...);
    if (inserted)
    {
      d_keys.emplace_back(it->first);
    }
    return std::make_pair(it, inserted);
  }

  auto begin() const { return d_data.begin(); }

  auto end() const { return d_data.end(); }

  /* --- Backtrackable interface -------------------------------------------- */

  void push() override { d_control.push_back(d_keys.size()); }

  void pop() override
  {
    assert(!d_control.empty());
    std::size_t pop_to = d_control.back();
    assert(pop_to <= d_keys.size());
    d_control.pop_back();

    while (d_keys.size() > pop_to)
    {
      d_data.erase(d_keys.back());
      d_keys.pop_back();
    }
  }

 private:
  std::unordered_map<K, V> d_data;
  std::vector<std::reference_wrapper<const K>> d_keys;
};

}  // namespace bzla::backtrack
#endif
