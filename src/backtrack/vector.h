#ifndef BZLA_BACKTRACK_VECTOR_H_INCLUDED
#define BZLA_BACKTRACK_VECTOR_H_INCLUDED

#include <cassert>
#include <vector>

#include "backtrack/backtrackable.h"

namespace bzla::backtrack {

template <class T>
class vector : public Backtrackable
{
 public:
  vector() = default;
  vector(BacktrackManager* mgr) : Backtrackable(mgr) {}

  /* --- std::vector interface ---------------------------------------------- */

  std::size_t size() const { return d_data.size(); }

  bool empty() const { return d_data.empty(); }

  auto operator[](std::size_t pos) const { return d_data[pos]; }

  void push_back(const T& value) { d_data.push_back(value); }

  auto begin() const { return d_data.begin(); }

  auto end() const { return d_data.end(); }

  /* --- Backtrackable interface -------------------------------------------- */

  void push() override { d_control.push_back(d_data.size()); }

  void pop() override
  {
    assert(!d_control.empty());
    std::size_t pop_to = d_control.back();
    assert(pop_to <= d_data.size());
    d_control.pop_back();

    while (d_data.size() > pop_to)
    {
      d_data.pop_back();
    }
  }

 private:
  std::vector<T> d_data;
};

}  // namespace bzla::backtrack
#endif
