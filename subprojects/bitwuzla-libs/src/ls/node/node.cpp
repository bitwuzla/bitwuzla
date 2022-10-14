#include "ls/node/node.h"

#include <cassert>
#include <iostream>
#include <sstream>

#include "bv/bitvector.h"
#include "rng/rng.h"

namespace bzla::ls {

template <class VALUE>
Node<VALUE>::Node(RNG* rng, const VALUE& assignment, bool is_value)
    : d_rng(rng),
      d_assignment(assignment),
      d_arity(0),
      d_is_value(is_value),
      d_all_value(d_is_value)
{
}

template <class VALUE>
Node<VALUE>::Node(RNG* rng,
                  const VALUE& assignment,
                  Node<VALUE>* child0,
                  bool is_value)
    : d_children({child0}),
      d_rng(rng),
      d_assignment(assignment),
      d_arity(1),
      d_is_value(is_value),
      d_all_value(child0->is_value())
{
}

template <class VALUE>
Node<VALUE>::Node(RNG* rng,
                  const VALUE& assignment,
                  Node<VALUE>* child0,
                  Node<VALUE>* child1,
                  bool is_value)
    : d_children({child0, child1}),
      d_rng(rng),
      d_assignment(assignment),
      d_arity(2),
      d_is_value(is_value),
      d_all_value(child0->is_value() && child1->is_value())
{
}

template <class VALUE>
Node<VALUE>::Node(RNG* rng,
                  const VALUE& assignment,
                  Node<VALUE>* child0,
                  Node<VALUE>* child1,
                  Node<VALUE>* child2,
                  bool is_value)
    : d_children({child0, child1, child2}),
      d_rng(rng),
      d_assignment(assignment),
      d_arity(3),
      d_is_value(is_value),
      d_all_value(child0->is_value() && child1->is_value()
                  && child2->is_value())
{
}

template <class VALUE>
Node<VALUE>::~Node()
{
}

template <class VALUE>
bool
Node<VALUE>::is_essential(const VALUE& t, uint64_t pos_x)
{
  return !is_invertible(t, 1 - pos_x, true);
}

template <class VALUE>
bool
Node<VALUE>::is_invertible(const VALUE& t,
                           uint64_t pos_x,
                           bool is_essential_check)
{
  (void) t;
  (void) pos_x;
  (void) is_essential_check;
  return true;
}

template <class VALUE>
bool
Node<VALUE>::is_consistent(const VALUE& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
  return true;
}

template <class VALUE>
const VALUE&
Node<VALUE>::inverse_value(const VALUE& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
  return *d_inverse;
}

template <class VALUE>
const VALUE&
Node<VALUE>::consistent_value(const VALUE& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
  return *d_consistent;
}

template <class VALUE>
uint64_t
Node<VALUE>::select_path(const VALUE& t)
{
  assert(!all_value());

  std::vector<uint64_t> inputs;

  /* select non-const operand if only one is non-const */
  uint64_t pos_x = select_path_non_const(inputs);

  /* select essential input if any and path selection based on essential
   * inputs is enabled. */
  if (pos_x == static_cast<uint64_t>(-1) && s_path_sel_essential
      && d_rng->pick_with_prob(s_prob_pick_ess_input))
  {
    /* determine essential inputs */
    std::vector<uint64_t> ess_inputs;
    for (uint64_t i : inputs)
    {
      assert(!d_children[i]->is_value());
      if (is_essential(t, i))
      {
        ess_inputs.push_back(i);
      }
    }
    if (!ess_inputs.empty())
    {
      pos_x = d_rng->pick_from_set<std::vector<uint64_t>, uint64_t>(ess_inputs);
    }
  }

  /* select random input if operation has no essential inputs or if random path
   * selection enabled */
  if (pos_x == static_cast<uint64_t>(-1))
  {
    pos_x = d_rng->pick_from_set<std::vector<uint64_t>, uint64_t>(inputs);
  }

  assert(pos_x != static_cast<uint64_t>(-1));
  return pos_x;
}

template <class VALUE>
Node<VALUE>*
Node<VALUE>::operator[](uint64_t pos) const
{
  assert(pos < arity());
  assert(d_children.size() == arity());
  return d_children[pos];
}

template <class VALUE>
uint64_t
Node<VALUE>::select_path_non_const(std::vector<uint64_t>& res_inputs) const
{
  assert(res_inputs.empty());
  for (uint32_t i = 0; i < d_arity; ++i)
  {
    if (d_children[i]->is_value()) continue;
    res_inputs.push_back(i);
  }
  if (res_inputs.size() > 1) return static_cast<uint64_t>(-1);
  return res_inputs[0];
}

template <class VALUE>
std::vector<std::string>
Node<VALUE>::log() const
{
  std::vector<std::string> res;
  for (uint32_t i = 0, n = arity(); i < n; ++i)
  {
    std::stringstream ss;
    ss << "      |- node[" << i << "]: " << d_children[i] << std::endl;
    res.push_back(ss.str());
  }
  return res;
}
std::ostream&
operator<<(std::ostream& out, const Node<BitVector>& node)
{
  out << node.to_string();
  return out;
}

template class Node<BitVector>;

}  // namespace bzla::ls
