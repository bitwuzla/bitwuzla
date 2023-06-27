/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "rewrite/rewrite_utils.h"

#include "bv/bitvector.h"
#include "node/node_kind.h"
#include "node/node_manager.h"

namespace bzla::rewrite::utils {

bool
is_inverted_of(const Node& a, const Node& b)
{
  return (a.is_inverted() && a[0] == b) || (b.is_inverted() && b[0] == a);
}

bool
is_always_disequal(const Node& a, const Node& b)
{
  // rewrite EQUAL_EVAL is expected to be enabled
  assert(!a.is_value() || !b.is_value());

  // a and be of function sort
  if (a.type().is_fun())
  {
    return false;
  }

  NodeManager& nm = NodeManager::get();
  uint64_t idx0, idx1;
  Node nodes[2] = {a, b};
  for (const auto& p :
       std::vector<std::pair<uint64_t, uint64_t>>{{0, 1}, {1, 0}})
  {
    std::tie(idx0, idx1) = p;

    // match: (= (bvnot a) a) or (= a (bvnot a))
    if (nodes[idx0].is_inverted() && nodes[idx0][0] == nodes[idx1])
    {
      return true;
    }

    bool inverted0    = nodes[idx0].is_inverted();
    const Node& node0 = inverted0 ? nodes[idx0][0] : nodes[idx0];
    if (node0.kind() == node::Kind::BV_ADD)
    {
      bool is_val00 = node0[0].is_value();
      bool is_val01 = node0[1].is_value();
      // match (= (not (bvadd a c)) (bvnot a)) with c a non-zero value
      // match: (= (bvadd a c) a) with c a non-zero value
      if (is_val00 && !node0[0].value<BitVector>().is_zero())
      {
        if ((inverted0 && nm.invert_node(node0[1]) == nodes[idx1])
            || (!inverted0 && node0[1] == nodes[idx1]))
        {
          return true;
        }
      }
      else if (is_val01 && !node0[1].value<BitVector>().is_zero())
      {
        if ((inverted0 && nm.invert_node(node0[0]) == nodes[idx1])
            || (!inverted0 && node0[0] == nodes[idx1]))
        {
          return true;
        }
      }
      bool inverted1    = nodes[idx1].is_inverted();
      const Node& node1 = inverted1 ? nodes[idx1][0] : nodes[idx1];
      if (node1.kind() == node::Kind::BV_ADD)
      {
        bool is_val10 = node1[0].is_value();
        bool is_val11 = node1[1].is_value();
        // match: (= (bvadd a c0) (bvadd a c1))
        //        (= (bvnot (bvadd a c0)) (bvnot (bvadd a c1)))
        //        with c0,c1 values and c0 != c1
        if (inverted0 == inverted1 && (is_val00 || is_val01)
            && (is_val10 || is_val11))
        {
          const Node& val0 = is_val00 ? node0[0] : node0[1];
          const Node& val1 = is_val10 ? node1[0] : node1[1];
          const Node& n0   = is_val00 ? node0[1] : node0[0];
          const Node& n1   = is_val10 ? node1[1] : node1[0];
          if (n0 == n1 && val0 != val1)
          {
            return true;
          }
        }
      }
    }
  }
  return false;
}
}  // namespace bzla::rewrite::utils
