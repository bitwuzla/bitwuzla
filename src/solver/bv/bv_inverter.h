/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_BV_BV_INVERTER_H_INCLUDED
#define BZLA_SOLVER_BV_BV_INVERTER_H_INCLUDED

#include "env.h"
#include "node/node.h"
#include "node/node_kind.h"

namespace bzla {

using namespace node;

namespace bv {

class BvInverter
{
 public:
  BvInverter(Env& env);
  ~BvInverter();

  Node ic(Kind predicate, Kind kind, const std::vector<Node>& nodes);

 private:
  Node ic_equal(Kind kind, const std::vector<Node>& nodes);
  Node ic_distinct(Kind kind, const std::vector<Node>& nodes);

  Node ic_bv_slt(Kind kind, const std::vector<Node>& nodes);
  Node ic_bv_sle(Kind kind, const std::vector<Node>& nodes);
  Node ic_bv_sgt(Kind kind, const std::vector<Node>& nodes);
  Node ic_bv_sge(Kind kind, const std::vector<Node>& nodes);

  Node ic_bv_ult(Kind kind, const std::vector<Node>& nodes);
  Node ic_bv_ule(Kind kind, const std::vector<Node>& nodes);
  Node ic_bv_ugt(Kind kind, const std::vector<Node>& nodes);
  Node ic_bv_uge(Kind kind, const std::vector<Node>& nodes);

  Node ic_eq_mul(const Node& s, const Node& t);
  Node ic_dist_mul(const Node& s, const Node& t);
  Node ic_bv_slt_mul(const Node& s, const Node& t);
  Node ic_bv_sle_mul(const Node& s, const Node& t);
  Node ic_bv_sgt_mul(const Node& s, const Node& t);
  Node ic_bv_sge_mul(const Node& s, const Node& t);
  Node ic_bv_ult_mul(const Node& s, const Node& t);
  Node ic_bv_ule_mul(const Node& s, const Node& t);
  Node ic_bv_ugt_mul(const Node& s, const Node& t);
  Node ic_bv_uge_mul(const Node& s, const Node& t);

  /** The associated node manager. */
  NodeManager& d_nm;
};

}  // namespace bv
}  // namespace bzla
#endif
