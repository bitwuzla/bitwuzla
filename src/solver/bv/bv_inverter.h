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

  Node ic(Kind predicate,
          Kind kind,
          const std::vector<Node>& nodes,
          size_t idx);

 private:
  Node ic_bv_and(Kind predicate, const std::vector<Node>& nodes, size_t idx);
  Node ic_bv_ashr(Kind predicate, const std::vector<Node>& nodes, size_t idx);
  Node ic_bv_concat(Kind predicate, const std::vector<Node>& nodes, size_t idx);
  Node ic_bv_mul(Kind predicate, const std::vector<Node>& nodes, size_t idx);
  Node ic_bv_shl(Kind predicate, const std::vector<Node>& nodes, size_t idx);
  Node ic_bv_shr(Kind predicate, const std::vector<Node>& nodes, size_t idx);
  Node ic_bv_udiv(Kind predicate, const std::vector<Node>& nodes, size_t idx);
  Node ic_bv_urem(Kind predicate, const std::vector<Node>& nodes, size_t idx);

  /** The associated node manager. */
  NodeManager& d_nm;
};

}  // namespace bv
}  // namespace bzla
#endif
