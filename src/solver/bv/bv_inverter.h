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

  Node ic(Kind kind, const Node& x, const Node& s, const Node& t);

 private:
  Node ic_bv_ult(const Node& x, const Node& t);
  Node ic_bv_ugt(const Node& x, const Node& t);

  /** The associated node manager. */
  NodeManager& d_nm;
};

}  // namespace bv
}  // namespace bzla
#endif
