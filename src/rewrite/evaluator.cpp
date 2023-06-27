/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "rewrite/evaluator.h"

#include "node/node_manager.h"
#include "solver/fp/floating_point.h"

namespace bzla {

using namespace node;

Node
Evaluator::evaluate(Kind kind,
                    const std::vector<Node>& values,
                    const std::vector<uint64_t>& indices)
{
  NodeManager& nm = NodeManager::get();
  switch (kind)
  {
    // TODO: bool
    // TODO: bit-vectors
    case Kind::EQUAL: return nm.mk_value(values[0] == values[1]);
    case Kind::FP_IS_INF:
      return nm.mk_value(values[0].value<FloatingPoint>().fpisinf());
    case Kind::FP_IS_NAN:
      return nm.mk_value(values[0].value<FloatingPoint>().fpisnan());
    case Kind::FP_IS_NEG:
      return nm.mk_value(values[0].value<FloatingPoint>().fpisneg());
    case Kind::FP_IS_NORMAL:
      return nm.mk_value(values[0].value<FloatingPoint>().fpisnormal());
    case Kind::FP_IS_POS:
      return nm.mk_value(values[0].value<FloatingPoint>().fpispos());
    case Kind::FP_IS_SUBNORMAL:
      return nm.mk_value(values[0].value<FloatingPoint>().fpissubnormal());
    case Kind::FP_IS_ZERO:
      return nm.mk_value(values[0].value<FloatingPoint>().fpiszero());
    case Kind::FP_LEQ:
      return nm.mk_value(values[0].value<FloatingPoint>().fple(
          values[1].value<FloatingPoint>()));
    case Kind::FP_LT:
      return nm.mk_value(values[0].value<FloatingPoint>().fplt(
          values[1].value<FloatingPoint>()));
    case Kind::FP_TO_FP_FROM_FP:
      return nm.mk_value(FloatingPoint(nm.mk_fp_type(indices[0], indices[1]),
                                       values[0].value<RoundingMode>(),
                                       values[1].value<FloatingPoint>()));
    case Kind::FP_ABS:
      return nm.mk_value(values[0].value<FloatingPoint>().fpabs());
    case Kind::FP_ADD:
      return nm.mk_value(values[1].value<FloatingPoint>().fpadd(
          values[0].value<RoundingMode>(), values[2].value<FloatingPoint>()));
    case Kind::FP_DIV:
      return nm.mk_value(values[1].value<FloatingPoint>().fpdiv(
          values[0].value<RoundingMode>(), values[2].value<FloatingPoint>()));
    case Kind::FP_FMA:
      return nm.mk_value(values[1].value<FloatingPoint>().fpfma(
          values[0].value<RoundingMode>(),
          values[2].value<FloatingPoint>(),
          values[3].value<FloatingPoint>()));
    case Kind::FP_GEQ:
      return nm.mk_value(values[0].value<FloatingPoint>().fpge(
          values[1].value<FloatingPoint>()));
    case Kind::FP_GT:
      return nm.mk_value(values[0].value<FloatingPoint>().fpgt(
          values[1].value<FloatingPoint>()));
    case Kind::FP_MUL:
      return nm.mk_value(values[1].value<FloatingPoint>().fpmul(
          values[0].value<RoundingMode>(), values[2].value<FloatingPoint>()));
    case Kind::FP_NEG:
      return nm.mk_value(values[0].value<FloatingPoint>().fpneg());
    case Kind::FP_REM:
      return nm.mk_value(values[0].value<FloatingPoint>().fprem(
          values[1].value<FloatingPoint>()));
    case Kind::FP_RTI:
      return nm.mk_value(values[1].value<FloatingPoint>().fprti(
          values[0].value<RoundingMode>()));
    case Kind::FP_SQRT:
      return nm.mk_value(values[1].value<FloatingPoint>().fpsqrt(
          values[0].value<RoundingMode>()));
    case Kind::FP_TO_FP_FROM_BV:
      return nm.mk_value(FloatingPoint(nm.mk_fp_type(indices[0], indices[1]),
                                       values[0].value<BitVector>()));
    case Kind::FP_TO_FP_FROM_SBV:
      return nm.mk_value(FloatingPoint(nm.mk_fp_type(indices[0], indices[1]),
                                       values[0].value<RoundingMode>(),
                                       values[1].value<BitVector>(),
                                       true));
    case Kind::FP_TO_FP_FROM_UBV:
      return nm.mk_value(FloatingPoint(nm.mk_fp_type(indices[0], indices[1]),
                                       values[0].value<RoundingMode>(),
                                       values[1].value<BitVector>(),
                                       false));
    default: std::cerr << kind << std::endl; assert(false);
  }
  return Node();
}

}  // namespace bzla
