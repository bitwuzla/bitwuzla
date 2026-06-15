/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "type/card.h"

#include <cassert>

#include "solver/fp/rounding_mode.h"
#include "util/integer.h"

namespace bzla::type {

using namespace util;

namespace {

/**
 * Compute min(base^exp, bound).
 *
 * Any type cardinality is >= 2, so for `base` >= 2 the running product at least
 * doubles each iteration and thus reaches `bound` within log2(bound) steps,
 * irrespective of how large `exp` is. This bounds both the number of iterations
 * and the magnitude of the intermediate value, avoiding the unrepresentable
 * results (and exponent overflow) of a direct base^exp.
 */
Integer
pow_bounded(const Integer& base, const Integer& exp, const Integer& bound)
{
  if (exp == 0)
  {
    return Integer(1);
  }
  if (base <= 1)
  {
    return base;
  }
  Integer res(1);
  for (Integer i(0); i < exp; ++i)
  {
    res *= base;
    if (res >= bound)
    {
      return bound;
    }
  }
  return res;
}

/** Compute min(cardinality(type), bound). */
Integer
card(const Type& type, const Integer& bound)
{
  if (type.is_bool())
  {
    return Integer(2);
  }
  else if (type.is_bv())
  {
    return pow_bounded(Integer(2), Integer(type.bv_size()), bound);
  }
  else if (type.is_rm())
  {
    return Integer(static_cast<uint64_t>(RoundingMode::NUM_RM));
  }
  else if (type.is_fp())
  {
    // +zero -zero: 2
    // +inf  -inf : 2
    // nan        : 1
    // subnormals : 2 * (2^{sig_size-1)-1) = 2^{sig_size} - 2
    // normalss   : 2 * (2^{exp_size} - 2) * 2^{sig_size-1} =
    //              (2^{exp_size} - 2) * 2^{sig_size}
    //
    // card = 5 + 2^{sig_size} - 2 + (2^{exp_size} - 2) * 2^{sig_size}
    //      = 3 + 2^{sig_size} * (1 + 2^{exp_size} - 2)
    //      = 3 + 2^{sig_size} * (2^{exp_size} - 1)
    //
    Integer res =
        Integer(3)
        + pow_bounded(Integer(2), Integer(type.fp_sig_size()), bound)
              * (pow_bounded(Integer(2), Integer(type.fp_exp_size()), bound)
                 - 1);
    return res < bound ? res : bound;
  }
  else if (type.is_array())
  {
    // Cardinality of (index -> element) is |element|^|index|.
    return pow_bounded(card(type.array_element(), bound),
                       card(type.array_index(), bound),
                       bound);
  }
  else
  {
    assert(type.is_fun());

    // Cardinality of (d_1, ..., d_n -> codomain) is
    // |codomain|^(|d_1| * ... * |d_n|).
    const auto& domains = type.fun_types();
    Integer exp(1);
    for (size_t i = 0, size = domains.size() - 1; i < size; ++i)
    {
      exp *= card(domains[i], bound);
      if (exp >= bound)
      {
        exp = bound;
        break;
      }
    }
    return pow_bounded(card(domains.back(), bound), exp, bound);
  }
}

}  // namespace

bool
cardinality_lt(const Type& type, uint64_t bound)
{
  Integer b(bound);
  return card(type, b) < b;
}

}  // namespace bzla::type
