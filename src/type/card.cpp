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

namespace bzla::type {

using namespace util;

Integer
compute_cardinality(const Type& type)
{
  if (type.is_bool())
  {
    return Integer(2);
  }
  else if (type.is_bv())
  {
    return Integer(2).ipow(type.bv_size());
  }
  else if (type.is_rm())
  {
    return Integer(static_cast<uint64_t>(RoundingMode::NUM_RM));
  }
  else if (type.is_fp())
  {
    return Integer(5)
           + Integer(2).ipow(type.fp_sig_size())
                 * (Integer(2).ipow(type.fp_exp_size()) - 1);
  }
  else if (type.is_array())
  {
    return compute_cardinality(type.array_index())
           * compute_cardinality(type.array_element());
  }
  else
  {
    assert(type.is_fun());
    Integer res(1);
    for (const auto& t : type.fun_types())
    {
      res *= compute_cardinality(t);
    }
    return res;
  }
}

}  // namespace bzla::type
