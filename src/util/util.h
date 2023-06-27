/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_UTIL_UTIL_H_INCLUDED
#define BZLA_UTIL_UTIL_H_INCLUDED

#include <cassert>
#include <cstdint>
#include <string>

namespace bzla::util {

/**
 * Determine if given string is a valid bit-vector value representation
 * with respect to the given base.
 * @param value The value string.
 * @param base  The base the value is given in; 2 for binary, 10 for decimal
 *              and 16 for hexadecimal.
 * @return True if given string is a valid string given the base.
 */
bool
is_valid_bv_str(const std::string &value, uint8_t base)
{
  if (base == 2)
  {
    for (const auto &c : value)
    {
      if (c != '0' && c != '1') return false;
    }
    return true;
  }
  if (base == 10)
  {
    for (size_t i = value[0] == '-' ? 1 : 0, n = value.size(); i < n; ++i)
    {
      if (value[i] < '0' || value[i] > '9') return false;
    }
    return true;
  }
  assert(base == 16);
  for (const auto &c : value)
  {
    if ((c < '0' || c > '9') && (c < 'a' || c > 'f') && (c < 'A' || c > 'F'))
    {
      return false;
    }
  }
  return true;
}

/**
 * Determine if given string is a valid real value representation.
 * @param str  The value string.
 * @return True if given string is a valid string given the base.
 */
bool
is_valid_real_str(const std::string &value)
{
  bool found_dec_point = false;
  for (size_t i = 0, size = value.size(); i < size; ++i)
  {
    if (!isdigit(value[i]))
    {
      if (i == 0 && value[i] == '-')
      {
        continue;
      }
      else if (value[i] == '.' && !found_dec_point)
      {
        found_dec_point = true;
        continue;
      }
      return false;
    }
  }
  return true;
}

}  // namespace bzla::util

#endif
