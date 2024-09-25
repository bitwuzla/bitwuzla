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
bool is_valid_bv_str(const std::string &value, uint8_t base);

/**
 * Determine if given string is a valid real value representation.
 * @param str  The value string.
 * @return True if given string is a valid string given the base.
 */
bool is_valid_real_str(const std::string &value);

}  // namespace bzla::util

#endif
