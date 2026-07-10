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

/*
 * Locale-independent, ASCII-only replacements for the corresponding <cctype>
 * functions. The <cctype> functions have undefined behavior when passed a char
 * whose value is not representable as unsigned char (e.g. a byte with the high
 * bit set on platforms where char is signed); these variants operate directly
 * on char and are safe for arbitrary input.
 */

/** @return True if `c` is a decimal digit ('0'-'9'). */
bool is_digit(char c);

/** @return True if `c` is a hexadecimal digit ('0'-'9', 'a'-'f', 'A'-'F'). */
bool is_xdigit(char c);

/**
 * @return True if `c` is an ASCII whitespace character (space, horizontal or
 *         vertical tab, form feed, carriage return, or newline).
 */
bool is_space(char c);

/**
 * @return The lower-case variant of `c` if `c` is an upper-case ASCII letter,
 *         `c` unchanged otherwise.
 */
char to_lower(char c);

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
