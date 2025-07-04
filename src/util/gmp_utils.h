/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_UTIL_GMP_UTILS_H_INCLUDED
#define BZLA_UTIL_GMP_UTILS_H_INCLUDED

#include <gmpxx.h>

#include <cstdint>

namespace bzla::util {

// GMP wrapper functions to properly handle case where unsigned long is 32 bit
// (Windows builds).

/** 64-bit version of mpz_set_ui. */
void mpz_set_ull(mpz_t rop, uint64_t op);

/**
 * 64-bit version of mpz_get_ui.
 *
 * mpz_get_ui returns a 32 bit or 64 bit unsigned long depending on the
 * platform (Windows: 32 bit, Linux, macOS: 64).
 *
 * @return The least significant bits of op that fit into 64 bit, sign bit of op
 *         is ignored.
 */
uint64_t mpz_get_ull(const mpz_t op);

/** 64-bit version of mpz_init_set_ui. */
void mpz_init_set_ull(mpz_t rop, uint64_t op);

/** Convert uint64_t to mpz_class. */
mpz_class uint64_to_mpz_class(uint64_t op);

/** 64-bit version of mpz_init_set_si. */
void mpz_init_set_sll(mpz_t rop, int64_t op);

/**
 * Compute hash value of GMP value rop
 * @param start Optionally seed hash given value.
 * @return The hash value.
 */
size_t mpz_hash(const mpz_t op, uint64_t start = 0);

// These functions only guard their *_ui counterparts with an assertion for the
// Windows 32-bit case. In the cases where these functions are used we should
// never use values that require more than 32 bit.
void mpz_fdiv_q_2exp_ull(mpz_t q, const mpz_t n, uint64_t b);

void mpz_fdiv_r_2exp_ull(mpz_t r, const mpz_t n, uint64_t b);

void mpz_mul_2exp_ull(mpz_t rop, const mpz_t op1, uint64_t op2);

/**
 * Create mpq from decimal real string.
 * @note This function will initialize rop.
 * @param rop The resulting mpq, must not be initialized.
 * @param str The real string.
 */
void mpq_from_dec_string(mpq_t rop, std::string str);
/**
 * Create mpq from rational, represented as decimal strings for the numerator
 * and denominator.
 * @note This function will initialize rop.
 * @param rop     The resulting mpq, must not be initialized.
 * @param str_num The string representation of the numerator.
 * @param str_den The string representation of the denominator.
 */
void mpq_from_rat_string(mpq_t rop, const char* str_num, const char* str_den);
/**
 * Create mpq from rational given as unsigned integers.
 * @note This function will initialize rop.
 * @param rop The resulting mpq, must not be initialized.
 * @param n   The numerator.
 * @param d   The denominator.
 */
void mpq_from_ui(mpq_t rop, uint32_t n, uint32_t d);
}  // namespace bzla::util

#endif
