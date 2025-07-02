/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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

/** Compute hash value of GMP value rop. */
size_t mpz_hash(const mpz_t op);

// These functions only guard their *_ui counterparts with an assertion for the
// Windows 32-bit case. In the cases where these functions are used we should
// never use values that require more than 32 bit.
void mpz_fdiv_q_2exp_ull(mpz_t q, const mpz_t n, uint64_t b);

void mpz_fdiv_r_2exp_ull(mpz_t r, const mpz_t n, uint64_t b);

void mpz_mul_2exp_ull(mpz_t rop, const mpz_t op1, uint64_t op2);

}  // namespace bzla::util
