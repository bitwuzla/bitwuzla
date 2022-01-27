/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAUTIL_H_INCLUDED
#define BZLAUTIL_H_INCLUDED

#include <ctype.h>
#include <stdbool.h>
#include <stdint.h>

#include "bzlatypes.h"
#include "utils/bzlamem.h"

/*------------------------------------------------------------------------*/

#define BZLA_MAX_UTIL(x, y) ((x) > (y) ? (x) : (y))

#define BZLA_MIN_UTIL(x, y) ((x) < (y) ? (x) : (y))

#define BZLA_AVERAGE_UTIL(a, b) ((b) ? ((double) (a)) / ((double) (b)) : 0.0)

#define BZLA_SWAP(TYPE, A, B)           \
  do                                    \
  {                                     \
    TYPE BZLA_SWAP_TMP = (A);           \
    (A)                = (B);           \
    (B)                = BZLA_SWAP_TMP; \
  } while (0)

/*------------------------------------------------------------------------*/

bool bzla_util_is_power_of_2(uint32_t x);

bool bzla_util_is_valid_real(const char *value);

uint32_t bzla_util_log_2(uint32_t x);

int32_t bzla_util_pow_2(int32_t x);

int32_t bzla_util_next_power_of_2(int32_t x);

/*------------------------------------------------------------------------*/

uint32_t bzla_util_num_digits(uint32_t x);

/*------------------------------------------------------------------------*/

char *bzla_util_dec_to_bin_str(BzlaMemMgr *mm, const char *str);

char *bzla_util_dec_to_bin_str_n(BzlaMemMgr *mm, const char *str, uint32_t len);

char *bzla_util_hex_to_bin_str(BzlaMemMgr *mm, const char *str);

char *bzla_util_hex_to_bin_str_n(BzlaMemMgr *mm, const char *str, uint32_t len);

/*------------------------------------------------------------------------*/

bool bzla_util_check_bin_to_bv(BzlaMemMgr *mm, const char *str, uint32_t bw);

bool bzla_util_check_dec_to_bv(BzlaMemMgr *mm, const char *str, uint32_t bw);

bool bzla_util_check_hex_to_bv(BzlaMemMgr *mm, const char *str, uint32_t bw);

/*------------------------------------------------------------------------*/

double bzla_util_time_stamp(void);
double bzla_util_process_time_thread(void);
double bzla_util_current_time(void);

/*------------------------------------------------------------------------*/

int32_t bzla_util_file_exists(const char *);
bool bzla_util_file_has_suffix(const char *path, const char *suffix);

/*------------------------------------------------------------------------*/

char *bzla_util_node2string(const BzlaNode *);

/*------------------------------------------------------------------------*/

char *bzla_util_getenv_value(BzlaMemMgr *mm, const char *name);

/*------------------------------------------------------------------------*/

#endif
