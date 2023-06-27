/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <bitwuzla/c/bitwuzla.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/time.h>

struct terminator_state
{
  struct timeval start;
  uint32_t time_limit_ms;
};

static int32_t
test_terminate(void* state)
{
  struct terminator_state* tstate = (struct terminator_state*) state;
  struct timeval now;
  gettimeofday(&now, NULL);
  if (((now.tv_sec - tstate->start.tv_sec) * 1000
       + (now.tv_usec - tstate->start.tv_usec) / 1000)
      >= tstate->time_limit_ms)
  {
    return 1;
  }
  return 0;
}

int
main()
{
  // First, create a Bitwuzla options instance.
  BitwuzlaOptions* options = bitwuzla_options_new();
  // Then, create a Bitwuzla instance.
  Bitwuzla* bitwuzla = bitwuzla_new(options);

  BitwuzlaSort bv = bitwuzla_mk_bv_sort(32);

  BitwuzlaTerm x = bitwuzla_mk_const(bv, "x");
  BitwuzlaTerm s = bitwuzla_mk_const(bv, "s");
  BitwuzlaTerm t = bitwuzla_mk_const(bv, "t");

  BitwuzlaTerm a = bitwuzla_mk_term2(
      BITWUZLA_KIND_DISTINCT,
      bitwuzla_mk_term2(BITWUZLA_KIND_BV_MUL,
                        s,
                        bitwuzla_mk_term2(BITWUZLA_KIND_BV_MUL, x, t)),
      bitwuzla_mk_term2(BITWUZLA_KIND_BV_MUL,
                        bitwuzla_mk_term2(BITWUZLA_KIND_BV_MUL, s, x),
                        t));

  // Now, we check that the following formula is unsat.
  // (assert (distinct (bvmul s (bvmul x t)) (bvmul (bvmul s x) t)))
  BitwuzlaTerm assumptions[1] = {a};
  printf("> Without terminator (with preprocessing):\n");
  printf("Expect: unsat\n");
  printf("Result: %s\n",
         bitwuzla_result_to_string(
             bitwuzla_check_sat_assuming(bitwuzla, 1, assumptions)));

  // Now, for illustration purposes, we disable preprocessing, which will
  // significantly increase solving time, and connect a terminator instance
  // that terminates after a certain time limit.
  bitwuzla_set_option(options, BITWUZLA_OPT_PREPROCESS, 0);
  // Create new Bitwuzla instance with reconfigured options.
  Bitwuzla* bitwuzla2 = bitwuzla_new(options);
  // Configure termination callback.
  struct terminator_state state;
  gettimeofday(&state.start, NULL);
  state.time_limit_ms = 1000;
  bitwuzla_set_termination_callback(bitwuzla2, test_terminate, &state);

  // Now, we expect Bitwuzla to be terminated during the check-sat call.
  printf("> With terminator (no preprocessing):\n");
  printf("Expect: unknown\n");
  printf("Result: %s\n",
         bitwuzla_result_to_string(
             bitwuzla_check_sat_assuming(bitwuzla2, 1, assumptions)));

  // Finally, delete the Bitwuzla and Bitwuzla options instance.
  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);

  return 0;
}
