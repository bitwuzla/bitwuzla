/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <bitwuzla/c/bitwuzla.h>
#include <stdio.h>
#include <assert.h>

int
main()
{
  // First, create a term manager instance.
  BitwuzlaTermManager *tm = bitwuzla_term_manager_new();
  // Create a Bitwuzla options instance.
  BitwuzlaOptions *options = bitwuzla_options_new();
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  // Then, create a Bitwuzla instance.
  Bitwuzla *bitwuzla = bitwuzla_new(tm, options);

  BitwuzlaSort sortb = bitwuzla_mk_bool_sort(tm);
  BitwuzlaTerm a = bitwuzla_mk_const(tm, sortb, "a");
  BitwuzlaTerm b = bitwuzla_mk_const(tm, sortb, "b");

  // Release sort reference.
  bitwuzla_sort_release(sortb);

  BitwuzlaTerm dis = bitwuzla_mk_term2(tm, BITWUZLA_KIND_DISTINCT, a, b);
  bitwuzla_assert(bitwuzla, dis);
  bitwuzla_check_sat(bitwuzla);

  // Release term reference.
  bitwuzla_term_release(dis);

  BitwuzlaTerm val_a = bitwuzla_get_value(bitwuzla, a);
  BitwuzlaTerm val_b = bitwuzla_get_value(bitwuzla, b);

  assert(val_a != val_b);
  printf("value a: %s\n", bitwuzla_term_to_string(val_a));
  printf("value b: %s\n", bitwuzla_term_to_string(val_b));

  // Release remaining term references.
  bitwuzla_term_release(val_a);
  bitwuzla_term_release(val_b);
  bitwuzla_term_release(a);
  bitwuzla_term_release(b);

  // At this point all sort and term references have been released. If all sort
  // and term references should be released at once we can also use the
  // following function.
  bitwuzla_term_manager_release(tm);

  // Finally, delete the Bitwuzla solver, options, and term manager instances.
  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);
  // Note: All sorts and terms not released until now will be released when
  // deleting the term manager.
  bitwuzla_term_manager_delete(tm);

  return 0;
}

