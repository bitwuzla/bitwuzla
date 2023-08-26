/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2021 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <assert.h>
#include <bitwuzla/c/bitwuzla.h>
#include <stdio.h>

int
main()
{
  // First, create a Bitwuzla options instance.
  BitwuzlaOptions *options = bitwuzla_options_new();
  // Then, enable model generation.
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  // Now, for illustration purposes, we enable CaDiCaL as SAT solver
  // (CaDiCaL is already configured by default).
  // Note: This will silently fall back to one of the compiled in SAT solvers
  //       if the selected solver is not compiled in.
  bitwuzla_set_option_mode(options, BITWUZLA_OPT_SAT_SOLVER, "cadical");
  // Then, create a Bitwuzla instance.
  Bitwuzla *bitwuzla = bitwuzla_new(options);

  // Create bit-vector sorts of size 4 and 8.
  BitwuzlaSort sortbv4 = bitwuzla_mk_bv_sort(4);
  BitwuzlaSort sortbv8 = bitwuzla_mk_bv_sort(8);
  // Create function sort.
  BitwuzlaSort domain[2] = {sortbv8, sortbv4};
  BitwuzlaSort sortfun   = bitwuzla_mk_fun_sort(2, domain, sortbv8);
  // Create array sort.
  BitwuzlaSort sortarr = bitwuzla_mk_array_sort(sortbv8, sortbv8);

  // Create two bit-vector constants of that sort.
  BitwuzlaTerm x = bitwuzla_mk_const(sortbv8, "x");
  BitwuzlaTerm y = bitwuzla_mk_const(sortbv8, "y");
  // Create fun const.
  BitwuzlaTerm f = bitwuzla_mk_const(sortfun, "f");
  // Create array const.
  BitwuzlaTerm a = bitwuzla_mk_const(sortarr, "a");
  // Create bit-vector values one and two of the same sort.
  BitwuzlaTerm one = bitwuzla_mk_bv_one(sortbv8);
  // Alternatively, you can create bit-vector value one with:
  // BitwuzlaTerm one = bitwuzla_mk_bv_value(sortbv8, "1", 2);
  // BitwuzlaTerm one = bitwuzla_mk_bv_value_uint64(sortbv8, 1);
  BitwuzlaTerm two = bitwuzla_mk_bv_value_uint64(sortbv8, 2);

  // (bvsdiv x (_ bv2 8))
  BitwuzlaTerm sdiv = bitwuzla_mk_term2(BITWUZLA_KIND_BV_SDIV, x, two);
  // (bvashr y (_ bv1 8))
  BitwuzlaTerm ashr = bitwuzla_mk_term2(BITWUZLA_KIND_BV_ASHR, y, one);
  // ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
  BitwuzlaTerm sdive =
      bitwuzla_mk_term1_indexed2(BITWUZLA_KIND_BV_EXTRACT, sdiv, 3, 0);
  // ((_ extract 3 0) (bvashr x (_ bv1 8)))
  BitwuzlaTerm ashre =
      bitwuzla_mk_term1_indexed2(BITWUZLA_KIND_BV_EXTRACT, ashr, 3, 0);

  // (assert
  //     (distinct
  //         ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
  //         ((_ extract 3 0) (bvashr y (_ bv1 8)))))
  bitwuzla_assert(bitwuzla,
                  bitwuzla_mk_term2(BITWUZLA_KIND_DISTINCT, sdive, ashre));
  // (assert (= (f x ((_ extract 6 3) x)) y))
  bitwuzla_assert(bitwuzla,
                  bitwuzla_mk_term2(
                      BITWUZLA_KIND_EQUAL,
                      bitwuzla_mk_term3(BITWUZLA_KIND_APPLY,
                                        f,
                                        x,
                                        bitwuzla_mk_term1_indexed2(
                                            BITWUZLA_KIND_BV_EXTRACT, x, 6, 3)),
                      y));
  // (assert (= (select a x) y))
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(BITWUZLA_KIND_EQUAL,
                        bitwuzla_mk_term2(BITWUZLA_KIND_ARRAY_SELECT, a, x),
                        y));

  // (check-sat)
  BitwuzlaResult result = bitwuzla_check_sat(bitwuzla);

  printf("Expect: sat\n");
  printf("Bitwuzla: %s\n\n",
         result == BITWUZLA_SAT
             ? "sat"
             : (result == BITWUZLA_UNSAT ? "unsat" : "unknown"));

  // Print model in SMT-LIBv2 format.
  printf("Model:\n");
  BitwuzlaTerm decls[4] = {x, y, f, a};
  printf("(\n");
  for (uint32_t i = 0; i < 4; ++i)
  {
    BitwuzlaSort sort = bitwuzla_term_get_sort(decls[i]);
    printf("  (define-fun %s (", bitwuzla_term_get_symbol(decls[i]));
    if (bitwuzla_sort_is_fun(sort))
    {
      BitwuzlaTerm value = bitwuzla_get_value(bitwuzla, decls[i]);
      size_t size;
      BitwuzlaTerm *children = bitwuzla_term_get_children(value, &size);
      assert(size == 2);
      while (bitwuzla_term_get_kind(children[1]) == BITWUZLA_KIND_LAMBDA)
      {
        assert(bitwuzla_term_is_var(children[0]));
        printf("(%s %s) ",
               bitwuzla_term_to_string(children[0]),
               bitwuzla_sort_to_string(bitwuzla_term_get_sort(children[0])));
        value    = children[1];
        children = bitwuzla_term_get_children(value, &size);
      }
      assert(bitwuzla_term_is_var(children[0]));
      // Note: The returned string of bitwuzla_term_to_string and
      //       bitwuzla_sort_to_string does not have to be freed, but is only
      //       valid until the next call to the respective function. Thus we
      //       split printing into separate printf calls so that none of these
      //       functions is called more than once in one printf call.
      //       Alternatively, we could also first get and copy the strings, use
      //       a single printf call, and then free the copied strings.
      printf("(%s %s))",
             bitwuzla_term_to_string(children[0]),
             bitwuzla_sort_to_string(bitwuzla_term_get_sort(children[0])));
      printf(" %s",
             bitwuzla_sort_to_string(bitwuzla_sort_fun_get_codomain(sort)));
      printf(" %s)\n", bitwuzla_term_to_string(children[1]));
    }
    else
    {
      printf(") %s %s)\n",
             bitwuzla_sort_to_string(sort),
             bitwuzla_term_to_string(bitwuzla_get_value(bitwuzla, decls[i])));
    }
  }
  printf(")\n");
  printf("\n");

  // Print value for x, y, f and a.
  // Note: The returned string of bitwuzla_term_value_get_str is only valid
  //       until the next call to bitwuzla_term_value_get_str
  // Both x and y are bit-vector terms and their value is a bit-vector
  // value that can be printed via bitwuzla_term_value_get_str().
  printf("value of x: %s\n",
         bitwuzla_term_value_get_str(bitwuzla_get_value(bitwuzla, x)));
  printf("value of y: %s\n",
         bitwuzla_term_value_get_str(bitwuzla_get_value(bitwuzla, y)));
  printf("\n");
  // f and a, on the other hand, are a function and array term, respectively.
  // The value of these terms is not a value term: for f, it is a lambda term,
  // and the value of a is represented as a store term. Thus we cannot use
  // bitwuzla_term_value_get_str(), but we can print the value of the terms
  // via bitwuzla_term_to_string().
  printf("to_string representation of value of f:\n%s\n\n",
         bitwuzla_term_to_string(bitwuzla_get_value(bitwuzla, f)));
  printf("to_string representation of value of a:\n%s\n",
         bitwuzla_term_to_string(bitwuzla_get_value(bitwuzla, a)));
  printf("\n");
  // Note that the assignment string of bit-vector terms is given as the
  // pure assignment string, either in binary, hexadecimal or decimal format,
  // whereas bitwuzla_term_to_string() prints the value in SMT-LIB2 format
  // (in binary number format).
  printf("to_string representation of value of x: %s\n",
         bitwuzla_term_to_string(bitwuzla_get_value(bitwuzla, x)));
  printf("to_string representation of value of y: %s\n",
         bitwuzla_term_to_string(bitwuzla_get_value(bitwuzla, y)));
  printf("\n");

  // Query value of bit-vector term that does not occur in the input formula
  BitwuzlaTerm v = bitwuzla_get_value(
      bitwuzla, bitwuzla_mk_term2(BITWUZLA_KIND_BV_MUL, x, x));
  printf("value of v = x * x: %s\n",
         bitwuzla_term_value_get_str(bitwuzla_get_value(bitwuzla, v)));

  // Finally, delete the Bitwuzla and the Bitwuzla options instance.
  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);

  return 0;
}
