#include <bitwuzla/bitwuzla.h>
#include <stdio.h>

int
main()
{
  // First, create a Bitwuzla instance.
  Bitwuzla *bzla = bitwuzla_new();
  // Then, enable model generation.
  bitwuzla_set_option(bzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  // Now, we enable CryptoMiniSat as SAT solver.
  // Note: This will silently fall back to one of the compiled in SAT solvers
  //       if the selected solver is not compiled in.
  bitwuzla_set_option_str(bzla, BITWUZLA_OPT_SAT_ENGINE, "cms");

  // Create a bit-vector sort of size 8.
  BitwuzlaSort *sortbv8 = bitwuzla_mk_bv_sort(bzla, 8);

  // Create two bit-vector variables of that sort.
  BitwuzlaTerm *x = bitwuzla_mk_const(bzla, sortbv8, "x");
  BitwuzlaTerm *y = bitwuzla_mk_const(bzla, sortbv8, "y");
  // Create bit-vector values one and two of the same sort.
  BitwuzlaTerm *one = bitwuzla_mk_bv_one(bzla, sortbv8);
  // alternatively, you can create bit-vector value one with:
  // BitwuzlaTerm *one =
  //     bitwuzla_mk_bv_value(bzla, sortbv8, "1", BITWUZLA_BV_BASE_BIN);
  // BitwuzlaTerm *one = bitwuzla_mk_bv_value_uint64(bzla, sortbv8, 1);
  BitwuzlaTerm *two = bitwuzla_mk_bv_value_uint64(bzla, sortbv8, 2);

  // (bvsdiv x (_ sortbv2 8))
  BitwuzlaTerm *sdiv = bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_SDIV, x, two);
  // (bvashr y (_ sortbv1 8))
  BitwuzlaTerm *ashr = bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_ASHR, y, one);
  // ((_ extract 3 0) (bvsdiv x (_ sortbv2 8)))
  BitwuzlaTerm *sdive =
      bitwuzla_mk_term1_indexed2(bzla, BITWUZLA_KIND_BV_EXTRACT, sdiv, 3, 0);
  // ((_ extract 3 0) (bvashr x (_ sortbv1 8)))
  BitwuzlaTerm *ashre =
      bitwuzla_mk_term1_indexed2(bzla, BITWUZLA_KIND_BV_EXTRACT, ashr, 3, 0);

  // (assert
  //     (distinct
  //         ((_ extract 3 0) (bvsdiv x (_ sortbv2 8)))
  //         ((_ extract 3 0) (bvashr y (_ sortbv1 8)))
  bitwuzla_assert(
      bzla, bitwuzla_mk_term2(bzla, BITWUZLA_KIND_DISTINCT, sdive, ashre));

  // (check-sat)
  BitwuzlaResult result = bitwuzla_check_sat(bzla);

  printf("Expect: sat\n");
  printf("Bitwuzla: %s\n\n",
         result == BITWUZLA_SAT
             ? "sat"
             : (result == BITWUZLA_UNSAT ? "unsat" : "unknown"));

  printf("Model:\n");
  // Print model in SMT-LIBv2 format.
  bitwuzla_print_model(bzla, "smt2", stdout);
  printf("\n");

  // Get assignment strings for x and y
  // Note: The returned string is only valid until the next call to
  //       bitwuzla_get_bv_value
  const char *xstr = bitwuzla_get_bv_value(bzla, x);  // returns "11111111"
  printf("assignment of x: %s\n", xstr);
  const char *ystr = bitwuzla_get_bv_value(bzla, y);  // returns "00011110"
  printf("assignment of y: %s\n", ystr);
  printf("\n");

  // Alternatively, get values for x and y as terms
  BitwuzlaTerm *x_value = bitwuzla_get_value(bzla, x);
  BitwuzlaTerm *y_value = bitwuzla_get_value(bzla, y);
  const char *xvaluestr =
      bitwuzla_get_bv_value(bzla, x_value);  // returns "11111111"
  printf("assignment of x (via bitwuzla_get_value): %s\n", xvaluestr);
  const char *yvaluestr =
      bitwuzla_get_bv_value(bzla, y_value);  // returns "00011110"
  printf("assignment of y (via bitwuzla_get_value): %s\n", yvaluestr);
  printf("\n");

  // Query value of expression that does not occur in the input formula
  BitwuzlaTerm *v = bitwuzla_get_value(
      bzla, bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_MUL, x, x));
  printf("assignment of v = x * x: %s\n", bitwuzla_get_bv_value(bzla, v));

  // Finally, delete the Bitwuzla instance.
  bitwuzla_delete(bzla);
}
