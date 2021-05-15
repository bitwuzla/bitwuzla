#include <bitwuzla/bitwuzla.h>
#include <stdio.h>

int
main()
{
  BitwuzlaResult result;

  // First, create a Bitwuzla instance.
  Bitwuzla *bzla = bitwuzla_new();
  // Then, enable incremental solving.
  // Note: Incremental solving is disabled by default.
  bitwuzla_set_option(bzla, BITWUZLA_OPT_INCREMENTAL, 1);

  // Create a bit-vector sort of size 1.
  BitwuzlaSort *sortbv1 = bitwuzla_mk_bv_sort(bzla, 1);
  // Create a bit-vector sort of size 2.
  BitwuzlaSort *sortbv2 = bitwuzla_mk_bv_sort(bzla, 2);

  // Create bit-vector variables.
  // (declare-const o0 (_ BitVec 2))
  BitwuzlaTerm *o0 = bitwuzla_mk_const(bzla, sortbv1, "o0");
  // (declare-const o1 (_ BitVec 2))
  BitwuzlaTerm *o1 = bitwuzla_mk_const(bzla, sortbv1, "o1");
  // (declare-const s0 (_ BitVec 2))
  BitwuzlaTerm *s0 = bitwuzla_mk_const(bzla, sortbv2, "s0");
  // (declare-const s1 (_ BitVec 2))
  BitwuzlaTerm *s1 = bitwuzla_mk_const(bzla, sortbv2, "s1");
  // (declare-const s2 (_ BitVec 2))
  BitwuzlaTerm *s2 = bitwuzla_mk_const(bzla, sortbv2, "s2");
  // (declare-const goal (_ BitVec 2))
  BitwuzlaTerm *goal = bitwuzla_mk_const(bzla, sortbv2, "goal");

  // Create bit-vector values zero, one, three.
  BitwuzlaTerm *zero  = bitwuzla_mk_bv_zero(bzla, sortbv2);
  BitwuzlaTerm *one1  = bitwuzla_mk_bv_one(bzla, sortbv1);
  BitwuzlaTerm *one2  = bitwuzla_mk_bv_one(bzla, sortbv2);
  BitwuzlaTerm *three = bitwuzla_mk_bv_value_uint64(bzla, sortbv2, 3);

  // Add some assertions.
  bitwuzla_assert(bzla, bitwuzla_mk_term2(bzla, BITWUZLA_KIND_EQUAL, s0, zero));
  bitwuzla_assert(bzla,
                  bitwuzla_mk_term2(bzla, BITWUZLA_KIND_EQUAL, goal, three));

  // (check-sat-assuming ((= s0 goal)))
  bitwuzla_assume(bzla, bitwuzla_mk_term2(bzla, BITWUZLA_KIND_EQUAL, s0, goal));
  result = bitwuzla_check_sat(bzla);
  printf("Expect: unsat\n");
  printf("Bitwuzla: %s\n",
         result == BITWUZLA_SAT
             ? "sat"
             : (result == BITWUZLA_UNSAT ? "unsat" : "unknown"));

  // (assert (= s1 (ite (= o0 (_ sortbv1 1)) (bvadd s0 one) s0)))
  bitwuzla_assert(
      bzla,
      bitwuzla_mk_term2(
          bzla,
          BITWUZLA_KIND_EQUAL,
          s1,
          bitwuzla_mk_term3(
              bzla,
              BITWUZLA_KIND_ITE,
              bitwuzla_mk_term2(bzla, BITWUZLA_KIND_EQUAL, o0, one1),
              bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_ADD, s0, one2),
              s0)));

  // (check-sat-assuming ((= s1 goal)))
  bitwuzla_assume(bzla, bitwuzla_mk_term2(bzla, BITWUZLA_KIND_EQUAL, s1, goal));
  result = bitwuzla_check_sat(bzla);
  printf("Expect: unsat\n");
  printf("Bitwuzla: %s\n",
         result == BITWUZLA_SAT
             ? "sat"
             : (result == BITWUZLA_UNSAT ? "unsat" : "unknown"));

  // (assert (= s2 (ite (= o1 (_ sortbv1 1)) (bvadd s1 one) s1)))
  bitwuzla_assert(
      bzla,
      bitwuzla_mk_term2(
          bzla,
          BITWUZLA_KIND_EQUAL,
          s2,
          bitwuzla_mk_term3(
              bzla,
              BITWUZLA_KIND_ITE,
              bitwuzla_mk_term2(bzla, BITWUZLA_KIND_EQUAL, o1, one1),
              bitwuzla_mk_term2(bzla, BITWUZLA_KIND_BV_ADD, s1, one2),
              s1)));

  // (check-sat-assuming ((= s2 goal)))
  bitwuzla_assume(bzla, bitwuzla_mk_term2(bzla, BITWUZLA_KIND_EQUAL, s2, goal));
  result = bitwuzla_check_sat(bzla);
  printf("Expect: unsat\n");
  printf("Bitwuzla: %s\n",
         result == BITWUZLA_SAT
             ? "sat"
             : (result == BITWUZLA_UNSAT ? "unsat" : "unknown"));

  // Finally, delete the Bitwuzla instance.
  bitwuzla_delete(bzla);
}
