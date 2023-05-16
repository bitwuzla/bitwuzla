#include <bitwuzla/cpp/bitwuzla.h>

#include <iostream>

using namespace bitwuzla;

int
main()
{
  Result result;

  // First, create a Bitwuzla options instance.
  Options options;
  // (set-option :produce-models true)
  options.set(Option::PRODUCE_MODELS, true);

  // Then, create a Bitwuzla instance.
  std::unique_ptr<Bitwuzla> bitwuzla(new Bitwuzla(options));

  // Create a bit-vector sort of size 3.
  Sort sortbv3 = mk_bv_sort(3);

  // (declare-const x (_ BitVec 3))
  Term x = mk_const(sortbv3, "x");

  // (assert (= x #b010))
  bitwuzla->assert_formula(
      mk_term(Kind::EQUAL, {x, mk_bv_value_uint64(sortbv3, 2)}));
  // (check-sat)
  result = bitwuzla->check_sat();
  std::cout << "Expect: sat" << std::endl;
  std::cout << "Bitwuzla: "
            << (result == Result::SAT
                    ? "sat"
                    : (result == Result::UNSAT ? "unsat" : "unknown"))
            << std::endl;

  // (assert (= x #b001))
  bitwuzla->assert_formula(
      mk_term(Kind::EQUAL, {x, mk_bv_value_uint64(sortbv3, 1)}));
  // (check-sat)
  result = bitwuzla->check_sat();
  std::cout << "Expect: unsat" << std::endl;
  std::cout << "Bitwuzla: "
            << (result == Result::SAT
                    ? "sat"
                    : (result == Result::UNSAT ? "unsat" : "unknown"))
            << std::endl;

  // (reset-assertions)
  // Note: Bitwuzla does not provide an explicit API function for
  //       reset-assertions since this is achieved by simply discarding
  //       the current Bitwuzla instance and creating a new one.
  bitwuzla.reset(new Bitwuzla(options));

  // (assert (= x #b011))
  bitwuzla->assert_formula(
      mk_term(Kind::EQUAL, {x, mk_bv_value_uint64(sortbv3, 3)}));
  // (check-sat)
  result = bitwuzla->check_sat();
  std::cout << "Expect: sat" << std::endl;
  std::cout << "Bitwuzla: "
            << (result == Result::SAT
                    ? "sat"
                    : (result == Result::UNSAT ? "unsat" : "unknown"))
            << std::endl;

  // (get-model)
  std::cout << "(" << std::endl
            << "  (define-fun " << x.symbol()->get() << " () " << x.sort()
            << " " << bitwuzla->get_value(x) << ")" << std::endl
            << ")" << std::endl;

  return 0;
}
