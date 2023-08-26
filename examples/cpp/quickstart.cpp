/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <assert.h>
#include <bitwuzla/cpp/bitwuzla.h>

#include <iostream>

using namespace bitwuzla;

int
main()
{
  // First, create a Bitwuzla options instance.
  Options options;
  // Then, enable model generation.
  options.set(Option::PRODUCE_MODELS, true);
  // Now, for illustration purposes, we enable CaDiCaL as SAT solver
  // (CaDiCaL is already configured by default).
  // Note: This will silently fall back to one of the compiled in SAT solvers
  //       if the selected solver is not compiled in.
  options.set(Option::SAT_SOLVER, "cadical");
  // Then, create a Bitwuzla instance.
  Bitwuzla bitwuzla(options);

  // Create bit-vector sorts of size 4 and 8.
  Sort sortbv4 = mk_bv_sort(4);
  Sort sortbv8 = mk_bv_sort(8);
  // Create function sort.
  Sort sortfun = mk_fun_sort({sortbv8, sortbv4}, sortbv8);
  // Create array sort.
  Sort sortarr = mk_array_sort(sortbv8, sortbv8);

  // Create two bit-vector constants of that sort.
  Term x = mk_const(sortbv8, "x");
  Term y = mk_const(sortbv8, "y");
  // Create fun const.
  Term f = mk_const(sortfun, "f");
  // Create array const.
  Term a = mk_const(sortarr, "a");
  // Create bit-vector values one and two of the same sort.
  Term one = mk_bv_one(sortbv8);
  // Alternatively, you can create bit-vector value one with:
  // Term one = mk_bv_value(sortbv8, "1", 2);
  // Term one = mk_bv_value_uint64(sortbv8, 1);
  Term two = mk_bv_value_uint64(sortbv8, 2);

  // (bvsdiv x (_ bv2 8))
  Term sdiv = mk_term(Kind::BV_SDIV, {x, two});
  // (bvashr y (_ bv1 8))
  Term ashr = mk_term(Kind::BV_ASHR, {y, one});
  // ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
  Term sdive = mk_term(Kind::BV_EXTRACT, {sdiv}, {3, 0});
  // ((_ extract 3 0) (bvashr x (_ bv1 8)))
  Term ashre = mk_term(Kind::BV_EXTRACT, {ashr}, {3, 0});

  // (assert
  //     (distinct
  //         ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
  //         ((_ extract 3 0) (bvashr y (_ bv1 8)))))
  bitwuzla.assert_formula(mk_term(Kind::DISTINCT, {sdive, ashre}));
  // (assert (= (f x ((_ extract 6 3) x)) y))
  bitwuzla.assert_formula(mk_term(
      Kind::EQUAL,
      {mk_term(Kind::APPLY, {f, x, mk_term(Kind::BV_EXTRACT, {x}, {6, 3})}),
       y}));
  // (assert (= (select a x) y))
  bitwuzla.assert_formula(
      mk_term(Kind::EQUAL, {mk_term(Kind::ARRAY_SELECT, {a, x}), y}));

  // (check-sat)
  Result result = bitwuzla.check_sat();

  std::cout << "Expect: sat" << std::endl;
  std::cout << "Bitwuzla: "
            << (result == Result::SAT
                    ? "sat"
                    : (result == Result::UNSAT ? "unsat" : "unknown"))
            << std::endl
            << std::endl;

  // Print model in SMT-LIBv2 format.
  std::cout << "Model:" << std::endl << "(" << std::endl;
  for (const auto& term : {x, y, f, a})
  {
    Sort sort = term.sort();
    std::cout << "  (define-fun "
              << (term.symbol() ? *term.symbol()
                                : "@t" + std::to_string(term.id()))
              << " (";
    if (sort.is_fun())
    {
      bitwuzla::Term value = bitwuzla.get_value(term);
      assert(value.kind() == bitwuzla::Kind::LAMBDA);
      assert(value.num_children() == 2);
      while (value[1].kind() == bitwuzla::Kind::LAMBDA)
      {
        assert(value[0].is_variable());
        std::cout << "(" << value[0] << " " << value[0].sort() << ") ";
        value = value[1];
      }
      assert(value[0].is_variable());
      std::cout << "(" << value[0] << " " << value[0].sort() << ")) "
                << sort.fun_codomain() << " ";
      std::cout << value[1] << ")" << std::endl;
    }
    else
    {
      std::cout << ") " << sort << " " << bitwuzla.get_value(term) << ")"
                << std::endl;
    }
  }
  std::cout << ")" << std::endl << std::endl;

  // Print value for x, y, f and a.
  // Note: The returned string of Term::value() is only valid until the next
  //       call to Term::value().
  // Both x and y are bit-vector terms and their value is a bit-vector
  // value that can be printed via Term::value().
  std::cout << "value of x: " << bitwuzla.get_value(x).value<std::string>(2)
            << std::endl;
  std::cout << "value of y: " << bitwuzla.get_value(y).value<std::string>(2)
            << std::endl;
  std::cout << std::endl;
  // f and a, on the other hand, are a function and array term, respectively.
  // The value of these terms is not a value term: for f, it is a lambda term,
  // and the value of a is represented as a store term. Thus we cannot use
  // Term::value(), but we can print the value of the terms via Term::str()
  // or operator<<.
  std::cout << "str() representation of value of f:" << std::endl
            << bitwuzla.get_value(f) << std::endl
            << std::endl;
  std::cout << "str() representation of value of a:" << std::endl
            << bitwuzla.get_value(a) << std::endl
            << std::endl;
  std::cout << std::endl;
  // Note that the assignment string of bit-vector terms is given as the
  // pure assignment string, either in binary, hexadecimal or decimal format,
  // whereas Term::str() and operator<< print the value in SMT-LIB2 format
  // ((in the configured bit-vector output number format, binary by default).
  std::cout << "str() representation of value of x: " << bitwuzla.get_value(x)
            << std::endl;
  std::cout << "str() representation of value of y: " << bitwuzla.get_value(y)
            << std::endl;
  std::cout << std::endl;

  // Query value of bit-vector term that does not occur in the input formula
  Term v = bitwuzla.get_value(mk_term(Kind::BV_MUL, {x, x}));
  std::cout << "value of v = x * x: " << v.value<std::string>(2) << std::endl;

  return 0;
}
