/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BITWUZLA_API_CHECKS_H_INCLUDED
#define BITWUZLA_API_CHECKS_H_INCLUDED

#include <iostream>
#include <sstream>

#include "util/ostream_voider.h"

namespace bitwuzla {

class BitwuzlaExceptionStream
{
 public:
  /** Constructor. */
  BitwuzlaExceptionStream();
  /**
   * Destructor.
   * @note This needs to be explicitly set to 'noexcept(false)' since it is
   *       a destructor that throws an exception and in C++11 all destructors
   *       default to noexcept(true) (else this triggers a call to
   *       `std::terminate)`.
   */
  ~BitwuzlaExceptionStream() noexcept(false);
  /** @return The associated stream. */
  std::ostream &ostream();

 private:
  /** The stream for the expection message. */
  std::stringstream d_stream;
};

#ifdef __has_builtin
#if __has_builtin(__builtin_expect)
#define BITWUZLA_PREDICT_TRUE(arg) (__builtin_expect(arg, true))
#else
#define BITWUZLA_PREDICT_TRUE(arg) arg
#endif
#else
#define BITWUZLA_PREDICT_TRUE(arg) arg
#endif

#define BITWUZLA_CHECK(cond)                              \
  BITWUZLA_PREDICT_TRUE(cond)                             \
  ? (void) 0                                              \
  : bzla::util::OstreamVoider()                           \
          & bitwuzla::BitwuzlaExceptionStream().ostream() \
                << "invalid call to '" << __PRETTY_FUNCTION__ << "', "

#define BITWUZLA_CHECK_NOT_NULL(arg) \
  BITWUZLA_CHECK((arg) != nullptr) << "expected non-null object";

#define BITWUZLA_CHECK_NOT_NULL_AT_IDX(arg, i) \
  BITWUZLA_CHECK((arg) != nullptr) << "expected non-null object at index " << i;

#define BITWUZLA_CHECK_NOT_ZERO(arg) \
  BITWUZLA_CHECK((arg) != 0) << "argument '" << #arg << "' must be > 0";

#define BITWUZLA_CHECK_GREATER_ONE(arg) \
  BITWUZLA_CHECK((arg) > 1) << "argument '" << #arg << "' must be > 1";

#define BITWUZLA_CHECK_STR_NOT_EMPTY(arg) \
  BITWUZLA_CHECK(!(arg).empty())          \
      << "argument '" << #arg << "' must not be an empty string";

#define BITWUZLA_CHECK_VALUE_BASE(arg)                                       \
  BITWUZLA_CHECK(arg == 2 || arg == 10 || arg == 16)                         \
      << "invalid base for string representations of values (must be 2 for " \
         "binary, 10 for decimal"                                            \
         "or 16 for hexadecimal), is '"                                      \
      << arg << "'";

#define BITWUZLA_CHECK_FORMAT(str) \
  BITWUZLA_CHECK(str == "smt2")    \
      << "invalid file format, expected 'smt2', 'btor' or 'btor2'";

#define BITWUZLA_CHECK_OPT_PRODUCE_UNSAT_ASSUMPTIONS(opts) \
  BITWUZLA_CHECK((opts).produce_unsat_assumptions())       \
      << "unsat assumptions production not enabled";

#define BITWUZLA_CHECK_OPT_PRODUCE_UNSAT_CORES(opts) \
  BITWUZLA_CHECK((opts).produce_unsat_cores())       \
      << "unsat core production not enabled";

#define BITWUZLA_CHECK_OPT_PRODUCE_MODELS(opts) \
  BITWUZLA_CHECK((opts).produce_models()) << "model production not enabled";

#define BITWUZLA_CHECK_LAST_CALL_SAT(what)        \
  BITWUZLA_CHECK(d_last_check_sat == Result::SAT) \
      << "cannot " << what << " if input formula is not sat";

#define BITWUZLA_CHECK_LAST_CALL_UNSAT(what)        \
  BITWUZLA_CHECK(d_last_check_sat == Result::UNSAT) \
      << "cannot " << what << " if input formula is not unsat";

#define BITWUZLA_CHECK_TERM_NOT_NULL(arg) \
  BITWUZLA_CHECK((arg).d_node != nullptr) << "expected non-null term";

#define BITWUZLA_CHECK_TERM_NOT_NULL_AT_IDX(args, i) \
  BITWUZLA_CHECK((args)[i].d_node != nullptr)        \
      << "expected non-null term at index " << i;

#define BITWUZLA_CHECK_TERM_IS_ARRAY(arg)                         \
  BITWUZLA_CHECK((arg).d_node && (arg).d_node->type().is_array()) \
      << "expected array term";

#define BITWUZLA_CHECK_TERM_IS_ARRAY_AT_IDX(args, i)                      \
  BITWUZLA_CHECK((args)[i].d_node && (args)[i].d_node->type().is_array()) \
      << "expected array term at index " << i;

#define BITWUZLA_CHECK_TERM_IS_BV(arg)                         \
  BITWUZLA_CHECK((arg).d_node && (arg).d_node->type().is_bv()) \
      << "expected bit-vector term";

#define BITWUZLA_CHECK_TERM_IS_BOOL_VALUE(arg)            \
  BITWUZLA_CHECK((arg).d_node && (arg).d_node->is_value() \
                 && (arg).d_node->type().is_bool())       \
      << "expected boolean value";

#define BITWUZLA_CHECK_TERM_IS_BV_VALUE(arg)              \
  BITWUZLA_CHECK((arg).d_node && (arg).d_node->is_value() \
                 && (arg).d_node->type().is_bv())         \
      << "expected bit-vector value";

#define BITWUZLA_CHECK_TERM_IS_FP(arg)                         \
  BITWUZLA_CHECK((arg).d_node && (arg).d_node->type().is_fp()) \
      << "expected floating-point term";

#define BITWUZLA_CHECK_TERM_IS_RM(arg)                    \
  BITWUZLA_CHECK((arg).d_node && !(arg).d_node->is_null() \
                 && (arg).d_node->type().is_rm())         \
      << "expected rounding-mode "                        \
         "term";
#define BITWUZLA_CHECK_TERM_IS_RM_AT_IDX(args, i)                 \
  BITWUZLA_CHECK((args)[i].d_node && !(args)[i].d_node->is_null() \
                 && (args)[i].d_node->type().is_rm())             \
      << "expected rounding-mode term at index " << i;

#define BITWUZLA_CHECK_TERM_IS_RM_VALUE(arg)                                  \
  BITWUZLA_CHECK((arg).d_node && !(arg).d_node->is_null()                     \
                 && (arg).d_node->is_value() && (arg).d_node->type().is_rm()) \
      << "expected rounding-mode value";

#define BITWUZLA_CHECK_TERM_IS_BOOL(arg)                  \
  BITWUZLA_CHECK((arg).d_node && !(arg).d_node->is_null() \
                 && (arg).d_node->type().is_bool())       \
      << "expected Boolean term";

#define BITWUZLA_CHECK_TERM_IS_BOOL_AT_IDX(args, i)               \
  BITWUZLA_CHECK((args)[i].d_node && !(args)[i].d_node->is_null() \
                 && (args)[i].d_node->type().is_bool())           \
      << "expected Boolean term at index " << i;

#define BITWUZLA_CHECK_TERM_IS_VAR_AT_IDX(args, i)                    \
  BITWUZLA_CHECK((args)[i].d_node && (args)[i].d_node->is_variable()) \
      << "expected variable at index " << i;

#define BITWUZLA_CHECK_TERM_IS_NOT_VAR(arg)                    \
  BITWUZLA_CHECK((arg).d_node && !(arg).d_node->is_variable()) \
      << "expected non-variable "                              \
         "term";

#define BITWUZLA_CHECK_TERM_IS_FUN_AT_IDX(args, i)                \
  BITWUZLA_CHECK((args)[i].d_node && !(args)[i].d_node->is_null() \
                 && (args)[i].d_node->type().is_fun())            \
      << "expected non-function term at index " << i;

#define BITWUZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(args, i)            \
  BITWUZLA_CHECK((args)[i].d_node && !(args)[i].d_node->is_null() \
                 && !(args)[i].d_node->type().is_fun())           \
      << "expected non-function term at index " << i;

#define BITWUZLA_CHECK_SORT_NOT_NULL(arg) \
  BITWUZLA_CHECK((arg).d_type != nullptr) << "expected non-null sort";

#define BITWUZLA_CHECK_SORT_IS_ARRAY(arg)                  \
  BITWUZLA_CHECK((arg).d_type && (arg).d_type->is_array()) \
      << "expected array sort";

#define BITWUZLA_CHECK_SORT_IS_BV(arg)                  \
  BITWUZLA_CHECK((arg).d_type && (arg).d_type->is_bv()) \
      << "expected bit-vector sort";

#define BITWUZLA_CHECK_SORT_IS_FP(arg)                  \
  BITWUZLA_CHECK((arg).d_type && (arg).d_type->is_fp()) \
      << "expected floating-point sort";

#define BITWUZLA_CHECK_SORT_IS_FUN(arg)                  \
  BITWUZLA_CHECK((arg).d_type && (arg).d_type->is_fun()) \
      << "expected function sort";

#define BITWUZLA_CHECK_SORT_NOT_IS_FUN(arg)               \
  BITWUZLA_CHECK((arg).d_type && !(arg).d_type->is_fun()) \
      << "expected non-function sort";

#define BITWUZLA_CHECK_SORT_IS_UNINTEPRETED(arg)                   \
  BITWUZLA_CHECK((arg).d_type && (arg).d_type->is_uninterpreted()) \
      << "expected uninterpreted sort";

#define BITWUZLA_CHECK_MK_TERM_ARGC(kind, is_nary, argc_expected, argc)       \
  BITWUZLA_CHECK((is_nary && argc >= argc_expected)                           \
                 || (!is_nary && argc == argc_expected))                      \
      << "invalid number of arguments for kind '" << (kind) << "', expected " \
      << (is_nary ? "(at least)" : "") << " '" << argc_expected               \
      << "' but got '" << argc << "'";

#define BITWUZLA_CHECK_MK_TERM_IDXC(kind, idxc_expected, idxc)              \
  BITWUZLA_CHECK(idxc == idxc_expected)                                     \
      << "invalid number of indices for kind '" << (kind) << "', expected " \
      << idxc_expected << "' but got '" << idxc << "'";

#define BITWUZLA_CHECK_MK_TERM_ARGS(args, start, is_sort_fun, match)           \
  do                                                                           \
  {                                                                            \
    for (size_t i = 0, argc = args.size(); i < argc; ++i)                      \
    {                                                                          \
      BITWUZLA_CHECK_NOT_NULL_AT_IDX(args[i].d_node, i);                       \
      if (i == start || i > start)                                             \
      {                                                                        \
        BITWUZLA_CHECK(args[i].d_node->type().is_sort_fun())                   \
            << "term with unexpected sort at index " << i;                     \
        if (i > start && (match))                                              \
        {                                                                      \
          BITWUZLA_CHECK(args[i].d_node->type() == args[i - 1].d_node->type()) \
              << "terms with mismatching sort at indices " << (i - 1)          \
              << " and " << i;                                                 \
        }                                                                      \
      }                                                                        \
    }                                                                          \
  } while (0)

#define BITWUZLA_CHECK_MK_TERM_ARGS_ANY_SORT(args, start, match)               \
  do                                                                           \
  {                                                                            \
    for (size_t i = 0, argc = args.size(); i < argc; ++i)                      \
    {                                                                          \
      BITWUZLA_CHECK_NOT_NULL_AT_IDX(args[i].d_node, i);                       \
      if (i > (start) && match)                                                \
      {                                                                        \
        BITWUZLA_CHECK(args[i].d_node->type() == args[i - 1].d_node->type())   \
            << "terms with mismatching sort at indices " << (i - 1) << " and " \
            << i;                                                              \
      }                                                                        \
    }                                                                          \
  } while (0)

}  // namespace bitwuzla

#endif
