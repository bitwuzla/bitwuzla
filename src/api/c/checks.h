/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BITWUZLA_API_C_CHECKS_H_INCLUDED
#define BITWUZLA_API_C_CHECKS_H_INCLUDED

/* -------------------------------------------------------------------------- */

#include <cstdlib>
#include <iostream>
#include <sstream>

struct BitwuzlaAbortCallback
{
  void (*abort_fun)(const char *msg);
  void *cb_fun; /* abort callback function */
};

/* Callback function to be executed on abort. Primarily intended to be used for
 * plugging in custom exception handling. */
static thread_local void (*bitwuzla_abort_callback)(const char *msg) = nullptr;

static void
bitwuzla_abort(const char *msg)
{
  if (!bitwuzla_abort_callback)
  {
    std::cerr << msg << std::endl;
    exit(EXIT_FAILURE);
  }
  bitwuzla_abort_callback(msg);
}

/* -------------------------------------------------------------------------- */

class BitwuzlaAbortStream
{
 public:
  BitwuzlaAbortStream(const std::string &msg_prefix)
  {
    stream() << msg_prefix << " ";
  }
  ~BitwuzlaAbortStream()
  {
    flush();
    bitwuzla_abort(d_stream.str().c_str());
  }
  std::ostream &stream() { return d_stream; }

 private:
  void flush()
  {
    stream() << std::endl;
    stream().flush();
  }
  std::stringstream d_stream;
};

#define BITWUZLA_ABORT        \
  bzla::util::OstreamVoider() \
      & BitwuzlaAbortStream("bitwuzla: error: ").stream()

#define BITWUZLA_C_TRY_CATCH_BEGIN \
  try                              \
  {
#define BITWUZLA_C_TRY_CATCH_END \
  }                              \
  catch (bitwuzla::Exception & e) { BITWUZLA_ABORT << e.msg(); }

/* -------------------------------------------------------------------------- */

#define BITWUZLA_CHECK_SORT(sort) \
  BITWUZLA_CHECK(sort != nullptr) << "invalid sort";

#define BITWUZLA_CHECK_SORT_AT_IDX(sorts, i) \
  BITWUZLA_CHECK(sorts[i] != nullptr) << "invalid sort at index " << i;

#define BITWUZLA_CHECK_TERM(term) \
  BITWUZLA_CHECK(term != nullptr) << "invalid term";

#define BITWUZLA_CHECK_TERM_AT_IDX(terms, i) \
  BITWUZLA_CHECK(terms[i] != nullptr) << "invalid term at index " << i;

#define BITWUZLA_CHECK_RM(rm) \
  BITWUZLA_CHECK((rm) < BITWUZLA_RM_MAX) << "invalid rounding mode";

#define BITWUZLA_CHECK_KIND(kind) \
  BITWUZLA_CHECK((kind) < BITWUZLA_KIND_NUM_KINDS) << "invalid term kind";

#define BITWUZLA_CHECK_OPTION(opt) \
  BITWUZLA_CHECK((opt) < BITWUZLA_OPT_NUM_OPTS) << "invalid option";

#define BITWUZLA_CHECK_RESULT(result)                                   \
  BITWUZLA_CHECK((result) == BITWUZLA_SAT || (result) == BITWUZLA_UNSAT \
                 || (result) == BITWUZLA_UNKNOWN)                       \
      << "invalid result";

#endif
