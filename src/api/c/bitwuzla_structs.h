/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BITWUZLA_API_C_BITWUZLA_STRUCTS_H_INCLUDED
#define BITWUZLA_API_C_BITWUZLA_STRUCTS_H_INCLUDED

extern "C" {
#include <bitwuzla/c/bitwuzla.h>
}
#include <bitwuzla/cpp/bitwuzla.h>

#include <cassert>
#include <fstream>

#include "util/exceptions.h"

namespace bitwuzla::parser {
class Parser;
}

/* -------------------------------------------------------------------------- */

class CTerminator : public bitwuzla::Terminator
{
 public:
  /**
   * Constructor.
   * @param fun The associated termination function.
   * @param state The associated state.
   */
  CTerminator(int32_t (*fun)(void*), void* state) : f_fun(fun), d_state(state)
  {
  }

  bool terminate() override
  {
    if (f_fun == nullptr)
    {
      return false;
    }
    return f_fun(d_state);
  }

  void* get_state() { return d_state; }

 private:
  /** The associated termination function. */
  int32_t (*f_fun)(void*);
  /** The associated state. */
  void* d_state;
};

struct BitwuzlaOptions
{
  BitwuzlaOptions() : d_options(bitwuzla::Options()) {}
  BitwuzlaOptions(bitwuzla::Options& options) : d_options(options) {}

  void set_diagnostic_output_stream(const char* output_filename);

  bitwuzla::Options d_options;
  std::ofstream d_diag_output;
};

/** Wrapper for C++ terms. */
struct bitwuzla_term_t
{
  /**
   * Constructor.
   * @param term The wrapped C++ term.
   * @param tm   The associated term manager.
   */
  bitwuzla_term_t(const bitwuzla::Term& term, BitwuzlaTermManager* tm)
      : d_term(term), d_tm(tm)
  {
  }
  /** The wrapped C++ term. */
  bitwuzla::Term d_term;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager. */
  BitwuzlaTermManager* d_tm = nullptr;
};

struct bitwuzla_sort_t
{
  /**
   * Constructor.
   * @param sort The wrapped C++ sort.
   * @param tm   The associated term manager.
   */
  bitwuzla_sort_t(const bitwuzla::Sort& sort, BitwuzlaTermManager* tm)
      : d_sort(sort), d_tm(tm)
  {
  }
  /** The wrapped C++ sort. */
  bitwuzla::Sort d_sort;
  /** External refs count. */
  uint32_t d_refs = 1;
  /** The associated term manager. */
  BitwuzlaTermManager* d_tm = nullptr;
};

struct BitwuzlaTermManager
{
  static const bitwuzla::Sort& import_sort(BitwuzlaSort sort);
  static const bitwuzla::Term& import_term(BitwuzlaTerm term);

  /**
   * Export C++ sort to C API.
   * @param sort The sort to export.
   */
  BitwuzlaSort export_sort(const bitwuzla::Sort& sort);
  /**
   * Export C++ term to C API.
   * @param term The term to export.
   */
  BitwuzlaTerm export_term(const bitwuzla::Term& term);

  /* Manual memory management for sorts and terms. ------------------- */

  /**
   * Decrement the external ref count of a term. If the ref count reaches zero,
   * the term is released (freed).
   * @param term The term to release.
   */
  void release(bitwuzla_term_t* term);
  /**
   * Increment the external ref count of a term.
   * @param term The term to copy.
   * @return The copied term.
   */
  bitwuzla_term_t* copy(bitwuzla_term_t* term);
  /**
   * Decrement the external ref count of a sort. If the ref count reaches zero,
   * the sort is released (freed).
   * @param sort The sort to release.
   */
  void release(bitwuzla_sort_t* sort);
  /**
   * Increment the external ref count of a sort.
   * @param sort The sort to copy.
   * @return The copied sort.
   */
  bitwuzla_sort_t* copy(bitwuzla_sort_t* sort);

  /** Release all sorts and terms. */
  void release();

  /* ----------------------------------------------------------------- */

  /** The associated term manager instance. */
  bitwuzla::TermManager d_tm;

 private:
  /** Map exported (and alive) C++ sorts to wrapper sort. */
  std::unordered_map<bitwuzla::Sort, bitwuzla_sort_t> d_alloc_sorts;
  /** Map exported (and alive) C++ terms to wrapper term. */
  std::unordered_map<bitwuzla::Term, bitwuzla_term_t> d_alloc_terms;
};

struct Bitwuzla
{
  /**
   * Constructor, creates and owns a new Bitwuzla instance.
   * @param tm      The associated term manager.
   * @param options The configuration options, nullptr for the default
   *                configuration.
   */
  Bitwuzla(BitwuzlaTermManager* tm, const BitwuzlaOptions* options)
  {
    (void) tm;
    (void) options;
#if defined(BZLA_IS_SAT_SOLVER_CONFIGURED)
    if (options)
    {
      d_bitwuzla.reset(new bitwuzla::Bitwuzla(tm->d_tm, options->d_options));
    }
    else
    {
      d_bitwuzla.reset(new bitwuzla::Bitwuzla(tm->d_tm));
    }
    d_tm = tm;
#else
    throw bitwuzla::Unsupported(
        "C bindings for external SAT solver factory not supported");
#endif
  }

  /**
   * Constructor, wraps the Bitwuzla instance of a parser.
   * @note The parser replaces its Bitwuzla instance on (reset) and
   *       (reset-assertions), this wrapper always refers to the current one.
   * @param tm     The associated term manager.
   * @param parser The parser, must outlive this wrapper.
   */
  Bitwuzla(BitwuzlaTermManager* tm, bitwuzla::parser::Parser* parser)
      : d_tm(tm), d_parser(parser)
  {
  }

  /**
   * Get the wrapped Bitwuzla instance.
   *
   * For the instance of a parser, this is the current instance of the parser.
   * If the parser replaced it since the last call, this wrapper switches to
   * the new instance and drops the terminator configured via this wrapper,
   * which was configured for the previous instance.
   *
   * @return The wrapped Bitwuzla instance.
   */
  bitwuzla::Bitwuzla& get();

  /** The terminator configured via this wrapper. */
  std::unique_ptr<CTerminator> d_terminator;
  /**
   * The wrapped Bitwuzla instance. Declared after d_terminator so that it is
   * destroyed before the terminator it may refer to.
   */
  std::shared_ptr<bitwuzla::Bitwuzla> d_bitwuzla;
  /** The associated term manager. */
  BitwuzlaTermManager* d_tm = nullptr;
  /** The parser that owns the wrapped instance, nullptr if owned by this. */
  bitwuzla::parser::Parser* d_parser = nullptr;
};

/* -------------------------------------------------------------------------- */

#endif
