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

/* -------------------------------------------------------------------------- */

class CTerminator : public bitwuzla::Terminator
{
 public:
  /**
   * Constructor.
   * @param fun The associated termination function.
   * @param state The associated state.
   */
  CTerminator(int32_t (*fun)(void *), void *state) : f_fun(fun), d_state(state)
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

  void *get_state() { return d_state; }

 private:
  /** The associated termination function. */
  int32_t (*f_fun)(void *);
  /** The associated state. */
  void *d_state;
};

struct BitwuzlaOptions
{
  BitwuzlaOptions() : d_options(bitwuzla::Options()) {}
  BitwuzlaOptions(bitwuzla::Options &options) : d_options(options) {}
  bitwuzla::Options d_options;
};

/** Wrapper for C++ terms. */
struct bitwuzla_term_t
{
  /**
   * Constructor.
   * @param term The wrapped C++ term.
   * @param tm   The associated term manager.
   */
  bitwuzla_term_t(const bitwuzla::Term &term, BitwuzlaTermManager *tm)
      : d_term(term), d_tm(tm)
  {
  }
  /** The wrapped C++ term. */
  bitwuzla::Term d_term;
  /** External refs count. */
  uint32_t d_refs           = 1;
  /** The associated term manager. */
  BitwuzlaTermManager *d_tm = nullptr;
};

struct bitwuzla_sort_t
{
  /**
   * Constructor.
   * @param sort The wrapped C++ sort.
   * @param tm   The associated term manager.
   */
  bitwuzla_sort_t(const bitwuzla::Sort &sort, BitwuzlaTermManager *tm)
      : d_sort(sort), d_tm(tm)
  {
  }
  /** The wrapped C++ sort. */
  bitwuzla::Sort d_sort;
  /** External refs count. */
  uint32_t d_refs           = 1;
  /** The associated term manager. */
  BitwuzlaTermManager *d_tm = nullptr;
};

struct BitwuzlaTermManager
{
  static const bitwuzla::Sort &import_sort(BitwuzlaSort sort);
  static const bitwuzla::Term &import_term(BitwuzlaTerm term);

  /**
   * Export C++ sort to C API.
   * @param sort The sort to export.
   */
  BitwuzlaSort export_sort(const bitwuzla::Sort &sort);
  /**
   * Export C++ term to C API.
   * @param term The term to export.
   */
  BitwuzlaTerm export_term(const bitwuzla::Term &term);

  /* Manual memory management for sorts and terms. ------------------- */

  /**
   * Decrement the external ref count of a term. If the ref count reaches zero,
   * the term is released (freed).
   * @param term The term to release.
   */
  void release(bitwuzla_term_t *term);
  /**
   * Increment the external ref count of a term.
   * @param term The term to copy.
   * @return The copied term.
   */
  bitwuzla_term_t *copy(bitwuzla_term_t *term);
  /**
   * Decrement the external ref count of a sort. If the ref count reaches zero,
   * the sort is released (freed).
   * @param sort The sort to release.
   */
  void release(bitwuzla_sort_t *sort);
  /**
   * Increment the external ref count of a sort.
   * @param sort The sort to copy.
   * @return The copied sort.
   */
  bitwuzla_sort_t *copy(bitwuzla_sort_t *sort);

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
  Bitwuzla(BitwuzlaTermManager *tm, const BitwuzlaOptions *options)
  {
    if (options)
    {
      d_bitwuzla = new bitwuzla::Bitwuzla(tm->d_tm, options->d_options);
    }
    else
    {
      d_bitwuzla = new bitwuzla::Bitwuzla(tm->d_tm);
    }
    d_tm                    = tm;
    d_bitwuzla_needs_delete = true;
  }

  Bitwuzla(BitwuzlaTermManager *tm, bitwuzla::Bitwuzla *bitwuzla)
  {
    d_bitwuzla = bitwuzla;
    d_tm       = tm;
  }

  ~Bitwuzla()
  {
    if (d_bitwuzla_needs_delete)
    {
      delete d_bitwuzla;
    }
  }

  void reset()
  {
    // TODO: reset solving context and options?
  }

  /** The associated bitwuzla instance. */
  bitwuzla::Bitwuzla *d_bitwuzla = nullptr;
  /** True if d_bitwuzla must be deleted on destruction. */
  bool d_bitwuzla_needs_delete = false;
  /** The currently configured terminator. */
  std::unique_ptr<CTerminator> d_terminator;
  /** The associated term manager. */
  BitwuzlaTermManager *d_tm = nullptr;
};

/* -------------------------------------------------------------------------- */

#endif
