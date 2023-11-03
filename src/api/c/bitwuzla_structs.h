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

struct bitwuzla_term_t
{
  std::unique_ptr<bitwuzla::Term> d_term;
  BitwuzlaTermManager *d_tm = nullptr;
};

struct bitwuzla_sort_t
{
  std::unique_ptr<bitwuzla::Sort> d_sort;
  BitwuzlaTermManager *d_tm = nullptr;
};

struct BitwuzlaTermManager
{
  static const bitwuzla::Sort &import_sort(BitwuzlaSort sort);
  static const bitwuzla::Term &import_term(BitwuzlaTerm term);

  BitwuzlaTermManager();
  BitwuzlaTermManager(bitwuzla::TermManager &tm);
  ~BitwuzlaTermManager();

  BitwuzlaSort export_sort(const bitwuzla::Sort &sort);
  BitwuzlaTerm export_term(const bitwuzla::Term &term);

  /** The associated term manager instance. */
  bitwuzla::TermManager *d_tm;

 private:
  bool d_term_mgr_needs_delete = false;
  std::vector<std::unique_ptr<bitwuzla_sort_t>> d_alloc_sorts;
  std::vector<std::unique_ptr<bitwuzla_term_t>> d_alloc_terms;
};

struct Bitwuzla
{
  Bitwuzla(BitwuzlaTermManager *tm, const BitwuzlaOptions *options)
  {
    if (options)
    {
      d_bitwuzla = new bitwuzla::Bitwuzla(*tm->d_tm, options->d_options);
    }
    else
    {
      d_bitwuzla = new bitwuzla::Bitwuzla(*tm->d_tm);
    }
    d_tm                    = tm;
    d_bitwuzla_needs_delete = true;
  }

  Bitwuzla(bitwuzla::Bitwuzla *bitwuzla)
  {
    d_bitwuzla = bitwuzla;
    d_tm       = new BitwuzlaTermManager(bitwuzla->term_mgr());
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
