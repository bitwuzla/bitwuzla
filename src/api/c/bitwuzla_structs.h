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

struct Bitwuzla
{
  /** Map C++ API term to term id and external reference count. */
  using TermMap =
      std::unordered_map<BitwuzlaTerm,
                         std::pair<std::unique_ptr<bitwuzla::Term>, uint64_t>>;
  /** Map C++ API term to sort id and external reference count. */
  using SortMap =
      std::unordered_map<BitwuzlaSort,
                         std::pair<std::unique_ptr<bitwuzla::Sort>, uint64_t>>;

  Bitwuzla(const BitwuzlaOptions *options)
  {
    if (options)
    {
      d_bitwuzla = new bitwuzla::Bitwuzla(options->d_options);
    }
    else
    {
      d_bitwuzla = new bitwuzla::Bitwuzla();
    }
    d_bitwuzla_needs_delete = true;
  }

  Bitwuzla(bitwuzla::Bitwuzla *bitwuzla) { d_bitwuzla = bitwuzla; }

  ~Bitwuzla()
  {
    if (d_bitwuzla_needs_delete)
    {
      delete d_bitwuzla;
    }
  }

  /** Get the map from C++ API term id to term object. */
  static TermMap &term_map()
  {
    thread_local static TermMap map;
    return map;
  }

  /** Get the map from C++ API sort id to sort object. */
  static SortMap &sort_map()
  {
    thread_local static SortMap map;
    return map;
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
};

/* -------------------------------------------------------------------------- */

#endif
