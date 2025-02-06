/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

extern "C" {
#include <bitwuzla/c/bitwuzla.h>
}

#include <cassert>
#include <cstring>
#include <unordered_map>

#include "api/c/bitwuzla_structs.h"
#include "api/c/checks.h"
#include "api/checks.h"
#include "terminator.h"

/* -------------------------------------------------------------------------- */

// Note: Definition of class CTerminator and structs BitwuzlaOptions,
//       BitwuzlaTermManager and Bitwuzla is in api/c/bitwuzla_structs.h

/* -------------------------------------------------------------------------- */

#define BZLA_IMPORT_BITWUZLA_OPTION(option) (bzla_options.at(option))
#define BZLA_EXPORT_BITWUZLA_OPTION(option) (bitwuzla_options.at(option))

/* -------------------------------------------------------------------------- */

namespace {

BitwuzlaKind
export_kind(bitwuzla::Kind kind)
{
  return static_cast<BitwuzlaKind>(kind);
}

bitwuzla::Kind
import_kind(BitwuzlaKind kind)
{
  return static_cast<bitwuzla::Kind>(kind);
}

bitwuzla::Option
import_option(BitwuzlaOption option)
{
  return static_cast<bitwuzla::Option>(option);
}

}  // namespace

/* -------------------------------------------------------------------------- */
/* BitwuzlaKind                                                               */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_kind_to_string(BitwuzlaKind kind)
{
  static thread_local std::string str;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  str = "BITWUZLA_KIND_" + std::to_string(static_cast<bitwuzla::Kind>(kind));
  BITWUZLA_C_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaRoundingMode                                                       */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_rm_to_string(BitwuzlaRoundingMode rm)
{
  static thread_local std::string str;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_RM(rm);
  str =
      "BITWUZLA_RM_" + std::to_string(static_cast<bitwuzla::RoundingMode>(rm));
  BITWUZLA_C_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaResult                                                             */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_result_to_string(BitwuzlaResult result)
{
  static thread_local std::string str;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_RESULT(result);
  str = std::to_string(static_cast<bitwuzla::Result>(result));
  BITWUZLA_C_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_term_to_string(BitwuzlaTerm term)
{
  static thread_local std::string str;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  str = BitwuzlaTermManager::import_term(term).str();
  BITWUZLA_C_TRY_CATCH_END;
  return str.c_str();
}

const char *
bitwuzla_term_to_string_fmt(BitwuzlaTerm term, uint8_t base)
{
  static thread_local std::string str;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  str = BitwuzlaTermManager::import_term(term).str(base);
  BITWUZLA_C_TRY_CATCH_END;
  return str.c_str();
}

const char *
bitwuzla_term_fp_value_to_real_string(BitwuzlaTerm term)
{
  static thread_local std::string str;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  str = BitwuzlaTermManager::import_term(term).fp_value_to_real_str();
  BITWUZLA_C_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_sort_to_string(BitwuzlaSort sort)
{
  static thread_local std::string str;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  str = BitwuzlaTermManager::import_sort(sort).str();
  BITWUZLA_C_TRY_CATCH_END;
  return str.c_str();
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaOptions                                                            */
/* -------------------------------------------------------------------------- */

BitwuzlaOptions *
bitwuzla_options_new()
{
  BitwuzlaOptions *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  res = new BitwuzlaOptions();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

void
bitwuzla_options_delete(BitwuzlaOptions *options)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  delete options;
  BITWUZLA_C_TRY_CATCH_END;
}

bool
bitwuzla_option_is_valid(BitwuzlaOptions *options, const char *name)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  res = options->d_options.is_valid(name);
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_option_is_numeric(BitwuzlaOptions *options, BitwuzlaOption option)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  res = options->d_options.is_numeric(static_cast<bitwuzla::Option>(option));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_option_is_mode(BitwuzlaOptions *options, BitwuzlaOption option)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  res = options->d_options.is_mode(static_cast<bitwuzla::Option>(option));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_option_is_string(BitwuzlaOptions *options, BitwuzlaOption option)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  res = options->d_options.is_str(static_cast<bitwuzla::Option>(option));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

void
bitwuzla_set_option(BitwuzlaOptions *options,
                    BitwuzlaOption option,
                    uint64_t value)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  options->d_options.set(import_option(option), value);
  BITWUZLA_C_TRY_CATCH_END;
}

void
bitwuzla_set_option_mode(BitwuzlaOptions *options,
                         BitwuzlaOption option,
                         const char *value)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  BITWUZLA_CHECK_NOT_NULL(value);
  options->d_options.set(import_option(option), value);
  BITWUZLA_C_TRY_CATCH_END;
}

void
bitwuzla_set_option_string(BitwuzlaOptions *options,
                           BitwuzlaOption option,
                           const char *value)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  BITWUZLA_CHECK_NOT_NULL(value);
  options->d_options.set(import_option(option), value);
  BITWUZLA_C_TRY_CATCH_END;
}

uint64_t
bitwuzla_get_option(BitwuzlaOptions *options, BitwuzlaOption option)
{
  uint64_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  res = options->d_options.get(import_option(option));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

const char *
bitwuzla_get_option_mode(BitwuzlaOptions *options, BitwuzlaOption option)
{
  const char *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  res = options->d_options.get_mode(import_option(option)).c_str();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

const char *
bitwuzla_get_option_string(BitwuzlaOptions *options, BitwuzlaOption option)
{
  const char *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  res = options->d_options.get_str(import_option(option)).c_str();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

void
bitwuzla_get_option_info(BitwuzlaOptions *options,
                         BitwuzlaOption option,
                         BitwuzlaOptionInfo *info)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  BITWUZLA_CHECK_NOT_NULL(info);

  static thread_local bitwuzla::OptionInfo cpp_info;
  cpp_info = bitwuzla::OptionInfo(options->d_options, import_option(option));

  std::memset(info, 0, sizeof(*info));
  info->opt         = option;
  info->shrt        = cpp_info.shrt;
  info->lng         = cpp_info.lng;
  info->description = cpp_info.description;

  if (cpp_info.kind == bitwuzla::OptionInfo::Kind::BOOL)
  {
    info->numeric.cur =
        std::get<bitwuzla::OptionInfo::Bool>(cpp_info.values).cur;
    info->numeric.dflt =
        std::get<bitwuzla::OptionInfo::Bool>(cpp_info.values).dflt;
    info->numeric.min = 0;
    info->numeric.max = 1;
    info->is_numeric  = true;
  }
  else if (cpp_info.kind == bitwuzla::OptionInfo::Kind::NUMERIC)
  {
    info->numeric.cur =
        std::get<bitwuzla::OptionInfo::Numeric>(cpp_info.values).cur;
    info->numeric.dflt =
        std::get<bitwuzla::OptionInfo::Numeric>(cpp_info.values).dflt;
    info->numeric.min =
        std::get<bitwuzla::OptionInfo::Numeric>(cpp_info.values).min;
    info->numeric.max =
        std::get<bitwuzla::OptionInfo::Numeric>(cpp_info.values).max;
    info->is_numeric = true;
  }
  else if (cpp_info.kind == bitwuzla::OptionInfo::Kind::MODE)
  {
    info->mode.cur =
        std::get<bitwuzla::OptionInfo::Mode>(cpp_info.values).cur.c_str();
    info->mode.dflt =
        std::get<bitwuzla::OptionInfo::Mode>(cpp_info.values).dflt.c_str();
    info->mode.num_modes =
        std::get<bitwuzla::OptionInfo::Mode>(cpp_info.values).modes.size();
    static thread_local std::vector<const char *> c_modes;
    c_modes.clear();
    for (const auto &m :
         std::get<bitwuzla::OptionInfo::Mode>(cpp_info.values).modes)
    {
      c_modes.push_back(m.c_str());
    }
    info->mode.modes = c_modes.data();
    info->is_mode    = true;
  }
  else
  {
    assert(cpp_info.kind == bitwuzla::OptionInfo::Kind::STRING);
    info->string.cur =
        std::get<bitwuzla::OptionInfo::String>(cpp_info.values).cur.c_str();
    info->string.dflt =
        std::get<bitwuzla::OptionInfo::String>(cpp_info.values).dflt.c_str();
    info->is_string = true;
  }
  BITWUZLA_C_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* Library info                                                               */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_copyright()
{
  const char *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  res = bitwuzla::copyright();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

const char *
bitwuzla_version()
{
  const char *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  res = bitwuzla::version();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

const char *
bitwuzla_git_id()
{
  const char *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  res = bitwuzla::git_id();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

Bitwuzla *
bitwuzla_new(BitwuzlaTermManager *tm, const BitwuzlaOptions *options)
{
  Bitwuzla *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  res = new Bitwuzla(tm, options);
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

void
bitwuzla_delete(Bitwuzla *bitwuzla)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  delete bitwuzla;
  BITWUZLA_C_TRY_CATCH_END;
}

void
bitwuzla_set_termination_callback(Bitwuzla *bitwuzla,
                                  int32_t (*fun)(void *),
                                  void *state)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(fun);
  bitwuzla->d_terminator.reset(new CTerminator(fun, state));
  bitwuzla->d_bitwuzla->configure_terminator(bitwuzla->d_terminator.get());
  BITWUZLA_C_TRY_CATCH_END;
}

void *
bitwuzla_get_termination_callback_state(Bitwuzla *bitwuzla)
{
  void *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  res = bitwuzla->d_terminator ? bitwuzla->d_terminator->get_state() : nullptr;
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

void
bitwuzla_set_abort_callback(void (*fun)(const char *msg))
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  bitwuzla_abort_callback = fun;
  BITWUZLA_C_TRY_CATCH_END;
}

void
bitwuzla_push(Bitwuzla *bitwuzla, uint64_t nlevels)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  bitwuzla->d_bitwuzla->push(nlevels);
  BITWUZLA_C_TRY_CATCH_END;
}

void
bitwuzla_pop(Bitwuzla *bitwuzla, uint64_t nlevels)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  bitwuzla->d_bitwuzla->pop(nlevels);
  BITWUZLA_C_TRY_CATCH_END;
}

void
bitwuzla_assert(Bitwuzla *bitwuzla, BitwuzlaTerm term)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_TERM(term);
  bitwuzla->d_bitwuzla->assert_formula(BitwuzlaTermManager::import_term(term));
  BITWUZLA_C_TRY_CATCH_END;
}

const BitwuzlaTerm *
bitwuzla_get_assertions(Bitwuzla *bitwuzla, size_t *size)
{
  static thread_local std::vector<BitwuzlaTerm> res;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  res.clear();
  auto assertions = bitwuzla->d_bitwuzla->get_assertions();
  auto tm         = bitwuzla->d_tm;
  for (auto &term : assertions)
  {
    res.push_back(tm->export_term(term));
  }
  *size = res.size();
  BITWUZLA_C_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

bool
bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla, BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_TERM(term);
  res = bitwuzla->d_bitwuzla->is_unsat_assumption(
      BitwuzlaTermManager::import_term(term));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

const BitwuzlaTerm *
bitwuzla_get_unsat_assumptions(Bitwuzla *bitwuzla, size_t *size)
{
  static thread_local std::vector<BitwuzlaTerm> res;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(size);
  res.clear();
  auto unsat_assumptions = bitwuzla->d_bitwuzla->get_unsat_assumptions();
  auto tm                = bitwuzla->d_tm;
  for (auto &term : unsat_assumptions)
  {
    res.push_back(tm->export_term(term));
  }
  *size = res.size();
  BITWUZLA_C_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

const BitwuzlaTerm *
bitwuzla_get_unsat_core(Bitwuzla *bitwuzla, size_t *size)
{
  static thread_local std::vector<BitwuzlaTerm> res;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(size);
  res.clear();
  auto unsat_core = bitwuzla->d_bitwuzla->get_unsat_core();
  auto tm         = bitwuzla->d_tm;
  for (auto &term : unsat_core)
  {
    res.push_back(tm->export_term(term));
  }
  *size = res.size();
  BITWUZLA_C_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

void
bitwuzla_simplify(Bitwuzla *bitwuzla)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  bitwuzla->d_bitwuzla->simplify();
  BITWUZLA_C_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_simplify_term(Bitwuzla *bitwuzla, BitwuzlaTerm term)
{
  BitwuzlaTerm res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_TERM(term);
  res = bitwuzla->d_tm->export_term(
      bitwuzla->d_bitwuzla->simplify(BitwuzlaTermManager::import_term(term)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaResult
bitwuzla_check_sat(Bitwuzla *bitwuzla)
{
  BitwuzlaResult res = BITWUZLA_UNKNOWN;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  res = static_cast<BitwuzlaResult>(bitwuzla->d_bitwuzla->check_sat());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaResult
bitwuzla_check_sat_assuming(Bitwuzla *bitwuzla,
                            uint32_t argc,
                            BitwuzlaTerm args[])
{
  BitwuzlaResult res = BITWUZLA_UNKNOWN;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(args);
  std::vector<bitwuzla::Term> assumptions;
  for (uint32_t i = 0; i < argc; ++i)
  {
    assumptions.push_back(BitwuzlaTermManager::import_term(args[i]));
  }
  res =
      static_cast<BitwuzlaResult>(bitwuzla->d_bitwuzla->check_sat(assumptions));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_get_value(Bitwuzla *bitwuzla, BitwuzlaTerm term)
{
  BitwuzlaTerm res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_TERM(term);
  res = bitwuzla->d_tm->export_term(
      bitwuzla->d_bitwuzla->get_value(BitwuzlaTermManager::import_term(term)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

void
bitwuzla_print_formula(Bitwuzla *bitwuzla,
                       const char *format,
                       FILE *file,
                       uint8_t base)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(format);
  BITWUZLA_CHECK_NOT_NULL(file);
  std::stringstream ss;
  ss << bitwuzla::set_bv_format(base);
  bitwuzla->d_bitwuzla->print_formula(ss, format);
  fprintf(file, "%s", ss.str().c_str());
  BITWUZLA_C_TRY_CATCH_END;
}

void
bitwuzla_print_unsat_core(Bitwuzla *bitwuzla,
                          const char *format,
                          FILE *file,
                          uint8_t base)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(format);
  BITWUZLA_CHECK_NOT_NULL(file);
  std::stringstream ss;
  ss << bitwuzla::set_bv_format(base);
  bitwuzla->d_bitwuzla->print_unsat_core(ss, format);
  fprintf(file, "%s", ss.str().c_str());
  BITWUZLA_C_TRY_CATCH_END;
}

void
bitwuzla_get_statistics(Bitwuzla *bitwuzla,
                        const char ***keys,
                        const char ***values,
                        size_t *size)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(keys);
  BITWUZLA_CHECK_NOT_NULL(values);
  BITWUZLA_CHECK_NOT_NULL(size);
  static thread_local std::vector<const char *> rkeys;
  static thread_local std::vector<const char *> rvalues;
  static thread_local std::map<std::string, std::string> stats;
  rkeys.clear();
  rvalues.clear();
  stats.clear();
  stats = bitwuzla->d_bitwuzla->statistics();
  for (auto &[key, value] : stats)
  {
    rkeys.push_back(key.c_str());
    rvalues.push_back(value.c_str());
  }
  *keys   = rkeys.data();
  *values = rvalues.data();
  *size   = rkeys.size();
  BITWUZLA_C_TRY_CATCH_END;
}

BitwuzlaTermManager *
bitwuzla_get_term_mgr(Bitwuzla *bitwuzla)
{
  return bitwuzla->d_tm;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTermManager                                                        */
/* -------------------------------------------------------------------------- */

BitwuzlaTermManager *
bitwuzla_term_manager_new()
{
  BitwuzlaTermManager *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  res = new BitwuzlaTermManager();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

void
bitwuzla_term_manager_delete(BitwuzlaTermManager *tm)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  delete tm;
  BITWUZLA_C_TRY_CATCH_END;
}

void
bitwuzla_term_manager_release(BitwuzlaTermManager *tm)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  tm->release();
  BITWUZLA_C_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_mk_array_sort(BitwuzlaTermManager *tm,
                       BitwuzlaSort index,
                       BitwuzlaSort element)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(index);
  BITWUZLA_CHECK_SORT(element);
  res = tm->export_sort(
      tm->d_tm.mk_array_sort(BitwuzlaTermManager::import_sort(index),
                             BitwuzlaTermManager::import_sort(element)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_mk_bool_sort(BitwuzlaTermManager *tm)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.mk_bool_sort());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_mk_bv_sort(BitwuzlaTermManager *tm, uint64_t size)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.mk_bv_sort(size));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_mk_fp_sort(BitwuzlaTermManager *tm,
                    uint64_t exp_size,
                    uint64_t sig_size)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.mk_fp_sort(exp_size, sig_size));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_mk_fun_sort(BitwuzlaTermManager *tm,
                     uint64_t arity,
                     BitwuzlaSort domain[],
                     BitwuzlaSort codomain)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_NOT_NULL(domain);
  std::vector<bitwuzla::Sort> dom;
  for (uint64_t i = 0; i < arity; ++i)
  {
    BITWUZLA_CHECK_SORT_AT_IDX(domain, i);
    dom.push_back(BitwuzlaTermManager::import_sort(domain[i]));
  }
  BITWUZLA_CHECK_SORT(codomain);
  res = tm->export_sort(
      tm->d_tm.mk_fun_sort(dom, BitwuzlaTermManager::import_sort(codomain)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_mk_rm_sort(BitwuzlaTermManager *tm)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  res = tm->export_sort(tm->d_tm.mk_rm_sort());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_mk_uninterpreted_sort(BitwuzlaTermManager *tm, const char *symbol)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  if (symbol)
  {
    res = tm->export_sort(tm->d_tm.mk_uninterpreted_sort(std::string(symbol)));
  }
  else
  {
    res = tm->export_sort(tm->d_tm.mk_uninterpreted_sort());
  }
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_true(BitwuzlaTermManager *tm)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mk_true());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_false(BitwuzlaTermManager *tm)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  res = tm->export_term(tm->d_tm.mk_false());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_bv_zero(BitwuzlaTermManager *tm, BitwuzlaSort sort)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mk_bv_zero(BitwuzlaTermManager::import_sort(sort)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_bv_one(BitwuzlaTermManager *tm, BitwuzlaSort sort)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mk_bv_one(BitwuzlaTermManager::import_sort(sort)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_bv_ones(BitwuzlaTermManager *tm, BitwuzlaSort sort)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mk_bv_ones(BitwuzlaTermManager::import_sort(sort)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_bv_min_signed(BitwuzlaTermManager *tm, BitwuzlaSort sort)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mk_bv_min_signed(BitwuzlaTermManager::import_sort(sort)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_bv_max_signed(BitwuzlaTermManager *tm, BitwuzlaSort sort)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mk_bv_max_signed(BitwuzlaTermManager::import_sort(sort)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_fp_pos_zero(BitwuzlaTermManager *tm, BitwuzlaSort sort)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mk_fp_pos_zero(BitwuzlaTermManager::import_sort(sort)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_fp_neg_zero(BitwuzlaTermManager *tm, BitwuzlaSort sort)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mk_fp_neg_zero(BitwuzlaTermManager::import_sort(sort)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_fp_pos_inf(BitwuzlaTermManager *tm, BitwuzlaSort sort)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mk_fp_pos_inf(BitwuzlaTermManager::import_sort(sort)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_fp_neg_inf(BitwuzlaTermManager *tm, BitwuzlaSort sort)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mk_fp_neg_inf(BitwuzlaTermManager::import_sort(sort)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_fp_nan(BitwuzlaTermManager *tm, BitwuzlaSort sort)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(
      tm->d_tm.mk_fp_nan(BitwuzlaTermManager::import_sort(sort)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_bv_value(BitwuzlaTermManager *tm,
                     BitwuzlaSort sort,
                     const char *value,
                     uint8_t base)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  BITWUZLA_CHECK_NOT_NULL(value);
  res = tm->export_term(tm->d_tm.mk_bv_value(
      BitwuzlaTermManager::import_sort(sort), value, base));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_bv_value_uint64(BitwuzlaTermManager *tm,
                            BitwuzlaSort sort,
                            uint64_t value)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(tm->d_tm.mk_bv_value_uint64(
      BitwuzlaTermManager::import_sort(sort), value));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_bv_value_int64(BitwuzlaTermManager *tm,
                           BitwuzlaSort sort,
                           int64_t value)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  res = tm->export_term(tm->d_tm.mk_bv_value_int64(
      BitwuzlaTermManager::import_sort(sort), value));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_fp_value(BitwuzlaTermManager *tm,
                     BitwuzlaTerm bv_sign,
                     BitwuzlaTerm bv_exponent,
                     BitwuzlaTerm bv_significand)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_TERM(bv_sign);
  BITWUZLA_CHECK_TERM(bv_exponent);
  BITWUZLA_CHECK_TERM(bv_significand);
  res = tm->export_term(
      tm->d_tm.mk_fp_value(BitwuzlaTermManager::import_term(bv_sign),
                           BitwuzlaTermManager::import_term(bv_exponent),
                           BitwuzlaTermManager::import_term(bv_significand)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_fp_from_real(BitwuzlaTermManager *tm,
                         BitwuzlaSort sort,
                         BitwuzlaTerm rm,
                         const char *real)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  BITWUZLA_CHECK_TERM(rm);
  BITWUZLA_CHECK_NOT_NULL(real);
  res = tm->export_term(
      tm->d_tm.mk_fp_value(BitwuzlaTermManager::import_sort(sort),
                           BitwuzlaTermManager::import_term(rm),
                           real));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_fp_from_rational(BitwuzlaTermManager *tm,
                             BitwuzlaSort sort,
                             BitwuzlaTerm rm,
                             const char *num,
                             const char *den)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  BITWUZLA_CHECK_TERM(rm);
  BITWUZLA_CHECK_NOT_NULL(num);
  BITWUZLA_CHECK_NOT_NULL(den);
  res = tm->export_term(
      tm->d_tm.mk_fp_value(BitwuzlaTermManager::import_sort(sort),
                           BitwuzlaTermManager::import_term(rm),
                           num,
                           den));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_rm_value(BitwuzlaTermManager *tm, BitwuzlaRoundingMode rm)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_RM(rm);
  res = tm->export_term(
      tm->d_tm.mk_rm_value(static_cast<bitwuzla::RoundingMode>(rm)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_term1(BitwuzlaTermManager *tm, BitwuzlaKind kind, BitwuzlaTerm arg)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM(arg);
  res = tm->export_term(tm->d_tm.mk_term(
      import_kind(kind), {BitwuzlaTermManager::import_term(arg)}));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_term2(BitwuzlaTermManager *tm,
                  BitwuzlaKind kind,
                  BitwuzlaTerm arg0,
                  BitwuzlaTerm arg1)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM(arg0);
  BITWUZLA_CHECK_TERM(arg1);
  res = tm->export_term(
      tm->d_tm.mk_term(import_kind(kind),
                       {BitwuzlaTermManager::import_term(arg0),
                        BitwuzlaTermManager::import_term(arg1)}));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_term3(BitwuzlaTermManager *tm,
                  BitwuzlaKind kind,
                  BitwuzlaTerm arg0,
                  BitwuzlaTerm arg1,
                  BitwuzlaTerm arg2)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM(arg0);
  BITWUZLA_CHECK_TERM(arg1);
  BITWUZLA_CHECK_TERM(arg2);
  res = tm->export_term(
      tm->d_tm.mk_term(import_kind(kind),
                       {BitwuzlaTermManager::import_term(arg0),
                        BitwuzlaTermManager::import_term(arg1),
                        BitwuzlaTermManager::import_term(arg2)}));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_term(BitwuzlaTermManager *tm,
                 BitwuzlaKind kind,
                 uint32_t argc,
                 BitwuzlaTerm args[])
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_KIND(kind);
  std::vector<bitwuzla::Term> terms;
  for (uint32_t i = 0; i < argc; ++i)
  {
    BITWUZLA_CHECK_TERM_AT_IDX(args, i);
    terms.push_back(BitwuzlaTermManager::import_term(args[i]));
  }
  res = tm->export_term(tm->d_tm.mk_term(import_kind(kind), terms));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_term1_indexed1(BitwuzlaTermManager *tm,
                           BitwuzlaKind kind,
                           BitwuzlaTerm arg,
                           uint64_t idx)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM(arg);
  res = tm->export_term(tm->d_tm.mk_term(
      import_kind(kind), {BitwuzlaTermManager::import_term(arg)}, {idx}));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_term1_indexed2(BitwuzlaTermManager *tm,
                           BitwuzlaKind kind,
                           BitwuzlaTerm arg,
                           uint64_t idx0,
                           uint64_t idx1)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM(arg);
  res =
      tm->export_term(tm->d_tm.mk_term(import_kind(kind),
                                       {BitwuzlaTermManager::import_term(arg)},
                                       {idx0, idx1}));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_term2_indexed1(BitwuzlaTermManager *tm,
                           BitwuzlaKind kind,
                           BitwuzlaTerm arg0,
                           BitwuzlaTerm arg1,
                           uint64_t idx)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM(arg0);
  BITWUZLA_CHECK_TERM(arg1);
  res =
      tm->export_term(tm->d_tm.mk_term(import_kind(kind),
                                       {BitwuzlaTermManager::import_term(arg0),
                                        BitwuzlaTermManager::import_term(arg1)},
                                       {idx}));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_term2_indexed2(BitwuzlaTermManager *tm,
                           BitwuzlaKind kind,
                           BitwuzlaTerm arg0,
                           BitwuzlaTerm arg1,
                           uint64_t idx0,
                           uint64_t idx1)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM(arg0);
  BITWUZLA_CHECK_TERM(arg1);
  res =
      tm->export_term(tm->d_tm.mk_term(import_kind(kind),
                                       {BitwuzlaTermManager::import_term(arg0),
                                        BitwuzlaTermManager::import_term(arg1)},
                                       {idx0, idx1}));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_term_indexed(BitwuzlaTermManager *tm,
                         BitwuzlaKind kind,
                         uint32_t argc,
                         BitwuzlaTerm args[],
                         uint32_t idxc,
                         const uint64_t idxs[])
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_KIND(kind);
  std::vector<bitwuzla::Term> terms;
  for (uint32_t i = 0; i < argc; ++i)
  {
    BITWUZLA_CHECK_TERM_AT_IDX(args, i);
    terms.push_back(BitwuzlaTermManager::import_term(args[i]));
  }
  std::vector<uint64_t> indices;
  for (uint32_t i = 0; i < idxc; ++i)
  {
    indices.push_back(idxs[i]);
  }
  res = tm->export_term(tm->d_tm.mk_term(import_kind(kind), terms, indices));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_const(BitwuzlaTermManager *tm,
                  BitwuzlaSort sort,
                  const char *symbol)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  if (symbol)
  {
    res = tm->export_term(
        tm->d_tm.mk_const(BitwuzlaTermManager::import_sort(sort), symbol));
  }
  else
  {
    res = tm->export_term(
        tm->d_tm.mk_const(BitwuzlaTermManager::import_sort(sort)));
  }
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_const_array(BitwuzlaTermManager *tm,
                        BitwuzlaSort sort,
                        BitwuzlaTerm value)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  BITWUZLA_CHECK_TERM(value);
  res = tm->export_term(
      tm->d_tm.mk_const_array(BitwuzlaTermManager::import_sort(sort),
                              BitwuzlaTermManager::import_term(value)));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_mk_var(BitwuzlaTermManager *tm, BitwuzlaSort sort, const char *symbol)
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(tm);
  BITWUZLA_CHECK_SORT(sort);
  if (symbol)
  {
    res = tm->export_term(
        tm->d_tm.mk_var(BitwuzlaTermManager::import_sort(sort), symbol));
  }
  else
  {
    res = tm->export_term(
        tm->d_tm.mk_var(BitwuzlaTermManager::import_sort(sort)));
  }
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm
bitwuzla_substitute_term(BitwuzlaTerm term,
                         size_t map_size,
                         BitwuzlaTerm map_keys[],
                         BitwuzlaTerm map_values[])
{
  BitwuzlaTerm res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  BITWUZLA_CHECK_NOT_ZERO(map_size);
  BITWUZLA_CHECK_NOT_NULL(map_keys);
  BITWUZLA_CHECK_NOT_NULL(map_values);
  auto tm = term->d_tm;
  std::unordered_map<bitwuzla::Term, bitwuzla::Term> map;
  for (size_t i = 0; i < map_size; ++i)
  {
    BITWUZLA_CHECK_TERM_AT_IDX(map_keys, i);
    BITWUZLA_CHECK_TERM_AT_IDX(map_values, i);
    map.emplace(BitwuzlaTermManager::import_term(map_keys[i]),
                BitwuzlaTermManager::import_term(map_values[i]));
  }
  res = tm->export_term(
      tm->d_tm.substitute_term(BitwuzlaTermManager::import_term(term), map));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

void
bitwuzla_substitute_terms(size_t terms_size,
                          BitwuzlaTerm terms[],
                          size_t map_size,
                          BitwuzlaTerm map_keys[],
                          BitwuzlaTerm map_values[])
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(terms);
  BITWUZLA_CHECK_NOT_ZERO(terms_size);
  BITWUZLA_CHECK_NOT_NULL(terms);
  BITWUZLA_CHECK_NOT_ZERO(map_size);
  BITWUZLA_CHECK_NOT_NULL(map_keys);
  BITWUZLA_CHECK_NOT_NULL(map_values);
  auto tm = terms[0]->d_tm;
  std::vector<bitwuzla::Term> ts;
  for (size_t i = 0; i < terms_size; ++i)
  {
    ts.push_back(BitwuzlaTermManager::import_term(terms[i]));
  }
  std::unordered_map<bitwuzla::Term, bitwuzla::Term> map;
  for (size_t i = 0; i < map_size; ++i)
  {
    map.emplace(BitwuzlaTermManager::import_term(map_keys[i]),
                BitwuzlaTermManager::import_term(map_values[i]));
  }
  tm->d_tm.substitute_terms(ts, map);
  assert(ts.size() == terms_size);
  for (size_t i = 0; i < terms_size; ++i)
  {
    terms[i] = tm->export_term(ts[i]);
  }
  BITWUZLA_C_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_term_copy(BitwuzlaTerm term)
{
  return term->d_tm->copy(term);
}

void
bitwuzla_term_release(BitwuzlaTerm term)
{
  term->d_tm->release(term);
}

BitwuzlaSort
bitwuzla_sort_copy(BitwuzlaSort sort)
{
  return sort->d_tm->copy(sort);
}

void
bitwuzla_sort_release(BitwuzlaSort sort)
{
  sort->d_tm->release(sort);
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

size_t
bitwuzla_sort_hash(BitwuzlaSort sort)
{
  size_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = std::hash<bitwuzla::Sort>{}(BitwuzlaTermManager::import_sort(sort));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

uint64_t
bitwuzla_sort_bv_get_size(BitwuzlaSort sort)
{
  uint64_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).bv_size();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

uint64_t
bitwuzla_sort_fp_get_exp_size(BitwuzlaSort sort)
{
  uint64_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).fp_exp_size();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

uint64_t
bitwuzla_sort_fp_get_sig_size(BitwuzlaSort sort)
{
  uint64_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).fp_sig_size();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_sort_array_get_index(BitwuzlaSort sort)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(
      BitwuzlaTermManager::import_sort(sort).array_index());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_sort_array_get_element(BitwuzlaSort sort)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(
      BitwuzlaTermManager::import_sort(sort).array_element());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort *
bitwuzla_sort_fun_get_domain_sorts(BitwuzlaSort sort, size_t *size)
{
  static thread_local std::vector<BitwuzlaSort> res;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  BITWUZLA_CHECK_NOT_NULL(size);
  res.clear();
  auto sorts = BitwuzlaTermManager::import_sort(sort).fun_domain();
  assert(sorts.size() == BitwuzlaTermManager::import_sort(sort).fun_arity());
  res.clear();
  auto tm = sort->d_tm;
  for (auto &sort : sorts)
  {
    res.push_back(tm->export_sort(sort));
  }
  *size = res.size();
  BITWUZLA_C_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

BitwuzlaSort
bitwuzla_sort_fun_get_codomain(BitwuzlaSort sort)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = sort->d_tm->export_sort(
      BitwuzlaTermManager::import_sort(sort).fun_codomain());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

uint64_t
bitwuzla_sort_fun_get_arity(BitwuzlaSort sort)
{
  uint64_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).fun_arity();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

const char *
bitwuzla_sort_get_uninterpreted_symbol(BitwuzlaSort sort)
{
  const char *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  static thread_local std::string str;
  const std::optional<std::string> s =
      BitwuzlaTermManager::import_sort(sort).uninterpreted_symbol();
  if (s)
  {
    str = *s;
    res = str.c_str();
  }
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_sort_is_array(BitwuzlaSort sort)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).is_array();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_sort_is_bool(BitwuzlaSort sort)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).is_bool();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_sort_is_bv(BitwuzlaSort sort)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).is_bv();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_sort_is_fp(BitwuzlaSort sort)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).is_fp();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_sort_is_fun(BitwuzlaSort sort)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).is_fun();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_sort_is_rm(BitwuzlaSort sort)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).is_rm();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_sort_is_uninterpreted(BitwuzlaSort sort)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  res = BitwuzlaTermManager::import_sort(sort).is_uninterpreted();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

void
bitwuzla_sort_print(BitwuzlaSort sort, FILE *file)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT(sort);
  BITWUZLA_CHECK_NOT_NULL(file);
  std::stringstream ss;
  ss << BitwuzlaTermManager::import_sort(sort);
  fprintf(file, "%s", ss.str().c_str());
  BITWUZLA_C_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

size_t
bitwuzla_term_hash(BitwuzlaTerm term)
{
  size_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = std::hash<bitwuzla::Term>{}(BitwuzlaTermManager::import_term(term));
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaKind
bitwuzla_term_get_kind(BitwuzlaTerm term)
{
  BitwuzlaKind res = BITWUZLA_KIND_NUM_KINDS;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = export_kind(BitwuzlaTermManager::import_term(term).kind());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaTerm *
bitwuzla_term_get_children(BitwuzlaTerm term, size_t *size)
{
  static thread_local std::vector<BitwuzlaTerm> res;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  BITWUZLA_CHECK_NOT_NULL(size);
  res.clear();
  auto tm       = term->d_tm;
  auto children = BitwuzlaTermManager::import_term(term).children();
  for (auto &child : children)
  {
    res.push_back(tm->export_term(child));
  }
  *size = res.size();
  BITWUZLA_C_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

uint64_t *
bitwuzla_term_get_indices(BitwuzlaTerm term, size_t *size)
{
  static thread_local std::vector<uint64_t> res;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  BITWUZLA_CHECK_NOT_NULL(size);
  res   = BitwuzlaTermManager::import_term(term).indices();
  *size = res.size();
  BITWUZLA_C_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

bool
bitwuzla_term_is_indexed(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).num_indices() > 0;
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_term_get_sort(BitwuzlaTerm term)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = term->d_tm->export_sort(BitwuzlaTermManager::import_term(term).sort());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_term_array_get_index_sort(BitwuzlaTerm term)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = term->d_tm->export_sort(
      BitwuzlaTermManager::import_term(term).sort().array_index());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort
bitwuzla_term_array_get_element_sort(BitwuzlaTerm term)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = term->d_tm->export_sort(
      BitwuzlaTermManager::import_term(term).sort().array_element());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

BitwuzlaSort *
bitwuzla_term_fun_get_domain_sorts(BitwuzlaTerm term, size_t *size)
{
  static thread_local std::vector<BitwuzlaSort> res;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  BITWUZLA_CHECK_NOT_NULL(size);
  res.clear();
  auto tm    = term->d_tm;
  auto sorts = BitwuzlaTermManager::import_term(term).sort().fun_domain();
  for (auto &sort : sorts)
  {
    res.push_back(tm->export_sort(sort));
  }
  *size = res.size();
  BITWUZLA_C_TRY_CATCH_END;
  return *size > 0 ? res.data() : nullptr;
}

BitwuzlaSort
bitwuzla_term_fun_get_codomain_sort(BitwuzlaTerm term)
{
  BitwuzlaSort res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = term->d_tm->export_sort(
      BitwuzlaTermManager::import_term(term).sort().fun_codomain());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

uint64_t
bitwuzla_term_bv_get_size(BitwuzlaTerm term)
{
  uint64_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().bv_size();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

uint64_t
bitwuzla_term_fp_get_exp_size(BitwuzlaTerm term)
{
  uint64_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().fp_exp_size();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

uint64_t
bitwuzla_term_fp_get_sig_size(BitwuzlaTerm term)
{
  uint64_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().fp_sig_size();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

uint64_t
bitwuzla_term_fun_get_arity(BitwuzlaTerm term)
{
  uint64_t res = 0;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().fun_arity();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

const char *
bitwuzla_term_get_symbol(BitwuzlaTerm term)
{
  const char *res = nullptr;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  static thread_local std::string str;
  auto symbol = BitwuzlaTermManager::import_term(term).symbol();
  if (symbol)
  {
    str = symbol->get();
    res = str.c_str();
  }
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_equal_sort(BitwuzlaTerm term0, BitwuzlaTerm term1)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term0);
  BITWUZLA_CHECK_TERM(term1);
  res = BitwuzlaTermManager::import_term(term0).sort()
        == BitwuzlaTermManager::import_term(term1).sort();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_array(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().is_array();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_const(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_const();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_fun(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().is_fun();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_var(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_variable();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_value(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_value();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_bv_value(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  const bitwuzla::Term &t = BitwuzlaTermManager::import_term(term);
  res                     = t.is_value() && t.sort().is_bv();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_fp_value(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  const bitwuzla::Term &t = BitwuzlaTermManager::import_term(term);
  res                     = t.is_value() && t.sort().is_fp();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_rm_value(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  const bitwuzla::Term &t = BitwuzlaTermManager::import_term(term);
  res                     = t.is_value() && t.sort().is_rm();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_bool(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().is_bool();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_bv(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().is_bv();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_fp(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().is_fp();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_rm(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().is_rm();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_uninterpreted(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).sort().is_uninterpreted();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_true(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_true();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_false(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_false();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_bv_value_zero(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_bv_value_zero();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_bv_value_one(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_bv_value_one();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_bv_value_ones(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_bv_value_ones();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_bv_value_min_signed(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_bv_value_min_signed();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_bv_value_max_signed(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_bv_value_max_signed();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_fp_value_pos_zero(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_fp_value_pos_zero();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_fp_value_neg_zero(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_fp_value_neg_zero();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_fp_value_pos_inf(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_fp_value_pos_inf();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_fp_value_neg_inf(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_fp_value_neg_inf();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_fp_value_nan(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_fp_value_nan();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_rm_value_rna(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_rm_value_rna();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_rm_value_rne(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_rm_value_rne();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_rm_value_rtn(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_rm_value_rtn();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_rm_value_rtp(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_rm_value_rtp();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_is_rm_value_rtz(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).is_rm_value_rtz();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

bool
bitwuzla_term_value_get_bool(BitwuzlaTerm term)
{
  bool res = false;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = BitwuzlaTermManager::import_term(term).value<bool>();
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

const char *
bitwuzla_term_value_get_str(BitwuzlaTerm term)
{
  static thread_local std::string str;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  str = BitwuzlaTermManager::import_term(term).value<std::string>();
  BITWUZLA_C_TRY_CATCH_END;
  return str.c_str();
}

const char *
bitwuzla_term_value_get_str_fmt(BitwuzlaTerm term, uint8_t base)
{
  static thread_local std::string str;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  str = BitwuzlaTermManager::import_term(term).value<std::string>(base);
  BITWUZLA_C_TRY_CATCH_END;
  return str.c_str();
}

void
bitwuzla_term_value_get_fp_ieee(BitwuzlaTerm term,
                                const char **sign,
                                const char **exponent,
                                const char **significand,
                                uint8_t base)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  static thread_local std::string _sign, _exp, _sig;
  std::tie(_sign, _exp, _sig) =
      BitwuzlaTermManager::import_term(term)
          .value<std::tuple<std::string, std::string, std::string>>(base);
  *sign        = _sign.c_str();
  *exponent    = _exp.c_str();
  *significand = _sig.c_str();
  BITWUZLA_C_TRY_CATCH_END;
}

BitwuzlaRoundingMode
bitwuzla_term_value_get_rm(BitwuzlaTerm term)
{
  BitwuzlaRoundingMode res = BITWUZLA_RM_RNA;
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  res = static_cast<BitwuzlaRoundingMode>(
      BitwuzlaTermManager::import_term(term).value<bitwuzla::RoundingMode>());
  BITWUZLA_C_TRY_CATCH_END;
  return res;
}

void
bitwuzla_term_print(BitwuzlaTerm term, FILE *file)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  BITWUZLA_CHECK_NOT_NULL(file);
  std::stringstream ss;
  ss << BitwuzlaTermManager::import_term(term);
  fprintf(file, "%s", ss.str().c_str());
  BITWUZLA_C_TRY_CATCH_END;
}

void
bitwuzla_term_print_fmt(BitwuzlaTerm term, FILE *file, uint8_t base)
{
  BITWUZLA_C_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM(term);
  BITWUZLA_CHECK_NOT_NULL(file);
  std::stringstream ss;
  ss << bitwuzla::set_bv_format(base);
  ss << BitwuzlaTermManager::import_term(term);
  fprintf(file, "%s", ss.str().c_str());
  BITWUZLA_C_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
