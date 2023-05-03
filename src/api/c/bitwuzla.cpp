/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
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

// Note: Definition of class CTerminator and structs BitwuzlaOptions and
//       Bitwuzla is in api/c/bitwuzla_structs.h

/* -------------------------------------------------------------------------- */

#define BZLA_IMPORT_BITWUZLA_OPTION(option) (bzla_options.at(option))
#define BZLA_EXPORT_BITWUZLA_OPTION(option) (bitwuzla_options.at(option))

/* -------------------------------------------------------------------------- */

namespace {
BitwuzlaSort
export_sort(const bitwuzla::Sort &sort)
{
  assert(!sort.is_null());

  BitwuzlaSort sort_id        = sort.id();
  Bitwuzla::SortMap &sort_map = Bitwuzla::sort_map();
  const auto it               = sort_map.find(sort_id);
  if (it == sort_map.end())
  {
    sort_map.emplace(sort_id,
                     std::make_pair(std::make_unique<bitwuzla::Sort>(sort), 1));
  }
  else
  {
    it->second.second += 1;
  }
  return sort_id;
}

const bitwuzla::Sort &
import_sort(BitwuzlaSort sort_id)
{
  return *Bitwuzla::sort_map().at(sort_id).first;
}

BitwuzlaTerm
export_term(const bitwuzla::Term &term)
{
  assert(!term.is_null());

  BitwuzlaTerm term_id        = term.id();
  Bitwuzla::TermMap &term_map = Bitwuzla::term_map();
  const auto it               = term_map.find(term_id);
  if (it == term_map.end())
  {
    term_map.emplace(term_id,
                     std::make_pair(std::make_unique<bitwuzla::Term>(term), 1));
  }
  else
  {
    it->second.second += 1;
  }
  return term_id;
}

const bitwuzla::Term &
import_term(BitwuzlaSort term_id)
{
  return *Bitwuzla::term_map().at(term_id).first;
}

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
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  static thread_local std::string str;
  str = "BITWUZLA_KIND_" + std::to_string(static_cast<bitwuzla::Kind>(kind));
  return str.c_str();
  BITWUZLA_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaRoundingMode                                                       */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_rm_to_string(BitwuzlaRoundingMode rm)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_RM(rm);
  static thread_local std::string str;
  str =
      "BITWUZLA_RM_" + std::to_string(static_cast<bitwuzla::RoundingMode>(rm));
  return str.c_str();
  BITWUZLA_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaResult                                                             */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_result_to_string(BitwuzlaResult result)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_RESULT(result);
  static thread_local std::string str;
  str = std::to_string(static_cast<bitwuzla::Result>(result));
  return str.c_str();
  BITWUZLA_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_term_to_string(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  static thread_local std::string str;
  str = import_term(term).str();
  return str.c_str();
  BITWUZLA_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_sort_to_string(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  static thread_local std::string str;
  str = import_sort(sort).str();
  return str.c_str();
  BITWUZLA_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaOptions                                                            */
/* -------------------------------------------------------------------------- */

BitwuzlaOptions *
bitwuzla_options_new()
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return new BitwuzlaOptions();
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_options_delete(BitwuzlaOptions *options)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  delete options;
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_option_is_numeric(BitwuzlaOptions *options, BitwuzlaOption option)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  return options->d_options.is_numeric(static_cast<bitwuzla::Option>(option));
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_option_is_mode(BitwuzlaOptions *options, BitwuzlaOption option)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  return options->d_options.is_mode(static_cast<bitwuzla::Option>(option));
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_set_option(BitwuzlaOptions *options,
                    BitwuzlaOption option,
                    uint64_t value)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  options->d_options.set(import_option(option), value);
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_set_option_mode(BitwuzlaOptions *options,
                         BitwuzlaOption option,
                         const char *value)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  BITWUZLA_CHECK_NOT_NULL(value);
  options->d_options.set(import_option(option), value);
  BITWUZLA_TRY_CATCH_END;
}

uint64_t
bitwuzla_get_option(BitwuzlaOptions *options, BitwuzlaOption option)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  return options->d_options.get(import_option(option));
  BITWUZLA_TRY_CATCH_END;
}

const char *
bitwuzla_get_option_mode(BitwuzlaOptions *options, BitwuzlaOption option)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  return options->d_options.get_mode(import_option(option)).c_str();
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_get_option_info(BitwuzlaOptions *options,
                         BitwuzlaOption option,
                         BitwuzlaOptionInfo *info)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(options);
  BITWUZLA_CHECK_OPTION(option);
  BITWUZLA_CHECK_NOT_NULL(info);

  static thread_local bitwuzla::OptionInfo cpp_info;
  cpp_info = bitwuzla::OptionInfo(options->d_options, import_option(option));

  std::memset(info, 0, sizeof(*info));
  info->opt        = option;
  info->shrt       = cpp_info.shrt;
  info->lng        = cpp_info.lng;
  info->desc       = cpp_info.description;
  info->is_numeric = cpp_info.kind != bitwuzla::OptionInfo::Kind::MODE;

  if (info->is_numeric)
  {
    if (cpp_info.kind == bitwuzla::OptionInfo::Kind::BOOL)
    {
      info->numeric.cur =
          std::get<bitwuzla::OptionInfo::Bool>(cpp_info.values).cur;
      info->numeric.dflt =
          std::get<bitwuzla::OptionInfo::Bool>(cpp_info.values).dflt;
      info->numeric.min = 0;
      info->numeric.max = 1;
    }
    else
    {
      info->numeric.cur =
          std::get<bitwuzla::OptionInfo::Numeric>(cpp_info.values).cur;
      info->numeric.dflt =
          std::get<bitwuzla::OptionInfo::Numeric>(cpp_info.values).dflt;
      info->numeric.min =
          std::get<bitwuzla::OptionInfo::Numeric>(cpp_info.values).min;
      info->numeric.max =
          std::get<bitwuzla::OptionInfo::Numeric>(cpp_info.values).max;
    }
  }
  else
  {
    info->mode.cur =
        std::get<bitwuzla::OptionInfo::Mode>(cpp_info.values).cur.c_str();
    info->mode.num_modes =
        std::get<bitwuzla::OptionInfo::Mode>(cpp_info.values).modes.size();
    static thread_local std::vector<const char *> c_modes;
    for (const auto &m :
         std::get<bitwuzla::OptionInfo::Mode>(cpp_info.values).modes)
    {
      c_modes.push_back(m.c_str());
    }
  }
  BITWUZLA_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* Library info                                                               */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_copyright()
{
  BITWUZLA_TRY_CATCH_BEGIN;
  static thread_local std::string str = bitwuzla::copyright();
  return str.c_str();
  BITWUZLA_TRY_CATCH_END;
}

const char *
bitwuzla_version()
{
  BITWUZLA_TRY_CATCH_BEGIN;
  static thread_local std::string str = bitwuzla::version();
  return str.c_str();
  BITWUZLA_TRY_CATCH_END;
}

const char *
bitwuzla_git_id()
{
  BITWUZLA_TRY_CATCH_BEGIN;
  static thread_local std::string str = bitwuzla::git_id();
  return str.c_str();
  BITWUZLA_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

Bitwuzla *
bitwuzla_new(const BitwuzlaOptions *options)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return new Bitwuzla(options);
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_delete(Bitwuzla *bitwuzla)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  delete bitwuzla;
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_set_termination_callback(Bitwuzla *bitwuzla,
                                  int32_t (*fun)(void *),
                                  void *state)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(fun);
  bitwuzla->d_terminator.reset(new CTerminator(fun, state));
  bitwuzla->d_bitwuzla->configure_terminator(bitwuzla->d_terminator.get());
  BITWUZLA_TRY_CATCH_END;
}

void *
bitwuzla_get_termination_callback_state(Bitwuzla *bitwuzla)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  return bitwuzla->d_terminator ? bitwuzla->d_terminator->get_state() : nullptr;
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_set_abort_callback(void (*fun)(const char *msg))
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(fun);
  // TODO
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_mk_array_sort(BitwuzlaSort index, BitwuzlaSort element)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(index);
  BITWUZLA_CHECK_SORT_ID(element);
  return export_sort(
      bitwuzla::mk_array_sort(import_sort(index), import_sort(element)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_mk_bool_sort()
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return export_sort(bitwuzla::mk_bool_sort());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_mk_bv_sort(uint64_t size)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return export_sort(bitwuzla::mk_bv_sort(size));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_mk_fp_sort(uint64_t exp_size, uint64_t sig_size)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return export_sort(bitwuzla::mk_fp_sort(exp_size, sig_size));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_mk_fun_sort(uint64_t arity,
                     BitwuzlaSort domain[],
                     BitwuzlaSort codomain)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(domain);
  std::vector<bitwuzla::Sort> dom;
  for (uint64_t i = 0; i < arity; ++i)
  {
    BITWUZLA_CHECK_SORT_ID_AT_IDX(domain, i);
    dom.push_back(import_sort(domain[i]));
  }
  BITWUZLA_CHECK_SORT_ID(codomain);
  return export_sort(bitwuzla::mk_fun_sort(dom, import_sort(codomain)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_mk_rm_sort()
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return export_sort(bitwuzla::mk_rm_sort());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_mk_uninterpreted_sort(const char *symbol)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  if (symbol)
  {
    return export_sort(bitwuzla::mk_uninterpreted_sort(std::string(symbol)));
  }
  return export_sort(bitwuzla::mk_uninterpreted_sort());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_true()
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return export_term(bitwuzla::mk_true());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_false()
{
  BITWUZLA_TRY_CATCH_BEGIN;
  return export_term(bitwuzla::mk_false());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_bv_zero(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_bv_zero(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_bv_one(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_bv_one(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_bv_ones(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_bv_ones(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_bv_min_signed(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_bv_min_signed(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_bv_max_signed(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_bv_max_signed(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_fp_pos_zero(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_fp_pos_zero(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_fp_neg_zero(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_fp_neg_zero(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_fp_pos_inf(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_fp_pos_inf(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_fp_neg_inf(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_fp_neg_inf(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_fp_nan(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_fp_nan(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_bv_value(BitwuzlaSort sort, const char *value, uint8_t base)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  BITWUZLA_CHECK_NOT_NULL(value);
  return export_term(bitwuzla::mk_bv_value(import_sort(sort), value, base));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_bv_value_uint64(BitwuzlaSort sort, uint64_t value)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_bv_value_uint64(import_sort(sort), value));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_bv_value_int64(BitwuzlaSort sort, int64_t value)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_term(bitwuzla::mk_bv_value_int64(import_sort(sort), value));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_fp_value(BitwuzlaTerm bv_sign,
                     BitwuzlaTerm bv_exponent,
                     BitwuzlaTerm bv_significand)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(bv_sign);
  BITWUZLA_CHECK_TERM_ID(bv_exponent);
  BITWUZLA_CHECK_TERM_ID(bv_significand);
  return export_term(bitwuzla::mk_fp_value(import_term(bv_sign),
                                           import_term(bv_exponent),
                                           import_term(bv_significand)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_fp_from_real(BitwuzlaSort sort, BitwuzlaTerm rm, const char *real)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  BITWUZLA_CHECK_TERM_ID(rm);
  BITWUZLA_CHECK_NOT_NULL(real);
  return export_term(
      bitwuzla::mk_fp_value(import_sort(sort), import_term(rm), real));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_fp_from_rational(BitwuzlaSort sort,
                             BitwuzlaTerm rm,
                             const char *num,
                             const char *den)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  BITWUZLA_CHECK_TERM_ID(rm);
  BITWUZLA_CHECK_NOT_NULL(num);
  BITWUZLA_CHECK_NOT_NULL(den);
  return export_term(
      bitwuzla::mk_fp_value(import_sort(sort), import_term(rm), num, den));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_rm_value(BitwuzlaRoundingMode rm)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_RM(rm);
  return export_term(
      bitwuzla::mk_rm_value(static_cast<bitwuzla::RoundingMode>(rm)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_term1(BitwuzlaKind kind, BitwuzlaTerm arg)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM_ID(arg);
  return export_term(bitwuzla::mk_term(import_kind(kind), {import_term(arg)}));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_term2(BitwuzlaKind kind, BitwuzlaTerm arg0, BitwuzlaTerm arg1)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM_ID(arg0);
  BITWUZLA_CHECK_TERM_ID(arg1);
  return export_term(bitwuzla::mk_term(import_kind(kind),
                                       {import_term(arg0), import_term(arg1)}));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_term3(BitwuzlaKind kind,
                  BitwuzlaTerm arg0,
                  BitwuzlaTerm arg1,
                  BitwuzlaTerm arg2)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM_ID(arg0);
  BITWUZLA_CHECK_TERM_ID(arg1);
  BITWUZLA_CHECK_TERM_ID(arg2);
  return export_term(bitwuzla::mk_term(
      import_kind(kind),
      {import_term(arg0), import_term(arg1), import_term(arg2)}));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_term(BitwuzlaKind kind, uint32_t argc, BitwuzlaTerm args[])
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  std::vector<bitwuzla::Term> terms;
  for (uint32_t i = 0; i < argc; ++i)
  {
    BITWUZLA_CHECK_TERM_ID_AT_IDX(args, i);
    terms.push_back(import_term(args[i]));
  }
  return export_term(bitwuzla::mk_term(import_kind(kind), terms));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_term1_indexed1(BitwuzlaKind kind, BitwuzlaTerm arg, uint64_t idx)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM_ID(arg);
  return export_term(
      bitwuzla::mk_term(import_kind(kind), {import_term(arg)}, {idx}));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_term1_indexed2(BitwuzlaKind kind,
                           BitwuzlaTerm arg,
                           uint64_t idx0,
                           uint64_t idx1)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM_ID(arg);
  return export_term(
      bitwuzla::mk_term(import_kind(kind), {import_term(arg)}, {idx0, idx1}));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_term2_indexed1(BitwuzlaKind kind,
                           BitwuzlaTerm arg0,
                           BitwuzlaTerm arg1,
                           uint64_t idx)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM_ID(arg0);
  BITWUZLA_CHECK_TERM_ID(arg1);
  return export_term(bitwuzla::mk_term(
      import_kind(kind), {import_term(arg0), import_term(arg1)}, {idx}));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_term2_indexed2(BitwuzlaKind kind,
                           BitwuzlaTerm arg0,
                           BitwuzlaTerm arg1,
                           uint64_t idx0,
                           uint64_t idx1)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  BITWUZLA_CHECK_TERM_ID(arg0);
  BITWUZLA_CHECK_TERM_ID(arg1);
  return export_term(bitwuzla::mk_term(
      import_kind(kind), {import_term(arg0), import_term(arg1)}, {idx0, idx1}));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_term_indexed(BitwuzlaKind kind,
                         uint32_t argc,
                         BitwuzlaTerm args[],
                         uint32_t idxc,
                         const uint64_t idxs[])
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_KIND(kind);
  std::vector<bitwuzla::Term> terms;
  for (uint32_t i = 0; i < argc; ++i)
  {
    BITWUZLA_CHECK_TERM_ID_AT_IDX(args, i);
    terms.push_back(import_term(args[i]));
  }
  std::vector<uint64_t> indices;
  for (uint32_t i = 0; i < idxc; ++i)
  {
    indices.push_back(idxs[i]);
  }
  return export_term(bitwuzla::mk_term(import_kind(kind), terms, indices));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_const(BitwuzlaSort sort, const char *symbol)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  if (symbol)
  {
    return export_term(bitwuzla::mk_const(import_sort(sort), symbol));
  }
  return export_term(bitwuzla::mk_const(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_const_array(BitwuzlaSort sort, BitwuzlaTerm value)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  BITWUZLA_CHECK_TERM_ID(value);
  return export_term(
      bitwuzla::mk_const_array(import_sort(sort), import_term(value)));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_mk_var(BitwuzlaSort sort, const char *symbol)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  if (symbol)
  {
    return export_term(bitwuzla::mk_var(import_sort(sort), symbol));
  }
  return export_term(bitwuzla::mk_var(import_sort(sort)));
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_push(Bitwuzla *bitwuzla, uint64_t nlevels)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  bitwuzla->d_bitwuzla->push(nlevels);
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_pop(Bitwuzla *bitwuzla, uint64_t nlevels)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  bitwuzla->d_bitwuzla->pop(nlevels);
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_assert(Bitwuzla *bitwuzla, BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_TERM_ID(term);
  bitwuzla->d_bitwuzla->assert_formula(import_term(term));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm *
bitwuzla_get_assertions(Bitwuzla *bitwuzla, size_t *size)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  static thread_local std::vector<BitwuzlaTerm> res;
  res.clear();
  auto assertions = bitwuzla->d_bitwuzla->get_assertions();
  for (auto &term : assertions)
  {
    res.push_back(export_term(term));
  }
  *size = res.size();
  return *size > 0 ? res.data() : nullptr;
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla, BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_TERM_ID(term);
  return bitwuzla->d_bitwuzla->is_unsat_assumption(import_term(term));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm *
bitwuzla_get_unsat_assumptions(Bitwuzla *bitwuzla, size_t *size)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(size);
  static thread_local std::vector<BitwuzlaTerm> res;
  res.clear();
  auto unsat_assumptions = bitwuzla->d_bitwuzla->get_unsat_assumptions();
  for (auto &term : unsat_assumptions)
  {
    res.push_back(export_term(term));
  }
  *size = res.size();
  return *size > 0 ? res.data() : nullptr;
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm *
bitwuzla_get_unsat_core(Bitwuzla *bitwuzla, size_t *size)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(size);
  static thread_local std::vector<BitwuzlaTerm> res;
  res.clear();
  auto unsat_core = bitwuzla->d_bitwuzla->get_unsat_core();
  for (auto &term : unsat_core)
  {
    res.push_back(export_term(term));
  }
  *size = res.size();
  return *size > 0 ? res.data() : nullptr;
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaResult
bitwuzla_simplify(Bitwuzla *bitwuzla)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  return static_cast<BitwuzlaResult>(bitwuzla->d_bitwuzla->simplify());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaResult
bitwuzla_check_sat(Bitwuzla *bitwuzla)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  return static_cast<BitwuzlaResult>(bitwuzla->d_bitwuzla->check_sat());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaResult
bitwuzla_check_sat_assuming(Bitwuzla *bitwuzla,
                            uint32_t argc,
                            BitwuzlaTerm args[])
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(args);
  std::vector<bitwuzla::Term> assumptions;
  for (uint32_t i = 0; i < argc; ++i)
  {
    assumptions.push_back(import_term(args[i]));
  }
  return static_cast<BitwuzlaResult>(
      bitwuzla->d_bitwuzla->check_sat(assumptions));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_get_value(Bitwuzla *bitwuzla, BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_TERM_ID(term);
  return export_term(bitwuzla->d_bitwuzla->get_value(import_term(term)));
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_print_formula(Bitwuzla *bitwuzla, const char *format, FILE *file)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_NULL(format);
  BITWUZLA_CHECK_NOT_NULL(file);
  std::stringstream ss;
  bitwuzla->d_bitwuzla->print_formula(ss, format);
  fprintf(file, "%s", ss.str().c_str());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm
bitwuzla_substitute_term(Bitwuzla *bitwuzla,
                         BitwuzlaTerm term,
                         size_t map_size,
                         BitwuzlaTerm map_keys[],
                         BitwuzlaTerm map_values[])
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_TERM_ID(term);
  BITWUZLA_CHECK_NOT_ZERO(map_size);
  BITWUZLA_CHECK_NOT_NULL(map_keys);
  BITWUZLA_CHECK_NOT_NULL(map_values);
  std::unordered_map<bitwuzla::Term, bitwuzla::Term> map;
  for (size_t i = 0; i < map_size; ++i)
  {
    map.emplace(import_term(map_keys[i]), import_term(map_values[i]));
  }
  return export_term(bitwuzla::substitute_term(import_term(term), map));
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_substitute_terms(Bitwuzla *bitwuzla,
                          size_t terms_size,
                          BitwuzlaTerm terms[],
                          size_t map_size,
                          BitwuzlaTerm map_keys[],
                          BitwuzlaTerm map_values[])
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_NOT_NULL(bitwuzla);
  BITWUZLA_CHECK_NOT_ZERO(terms_size);
  BITWUZLA_CHECK_NOT_NULL(terms);
  BITWUZLA_CHECK_NOT_ZERO(map_size);
  BITWUZLA_CHECK_NOT_NULL(map_keys);
  BITWUZLA_CHECK_NOT_NULL(map_values);
  std::vector<bitwuzla::Term> ts;
  for (size_t i = 0; i < terms_size; ++i)
  {
    ts.push_back(import_term(terms[i]));
  }
  std::unordered_map<bitwuzla::Term, bitwuzla::Term> map;
  for (size_t i = 0; i < map_size; ++i)
  {
    map.emplace(import_term(map_keys[i]), import_term(map_values[i]));
  }
  bitwuzla::substitute_terms(ts, map);
  assert(ts.size() == terms_size);
  for (size_t i = 0; i < terms_size; ++i)
  {
    terms[i] = export_term(ts[i]);
  }
  BITWUZLA_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

size_t
bitwuzla_sort_hash(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return std::hash<bitwuzla::Sort>{}(import_sort(sort));
  BITWUZLA_TRY_CATCH_END;
}

uint64_t
bitwuzla_sort_bv_get_size(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).bv_size();
  BITWUZLA_TRY_CATCH_END;
}

uint64_t
bitwuzla_sort_fp_get_exp_size(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).fp_exp_size();
  BITWUZLA_TRY_CATCH_END;
}

uint64_t
bitwuzla_sort_fp_get_sig_size(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).fp_sig_size();
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_sort_array_get_index(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_sort(import_sort(sort).array_index());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_sort_array_get_element(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_sort(import_sort(sort).array_element());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort *
bitwuzla_sort_fun_get_domain_sorts(BitwuzlaSort sort, size_t *size)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  BITWUZLA_CHECK_NOT_NULL(size);
  static thread_local std::vector<BitwuzlaSort> res;
  res.clear();
  auto sorts = import_sort(sort).fun_domain();
  assert(sorts.size() == import_sort(sort).fun_arity());
  res.clear();
  for (auto &sort : sorts)
  {
    res.push_back(export_sort(sort));
  }
  *size = res.size();
  return *size > 0 ? res.data() : nullptr;
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_sort_fun_get_codomain(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return export_sort(import_sort(sort).fun_codomain());
  BITWUZLA_TRY_CATCH_END;
}

uint64_t
bitwuzla_sort_fun_get_arity(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).fun_arity();
  BITWUZLA_TRY_CATCH_END;
}

const char *
bitwuzla_sort_get_uninterpreted_symbol(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  static thread_local std::string str;
  const std::optional<std::string> s = import_sort(sort).uninterpreted_symbol();
  if (s) str = *s;
  return s ? str.c_str() : nullptr;
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_sort_is_equal(BitwuzlaSort sort0, BitwuzlaSort sort1)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort0);
  BITWUZLA_CHECK_SORT_ID(sort1);
  return import_sort(sort0) == import_sort(sort1);
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_sort_is_array(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).is_array();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_sort_is_bool(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).is_bool();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_sort_is_bv(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).is_bv();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_sort_is_fp(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).is_fp();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_sort_is_fun(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).is_fun();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_sort_is_rm(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).is_rm();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_sort_is_uninterpreted(BitwuzlaSort sort)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  return import_sort(sort).is_uninterpreted();
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_sort_print(BitwuzlaSort sort, FILE *file)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_SORT_ID(sort);
  BITWUZLA_CHECK_NOT_NULL(file);
  std::stringstream ss;
  ss << import_sort(sort);
  fprintf(file, "%s", ss.str().c_str());
  BITWUZLA_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

size_t
bitwuzla_term_hash(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return std::hash<bitwuzla::Term>{}(import_term(term));
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaKind
bitwuzla_term_get_kind(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return export_kind(import_term(term).kind());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaTerm *
bitwuzla_term_get_children(BitwuzlaTerm term, size_t *size)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  BITWUZLA_CHECK_NOT_NULL(size);
  static thread_local std::vector<BitwuzlaTerm> res;
  res.clear();
  auto children = import_term(term).children();
  for (auto &child : children)
  {
    res.push_back(export_term(child));
  }
  *size = res.size();
  return *size > 0 ? res.data() : nullptr;
  BITWUZLA_TRY_CATCH_END;
}

uint64_t *
bitwuzla_term_get_indices(BitwuzlaTerm term, size_t *size)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  BITWUZLA_CHECK_NOT_NULL(size);
  static thread_local std::vector<uint64_t> res;
  res = import_term(term).indices();
  *size = res.size();
  return *size > 0 ? res.data() : nullptr;
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_indexed(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).num_indices() > 0;
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_term_get_sort(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return export_sort(import_term(term).sort());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_term_array_get_index_sort(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return export_sort(import_term(term).sort().array_index());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_term_array_get_element_sort(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return export_sort(import_term(term).sort().array_element());
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort *
bitwuzla_term_fun_get_domain_sorts(BitwuzlaTerm term, size_t *size)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  BITWUZLA_CHECK_NOT_NULL(size);
  static thread_local std::vector<BitwuzlaSort> res;
  res.clear();
  auto sorts = import_term(term).sort().fun_domain();
  for (auto &sort : sorts)
  {
    res.push_back(export_sort(sort));
  }
  *size = res.size();
  return *size > 0 ? res.data() : nullptr;
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaSort
bitwuzla_term_fun_get_codomain_sort(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return export_sort(import_term(term).sort().fun_codomain());
  BITWUZLA_TRY_CATCH_END;
}

uint64_t
bitwuzla_term_bv_get_size(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().bv_size();
  BITWUZLA_TRY_CATCH_END;
}

uint64_t
bitwuzla_term_fp_get_exp_size(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().fp_exp_size();
  BITWUZLA_TRY_CATCH_END;
}

uint64_t
bitwuzla_term_fp_get_sig_size(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().fp_sig_size();
  BITWUZLA_TRY_CATCH_END;
}

uint64_t
bitwuzla_term_fun_get_arity(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().fun_arity();
  BITWUZLA_TRY_CATCH_END;
}

const char *
bitwuzla_term_get_symbol(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  static thread_local std::string str;
  auto symbol = import_term(term).symbol();
  if (symbol)
  {
    str = symbol->get();
    return str.c_str();
  }
  return nullptr;
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_equal_sort(BitwuzlaTerm term0, BitwuzlaTerm term1)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term0);
  BITWUZLA_CHECK_TERM_ID(term1);
  return import_term(term0).sort() == import_term(term1).sort();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_array(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().is_array();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_const(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_const();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_fun(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().is_fun();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_var(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_variable();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_value(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_value();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_bv_value(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  const bitwuzla::Term &t = import_term(term);
  return t.is_value() && t.sort().is_bv();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_fp_value(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  const bitwuzla::Term &t = import_term(term);
  return t.is_value() && t.sort().is_fp();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_rm_value(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  const bitwuzla::Term &t = import_term(term);
  return t.is_value() && t.sort().is_rm();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_bool(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().is_bool();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_bv(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().is_bv();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_fp(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().is_fp();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_rm(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().is_rm();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_uninterpreted(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).sort().is_uninterpreted();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_bv_value_zero(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_bv_value_zero();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_bv_value_one(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_bv_value_one();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_bv_value_ones(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_bv_value_ones();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_bv_value_min_signed(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_bv_value_min_signed();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_bv_value_max_signed(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_bv_value_max_signed();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_fp_value_pos_zero(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_fp_value_pos_zero();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_fp_value_neg_zero(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_fp_value_neg_zero();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_fp_value_pos_inf(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_fp_value_pos_inf();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_fp_value_neg_inf(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_fp_value_neg_inf();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_fp_value_nan(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_fp_value_nan();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_rm_value_rna(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_rm_value_rna();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_rm_value_rne(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_rm_value_rne();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_rm_value_rtn(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_rm_value_rtn();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_rm_value_rtp(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_rm_value_rtp();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_is_rm_value_rtz(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).is_rm_value_rtz();
  BITWUZLA_TRY_CATCH_END;
}

bool
bitwuzla_term_value_get_bool(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return import_term(term).value<bool>();
  BITWUZLA_TRY_CATCH_END;
}

const char *
bitwuzla_term_value_get_str(BitwuzlaTerm term, uint8_t base)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  static thread_local std::string str;
  str = import_term(term).value<std::string>(base);
  return str.c_str();
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_term_value_get_fp_ieee(BitwuzlaTerm term,
                                const char **sign,
                                const char **exponent,
                                const char **significand,
                                uint8_t base)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  static thread_local std::string _sign, _exp, _sig;
  std::tie(_sign, _exp, _sig) =
      import_term(term)
          .value<std::tuple<std::string, std::string, std::string>>(base);
  *sign        = _sign.c_str();
  *exponent    = _exp.c_str();
  *significand = _sig.c_str();
  BITWUZLA_TRY_CATCH_END;
}

BitwuzlaRoundingMode
bitwuzla_term_value_get_rm(BitwuzlaTerm term)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  return static_cast<BitwuzlaRoundingMode>(
      import_term(term).value<bitwuzla::RoundingMode>());
  BITWUZLA_TRY_CATCH_END;
}

void
bitwuzla_term_print(BitwuzlaTerm term, FILE *file)
{
  BITWUZLA_TRY_CATCH_BEGIN;
  BITWUZLA_CHECK_TERM_ID(term);
  BITWUZLA_CHECK_NOT_NULL(file);
  std::stringstream ss;
  ss << import_term(term);
  fprintf(file, "%s", ss.str().c_str());
  BITWUZLA_TRY_CATCH_END;
}

/* -------------------------------------------------------------------------- */
