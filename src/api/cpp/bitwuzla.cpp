/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <bitwuzla/cpp/bitwuzla.h>

#include <array>

#include "api/checks.h"
#include "bv/bitvector.h"
#include "config.h"
#include "node/node.h"
#include "node/node_kind.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_set.h"
#include "option/option.h"
#include "printer/printer.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "solver/result.h"
#include "solving_context.h"
#include "terminator.h"
#include "util/util.h"

namespace bitwuzla {

/* -------------------------------------------------------------------------- */

namespace {

// Helper to initialize reversed map.
template <typename K, typename V>
constexpr std::unordered_map<V, K>
_init_reverse(const std::unordered_map<K, V> &map)
{
  std::unordered_map<V, K> reversed;
  for (const auto &[k, v] : map)
  {
    auto [it, inserted] = reversed.emplace(v, k);
    (void) it;
    assert(inserted);
  }
  return reversed;
}

}  // namespace

/** Map api options to internal options. */
static const std::unordered_map<Option, bzla::option::Option>
    s_internal_options = {
        {Option::BV_SOLVER, bzla::option::Option::BV_SOLVER},
        {Option::LOGLEVEL, bzla::option::Option::LOG_LEVEL},
        {Option::PRODUCE_MODELS, bzla::option::Option::PRODUCE_MODELS},
        {Option::PRODUCE_UNSAT_ASSUMPTIONS,
         bzla::option::Option::PRODUCE_UNSAT_ASSUMPTIONS},
        {Option::PRODUCE_UNSAT_CORES,
         bzla::option::Option::PRODUCE_UNSAT_CORES},
        {Option::SAT_SOLVER, bzla::option::Option::SAT_SOLVER},
        {Option::SEED, bzla::option::Option::SEED},
        {Option::VERBOSITY, bzla::option::Option::VERBOSITY},
        {Option::TIME_LIMIT_PER, bzla::option::Option::TIME_LIMIT_PER},
        {Option::MEMORY_LIMIT, bzla::option::Option::MEMORY_LIMIT},
        {Option::REWRITE_LEVEL, bzla::option::Option::REWRITE_LEVEL},
        {Option::PROP_CONST_BITS, bzla::option::Option::PROP_CONST_BITS},
        {Option::PROP_INFER_INEQ_BOUNDS,
         bzla::option::Option::PROP_INEQ_BOUNDS},
        {Option::PROP_OPT_LT_CONCAT_SEXT,
         bzla::option::Option::PROP_OPT_LT_CONCAT_SEXT},
        {Option::PROP_NPROPS, bzla::option::Option::PROP_NPROPS},
        {Option::PROP_NUPDATES, bzla::option::Option::PROP_NUPDATES},
        {Option::PROP_PATH_SEL, bzla::option::Option::PROP_PATH_SEL},
        {Option::PROP_PROB_RANDOM_INPUT,
         bzla::option::Option::PROP_PROB_PICK_RANDOM_INPUT},
        {Option::PROP_PROB_USE_INV_VALUE,
         bzla::option::Option::PROP_PROB_PICK_INV_VALUE},
        {Option::PROP_SEXT, bzla::option::Option::PROP_SEXT},
        {Option::PROP_NORMALIZE, bzla::option::Option::PROP_NORMALIZE},
        {Option::NUM_OPTS, bzla::option::Option::NUM_OPTIONS},

        {Option::PREPROCESS, bzla::option::Option::PREPROCESS},
        {Option::PP_CONTRADICTING_ANDS,
         bzla::option::Option::PP_CONTRADICTING_ANDS},
        {Option::PP_ELIM_BV_EXTRACTS,
         bzla::option::Option::PP_ELIM_BV_EXTRACTS},
        {Option::PP_EMBEDDED_CONSTR, bzla::option::Option::PP_EMBEDDED_CONSTR},
        {Option::PP_FLATTEN_AND, bzla::option::Option::PP_FLATTEN_AND},
        {Option::PP_NORMALIZE, bzla::option::Option::PP_NORMALIZE},
        {Option::PP_NORMALIZE_SHARE_AWARE,
         bzla::option::Option::PP_NORMALIZE_SHARE_AWARE},
        {Option::PP_SKELETON_PREPROC,
         bzla::option::Option::PP_SKELETON_PREPROC},
        {Option::PP_VARIABLE_SUBST, bzla::option::Option::PP_VARIABLE_SUBST},
        {Option::PP_VARIABLE_SUBST_NORM_EQ,
         bzla::option::Option::PP_VARIABLE_SUBST_NORM_EQ},
        {Option::PP_VARIABLE_SUBST_NORM_DISEQ,
         bzla::option::Option::PP_VARIABLE_SUBST_NORM_DISEQ},
        {Option::PP_VARIABLE_SUBST_NORM_BV_INEQ,
         bzla::option::Option::PP_VARIABLE_SUBST_NORM_BV_INEQ},

        {Option::DBG_RW_NODE_THRESH, bzla::option::Option::DBG_RW_NODE_THRESH},
        {Option::DBG_PP_NODE_THRESH, bzla::option::Option::DBG_PP_NODE_THRESH},
        {Option::DBG_CHECK_MODEL, bzla::option::Option::DBG_CHECK_MODEL},
        {Option::DBG_CHECK_UNSAT_CORE,
         bzla::option::Option::DBG_CHECK_UNSAT_CORE},
};

static const std::unordered_map<bzla::option::Option, Option> s_options =
    _init_reverse(s_internal_options);

/** Map api result to internal result. */
static const std::unordered_map<Result, bzla::Result> s_internal_results = {
    {Result::SAT, bzla::Result::SAT},
    {Result::UNSAT, bzla::Result::UNSAT},
    {Result::UNKNOWN, bzla::Result::UNKNOWN},
};

/** Map internal result to api result. */
static const std::unordered_map<bzla::Result, Result> s_results =
    _init_reverse(s_internal_results);

/** Map api rounding mode to internal rounding mode. */
static const std::unordered_map<RoundingMode, bzla::RoundingMode>
    s_internal_rms = {
        {RoundingMode::RNA, bzla::RoundingMode::RNA},
        {RoundingMode::RNE, bzla::RoundingMode::RNE},
        {RoundingMode::RTN, bzla::RoundingMode::RTN},
        {RoundingMode::RTP, bzla::RoundingMode::RTP},
        {RoundingMode::RTZ, bzla::RoundingMode::RTZ},
};

/** Map internal rounding mode to api rounding mode. */
static const std::unordered_map<bzla::RoundingMode, RoundingMode> s_rms =
    _init_reverse(s_internal_rms);

/** Map api node kind to internal node kind. */
static const std::unordered_map<Kind, bzla::node::Kind> s_internal_kinds = {
    {Kind::CONSTANT, bzla::node::Kind::CONSTANT},
    {Kind::CONST_ARRAY, bzla::node::Kind::CONST_ARRAY},
    {Kind::VALUE, bzla::node::Kind::VALUE},
    {Kind::VARIABLE, bzla::node::Kind::VARIABLE},

    {Kind::AND, bzla::node::Kind::AND},
    {Kind::DISTINCT, bzla::node::Kind::DISTINCT},
    {Kind::EQUAL, bzla::node::Kind::EQUAL},
    {Kind::IMPLIES, bzla::node::Kind::IMPLIES},
    {Kind::NOT, bzla::node::Kind::NOT},
    {Kind::OR, bzla::node::Kind::OR},
    {Kind::XOR, bzla::node::Kind::XOR},

    {Kind::ITE, bzla::node::Kind::ITE},

    {Kind::EXISTS, bzla::node::Kind::EXISTS},
    {Kind::FORALL, bzla::node::Kind::FORALL},

    {Kind::APPLY, bzla::node::Kind::APPLY},
    {Kind::LAMBDA, bzla::node::Kind::LAMBDA},

    {Kind::ARRAY_SELECT, bzla::node::Kind::SELECT},
    {Kind::ARRAY_STORE, bzla::node::Kind::STORE},

    {Kind::BV_ADD, bzla::node::Kind::BV_ADD},
    {Kind::BV_AND, bzla::node::Kind::BV_AND},
    {Kind::BV_ASHR, bzla::node::Kind::BV_ASHR},
    {Kind::BV_COMP, bzla::node::Kind::BV_COMP},
    {Kind::BV_CONCAT, bzla::node::Kind::BV_CONCAT},
    {Kind::BV_DEC, bzla::node::Kind::BV_DEC},
    {Kind::BV_INC, bzla::node::Kind::BV_INC},
    {Kind::BV_MUL, bzla::node::Kind::BV_MUL},
    {Kind::BV_NAND, bzla::node::Kind::BV_NAND},
    {Kind::BV_NEG, bzla::node::Kind::BV_NEG},
    {Kind::BV_NEG_OVERFLOW, bzla::node::Kind::BV_NEGO},
    {Kind::BV_NOR, bzla::node::Kind::BV_NOR},
    {Kind::BV_NOT, bzla::node::Kind::BV_NOT},
    {Kind::BV_OR, bzla::node::Kind::BV_OR},
    {Kind::BV_REDAND, bzla::node::Kind::BV_REDAND},
    {Kind::BV_REDOR, bzla::node::Kind::BV_REDOR},
    {Kind::BV_REDXOR, bzla::node::Kind::BV_REDXOR},
    {Kind::BV_ROL, bzla::node::Kind::BV_ROL},
    {Kind::BV_ROR, bzla::node::Kind::BV_ROR},
    {Kind::BV_SADD_OVERFLOW, bzla::node::Kind::BV_SADDO},
    {Kind::BV_SDIV_OVERFLOW, bzla::node::Kind::BV_SDIVO},
    {Kind::BV_SDIV, bzla::node::Kind::BV_SDIV},
    {Kind::BV_SGE, bzla::node::Kind::BV_SGE},
    {Kind::BV_SGT, bzla::node::Kind::BV_SGT},
    {Kind::BV_SHL, bzla::node::Kind::BV_SHL},
    {Kind::BV_SHR, bzla::node::Kind::BV_SHR},
    {Kind::BV_SLE, bzla::node::Kind::BV_SLE},
    {Kind::BV_SLT, bzla::node::Kind::BV_SLT},
    {Kind::BV_SMOD, bzla::node::Kind::BV_SMOD},
    {Kind::BV_SMUL_OVERFLOW, bzla::node::Kind::BV_SMULO},
    {Kind::BV_SREM, bzla::node::Kind::BV_SREM},
    {Kind::BV_SSUB_OVERFLOW, bzla::node::Kind::BV_SSUBO},
    {Kind::BV_SUB, bzla::node::Kind::BV_SUB},
    {Kind::BV_UADD_OVERFLOW, bzla::node::Kind::BV_UADDO},
    {Kind::BV_UDIV, bzla::node::Kind::BV_UDIV},
    {Kind::BV_UGE, bzla::node::Kind::BV_UGE},
    {Kind::BV_UGT, bzla::node::Kind::BV_UGT},
    {Kind::BV_ULE, bzla::node::Kind::BV_ULE},
    {Kind::BV_ULT, bzla::node::Kind::BV_ULT},
    {Kind::BV_UMUL_OVERFLOW, bzla::node::Kind::BV_UMULO},
    {Kind::BV_UREM, bzla::node::Kind::BV_UREM},
    {Kind::BV_USUB_OVERFLOW, bzla::node::Kind::BV_USUBO},
    {Kind::BV_XNOR, bzla::node::Kind::BV_XNOR},
    {Kind::BV_XOR, bzla::node::Kind::BV_XOR},
    {Kind::BV_EXTRACT, bzla::node::Kind::BV_EXTRACT},
    {Kind::BV_REPEAT, bzla::node::Kind::BV_REPEAT},
    {Kind::BV_ROLI, bzla::node::Kind::BV_ROLI},
    {Kind::BV_RORI, bzla::node::Kind::BV_RORI},
    {Kind::BV_SIGN_EXTEND, bzla::node::Kind::BV_SIGN_EXTEND},
    {Kind::BV_ZERO_EXTEND, bzla::node::Kind::BV_ZERO_EXTEND},

    {Kind::FP_ABS, bzla::node::Kind::FP_ABS},
    {Kind::FP_ADD, bzla::node::Kind::FP_ADD},
    {Kind::FP_DIV, bzla::node::Kind::FP_DIV},
    {Kind::FP_EQUAL, bzla::node::Kind::FP_EQUAL},
    {Kind::FP_FMA, bzla::node::Kind::FP_FMA},
    {Kind::FP_FP, bzla::node::Kind::FP_FP},
    {Kind::FP_GEQ, bzla::node::Kind::FP_GEQ},
    {Kind::FP_GT, bzla::node::Kind::FP_GT},
    {Kind::FP_IS_INF, bzla::node::Kind::FP_IS_INF},
    {Kind::FP_IS_NAN, bzla::node::Kind::FP_IS_NAN},
    {Kind::FP_IS_NEG, bzla::node::Kind::FP_IS_NEG},
    {Kind::FP_IS_NORMAL, bzla::node::Kind::FP_IS_NORMAL},
    {Kind::FP_IS_POS, bzla::node::Kind::FP_IS_POS},
    {Kind::FP_IS_SUBNORMAL, bzla::node::Kind::FP_IS_SUBNORMAL},
    {Kind::FP_IS_ZERO, bzla::node::Kind::FP_IS_ZERO},
    {Kind::FP_LEQ, bzla::node::Kind::FP_LEQ},
    {Kind::FP_LT, bzla::node::Kind::FP_LT},
    {Kind::FP_MAX, bzla::node::Kind::FP_MAX},
    {Kind::FP_MIN, bzla::node::Kind::FP_MIN},
    {Kind::FP_MUL, bzla::node::Kind::FP_MUL},
    {Kind::FP_NEG, bzla::node::Kind::FP_NEG},
    {Kind::FP_REM, bzla::node::Kind::FP_REM},
    {Kind::FP_RTI, bzla::node::Kind::FP_RTI},
    {Kind::FP_SQRT, bzla::node::Kind::FP_SQRT},
    {Kind::FP_SUB, bzla::node::Kind::FP_SUB},
    {Kind::FP_TO_FP_FROM_BV, bzla::node::Kind::FP_TO_FP_FROM_BV},
    {Kind::FP_TO_FP_FROM_FP, bzla::node::Kind::FP_TO_FP_FROM_FP},
    {Kind::FP_TO_FP_FROM_SBV, bzla::node::Kind::FP_TO_FP_FROM_SBV},
    {Kind::FP_TO_FP_FROM_UBV, bzla::node::Kind::FP_TO_FP_FROM_UBV},
    {Kind::FP_TO_SBV, bzla::node::Kind::FP_TO_SBV},
    {Kind::FP_TO_UBV, bzla::node::Kind::FP_TO_UBV},
};

/** Map internal node kind to api node kind. */
static const std::unordered_map<bzla::node::Kind, Kind> s_kinds =
    _init_reverse(s_internal_kinds);

/* -------------------------------------------------------------------------- */

const char*
copyright()
{
  return bzla::config::license;
}

const char*
version()
{
  return bzla::config::version;
}

const char*
git_id()
{
  return bzla::config::git_id;
}

/* -------------------------------------------------------------------------- */

std::ostream &
operator<<(std::ostream &out, Result result)
{
  try
  {
    out << s_internal_results.at(result);
    return out;
  }
  catch (...)
  {
    throw Exception("invalid result");
  }
}

std::ostream &
operator<<(std::ostream &out, Kind kind)
{
  try
  {
    if (kind == Kind::IFF)
    {
      out << "IFF";
    }
    else
    {
      out << s_internal_kinds.at(kind);
    }
    return out;
  }
  catch (...)
  {
    throw Exception("invalid term kind");
  }
}

std::ostream &
operator<<(std::ostream &out, RoundingMode rm)
{
  try
  {
    out << s_internal_rms.at(rm);
    return out;
  }
  catch (...)
  {
    throw Exception("invalid rounding mode");
  }
}

/* Exception public --------------------------------------------------------- */

Exception::Exception(const std::string &msg) : d_msg(msg) {}

Exception::Exception(const std::stringstream &stream) : d_msg(stream.str()) {}

const std::string &
Exception::msg() const
{
  return d_msg;
}

const char *
Exception::what() const noexcept
{
  return d_msg.c_str();
}

/* set_bv_format public ----------------------------------------------------- */

set_bv_format::set_bv_format(uint8_t format) : d_format(format)
{
  BITWUZLA_CHECK(format == 2 || format == 10 || format == 16)
      << "invalid bit-vector output number format, expected '2', '10' or '16'";
}

std::ostream &
operator<<(std::ostream &ostream, const set_bv_format &f)
{
  ostream.iword(bzla::Printer::s_stream_index_bv_format) = f.format();
  return ostream;
}

/* Options public ----------------------------------------------------------- */

Options::Options() : d_options(new bzla::option::Options()) {}

Options::~Options() {}

Options::Options(const Options &options)
    : d_options(new bzla::option::Options(*options.d_options))
{
}

Options &
Options::operator=(const Options &options)
{
  d_options.reset(new bzla::option::Options(*options.d_options));
  return *this;
}

bool
Options::is_valid(const std::string &name) const
{
  return d_options->is_valid(name);
}

bool
Options::is_bool(Option option) const
{
  return d_options->is_bool(s_internal_options.at(option));
}

bool
Options::is_numeric(Option option) const
{
  return d_options->is_numeric(s_internal_options.at(option));
}

bool
Options::is_mode(Option option) const
{
  return d_options->is_mode(s_internal_options.at(option));
}

const char *
Options::shrt(Option option) const
{
  return d_options->shrt(s_internal_options.at(option));
}

const char *
Options::lng(Option option) const
{
  return d_options->lng(s_internal_options.at(option));
}

const char *
Options::description(Option option) const
{
  return d_options->description(s_internal_options.at(option));
}

std::vector<std::string>
Options::modes(Option option) const
{
  return d_options->modes(s_internal_options.at(option));
}

Option
Options::option(const char *name) const
{
  BITWUZLA_CHECK(d_options->is_valid(name))
      << "invalid option '" << name << "'";
  return s_options.at(d_options->option(name));
}

void
Options::set(Option option, uint64_t value)
{
  BITWUZLA_CHECK_NOT_NULL(d_options);
  bzla::option::Option opt = s_internal_options.at(option);
  if (d_options->is_bool(opt))
  {
    d_options->set<bool>(opt, value != 0, true);
  }
  else
  {
    BITWUZLA_CHECK(d_options->is_numeric(opt))
        << "expected Boolean or numeric option";
    BITWUZLA_CHECK(value >= d_options->min<uint64_t>(opt))
        << "invalid option value, expected value >= "
        << d_options->min<uint64_t>(opt);
    BITWUZLA_CHECK(value <= d_options->max<uint64_t>(opt))
        << "invalid option value, expected value <= "
        << d_options->max<uint64_t>(opt);
    d_options->set<uint64_t>(opt, value, true);
  }
}

void
Options::set(Option option, const std::string &mode)
{
  BITWUZLA_CHECK_NOT_NULL(d_options);
  bzla::option::Option opt = s_internal_options.at(option);
  BITWUZLA_CHECK(d_options->is_mode(opt))
      << "expected option with option modes";
  BITWUZLA_CHECK(d_options->is_valid_mode(opt, mode))
      << "invalid mode for option";
  d_options->set<std::string>(s_internal_options.at(option), mode, true);
}

void
Options::set(Option option, const char *mode)
{
  BITWUZLA_CHECK_NOT_NULL(d_options);
  bzla::option::Option opt = s_internal_options.at(option);
  BITWUZLA_CHECK(d_options->is_mode(opt))
      << "expected option with option modes";
  BITWUZLA_CHECK(d_options->is_valid_mode(opt, mode))
      << "invalid mode for option";
  d_options->set<std::string>(s_internal_options.at(option), mode, true);
}

void
Options::set(const std::string &lng, const std::string &value)
{
  BITWUZLA_CHECK_STR_NOT_EMPTY(lng);
  BITWUZLA_CHECK_STR_NOT_EMPTY(value);
  BITWUZLA_CHECK(d_options->is_valid(lng)) << "invalid option '" << lng << "'";
  bzla::option::Option opt = d_options->option(lng);
  std::string v            = value;
  v.erase(std::remove_if(v.begin(), v.end(), ::isspace), v.end());
  std::transform(v.begin(), v.end(), v.begin(), ::tolower);
  BITWUZLA_CHECK(!d_options->is_bool(opt) || v == "0" || v == "1" || v == "true"
                 || v == "false")
      << "invalid option value for Boolean option, expected '1', '0', 'true' "
         "or 'false'; got '"
      << value << "'";
  BITWUZLA_CHECK(!d_options->is_numeric(opt)
                 || bzla::util::is_valid_bv_str(value, 10))
      << "invalid option value for numeric option";
  BITWUZLA_CHECK(!d_options->is_mode(opt)
                 || d_options->is_valid_mode(opt, value))
      << "invalid option value for option with modes";
  d_options->set(lng, value, true);
}

void
Options::set(const std::vector<std::string> &args)
{
  size_t i = 0, size = args.size();
  while (i < size)
  {
    const std::string &arg = args[i++];

    // -o=v, --option=value
    std::string opt, value;
    auto pos = arg.rfind("=");
    if (pos != std::string::npos)
    {
      opt   = arg.substr(0, pos);
      value = arg.substr(pos + 1);
    }
    // -o v, --option value
    else if (i < args.size() && !args[i].empty() && args[i][0] != '-')
    {
      opt   = arg;
      value = args[i++];
    }
    // no option value
    else
    {
      opt = arg;
    }

    bool is_no  = false;
    auto option = bzla::option::Option::NUM_OPTIONS;
    if (opt.rfind("--", 0) == 0)
    {
      std::string lng;
      if (opt.rfind("no-", 2) == 2)
      {
        lng   = opt.substr(5);
        is_no = true;
      }
      else
      {
        lng = opt.substr(2);
      }
      if (d_options->is_valid(lng))
      {
        option = d_options->option(lng);
      }
    }
    else if (opt.rfind("-", 0) == 0)
    {
      std::string shrt = opt.substr(1);
      if (d_options->is_valid(shrt))
      {
        option = d_options->option(shrt);
      }
    }

    BITWUZLA_CHECK(option != bzla::option::Option::NUM_OPTIONS)
        << "invalid option '" << opt << "'";

    if (d_options->is_bool(option))
    {
      bool val = true;
      if (!value.empty())
      {
        if (value == "true" || value == "1")
        {
          val = true;
        }
        else if (value == "false" || value == "0")
        {
          val = false;
        }
        else
        {
          BITWUZLA_CHECK(false)
              << "invalid option value for Boolean option '" << opt
              << "', expected '1', '0', 'true' or 'false'; got '"
              << value << "'";
        }
      }
      if (is_no)
      {
        val = !val;
      }
      auto it = s_options.find(option);
      BITWUZLA_CHECK(it != s_options.end()) << "invalid option '" << opt << "'";
      set(s_options.at(option), val);
      continue;
    }

    BITWUZLA_CHECK(!is_no) << "invalid --no- prefix for non-Boolean option: '"
                           << opt << "'";

    if (d_options->is_numeric(option))
    {
      uint64_t val = 0;
      if (value.empty())
      {
        // no value given, increment by one
        val = d_options->get<uint64_t>(option) + 1;
      }
      else
      {
        try
        {
          val          = std::stoull(value);
          uint64_t max = d_options->max<uint64_t>(option);
          BITWUZLA_CHECK(val <= max)
              << "invalid value '" << value << "' for numeric option '" << opt
              << "', maximum is " << max;
          uint64_t min = d_options->min<uint64_t>(option);
          BITWUZLA_CHECK(val >= min)
              << "invalid value '" << value << "' for numeric option '" << opt
              << "', minimum is " << max;
        }
        catch (const std::invalid_argument &e)
        {
          BITWUZLA_CHECK(false) << "invalid value '" << value
                                << "' for numeric option '" << opt << "'";
        }
      }
      set(s_options.at(option), val);
    }
    else
    {
      BITWUZLA_CHECK(!value.empty())
          << "expected value for option '" << opt << "'";
      BITWUZLA_CHECK(d_options->is_valid_mode(option, value))
          << "invalid mode '" << value << "' for option '" << opt << "'";
      set(s_options.at(option), value);
    }
  }
}

uint64_t
Options::get(Option option) const
{
  BITWUZLA_CHECK_NOT_NULL(d_options);
  bzla::option::Option opt = s_internal_options.at(option);
  if (d_options->is_bool(opt))
  {
    return d_options->get<bool>(opt);
  }
  BITWUZLA_CHECK(d_options->is_numeric(opt))
      << "expected Boolean or numeric option";
  return d_options->get<uint64_t>(opt);
}

const std::string &
Options::get_mode(Option option) const
{
  BITWUZLA_CHECK_NOT_NULL(d_options);
  bzla::option::Option opt = s_internal_options.at(option);
  BITWUZLA_CHECK(d_options->is_mode(opt))
      << "expected option with option modes";
  return d_options->get<std::string>(opt);
}

/* OptionInfo public -------------------------------------------------------- */

OptionInfo::OptionInfo(const Options &options, Option option) : opt(option)
{
  try
  {
    bzla::option::Option opt = s_internal_options.at(option);
    shrt                     = options.d_options->shrt(opt);
    lng                      = options.d_options->lng(opt);
    description              = options.d_options->description(opt);

    if (options.is_bool(option))
    {
      kind   = Kind::BOOL;
      values = Bool{options.d_options->get<bool>(opt),
                    options.d_options->dflt<bool>(opt)};
    }
    else if (options.is_numeric(option))
    {
      kind   = Kind::NUMERIC;
      values = Numeric{options.d_options->get<uint64_t>(opt),
                       options.d_options->dflt<uint64_t>(opt),
                       options.d_options->min<uint64_t>(opt),
                       options.d_options->max<uint64_t>(opt)};
    }
    else
    {
      assert(options.is_mode(option));
      kind   = Kind::MODE;
      values = Mode{options.d_options->get<std::string>(opt),
                    options.d_options->dflt<std::string>(opt),
                    options.d_options->modes(opt)};
    }
  }
  catch (std::out_of_range &e)
  {
    throw Exception("invalid option");
  }
}

template <>
OptionInfo::Bool
OptionInfo::value() const
{
  BITWUZLA_CHECK(kind == Kind::BOOL) << "expected Boolean option";
  return std::get<OptionInfo::Bool>(values);
}

template <>
OptionInfo::Numeric
OptionInfo::value() const
{
  BITWUZLA_CHECK(kind == Kind::NUMERIC) << "expected numeric option";
  return std::get<OptionInfo::Numeric>(values);
}

template <>
OptionInfo::Mode
OptionInfo::value() const
{
  BITWUZLA_CHECK(kind == Kind::MODE) << "expected option with modes";
  return std::get<OptionInfo::Mode>(values);
}

/* Term public -------------------------------------------------------------- */

Term::Term() : d_node(nullptr) {}

Term::~Term() {}

bool
Term::is_null() const
{
  return d_node == nullptr;
}

uint64_t
Term::id() const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  return d_node->id();
}

Kind
Term::kind() const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  return s_kinds.at(d_node->kind());
}

Sort
Term::sort() const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  return d_node->type();
}

size_t
Term::num_children() const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  return d_node->num_children();
}

std::vector<Term>
Term::children() const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  std::vector<Term> res;
  for (const bzla::Node &node : *d_node)
  {
    res.push_back(node);
  }
  return res;
}

Term
Term::operator[](size_t index) const
{
  BITWUZLA_CHECK(index < d_node->num_children())
      << "invalid access into term children, index '" << index
      << "' is greater than number of children";
  return (*d_node)[index];
}

size_t
Term::num_indices() const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  return d_node->num_indices();
}

std::vector<uint64_t>
Term::indices() const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  return d_node->indices();
}

std::optional<std::reference_wrapper<const std::string>>
Term::symbol() const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  return d_node->symbol();
}

bool
Term::is_const() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::CONSTANT;
}

bool
Term::is_variable() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VARIABLE;
}

bool
Term::is_value() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE;
}

bool
Term::is_true() const
{
  return d_node != nullptr && d_node->is_value() && d_node->type().is_bool()
         && d_node->value<bool>();
}

bool
Term::is_false() const
{
  return d_node != nullptr && d_node->is_value() && d_node->type().is_bool()
         && !d_node->value<bool>();
}

bool
Term::is_bv_value_zero() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_bv()
         && d_node->value<bzla::BitVector>().is_zero();
}

bool
Term::is_bv_value_one() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_bv() && d_node->value<bzla::BitVector>().is_one();
}

bool
Term::is_bv_value_ones() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_bv()
         && d_node->value<bzla::BitVector>().is_ones();
}

bool
Term::is_bv_value_min_signed() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_bv()
         && d_node->value<bzla::BitVector>().is_min_signed();
}

bool
Term::is_bv_value_max_signed() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_bv()
         && d_node->value<bzla::BitVector>().is_max_signed();
}

bool
Term::is_fp_value_pos_zero() const
{
  if (d_node == nullptr || d_node->kind() != bzla::node::Kind::VALUE
      || !d_node->type().is_fp())
  {
    return false;
  }
  const bzla::FloatingPoint &fp = d_node->value<bzla::FloatingPoint>();
  return fp.fpispos() && fp.fpiszero();
}

bool
Term::is_fp_value_neg_zero() const
{
  if (d_node == nullptr || d_node->kind() != bzla::node::Kind::VALUE
      || !d_node->type().is_fp())
  {
    return false;
  }
  const bzla::FloatingPoint &fp = d_node->value<bzla::FloatingPoint>();
  return fp.fpisneg() && fp.fpiszero();
}

bool
Term::is_fp_value_pos_inf() const
{
  if (d_node == nullptr || d_node->kind() != bzla::node::Kind::VALUE
      || !d_node->type().is_fp())
  {
    return false;
  }
  const bzla::FloatingPoint &fp = d_node->value<bzla::FloatingPoint>();
  return fp.fpispos() && fp.fpisinf();
}

bool
Term::is_fp_value_neg_inf() const
{
  if (d_node == nullptr || d_node->kind() != bzla::node::Kind::VALUE
      || !d_node->type().is_fp())
  {
    return false;
  }
  const bzla::FloatingPoint &fp = d_node->value<bzla::FloatingPoint>();
  return fp.fpisneg() && fp.fpisinf();
}

bool
Term::is_fp_value_nan() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_fp()
         && d_node->value<bzla::FloatingPoint>().fpisnan();
}

bool
Term::is_rm_value_rna() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_rm()
         && d_node->value<bzla::RoundingMode>() == bzla::RoundingMode::RNA;
}

bool
Term::is_rm_value_rne() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_rm()
         && d_node->value<bzla::RoundingMode>() == bzla::RoundingMode::RNE;
}

bool
Term::is_rm_value_rtn() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_rm()
         && d_node->value<bzla::RoundingMode>() == bzla::RoundingMode::RTN;
}

bool
Term::is_rm_value_rtp() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_rm()
         && d_node->value<bzla::RoundingMode>() == bzla::RoundingMode::RTP;
}

bool
Term::is_rm_value_rtz() const
{
  return d_node != nullptr && d_node->kind() == bzla::node::Kind::VALUE
         && d_node->type().is_rm()
         && d_node->value<bzla::RoundingMode>() == bzla::RoundingMode::RTZ;
}

std::string
Term::str(uint8_t base) const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  if (!d_node)
  {
    return "(nil)";
  }
  return d_node->str(base);
}

template <>
bool
Term::value(uint8_t base) const
{
  (void) base;
  BITWUZLA_CHECK_NOT_NULL(d_node);
  BITWUZLA_CHECK_TERM_IS_BOOL_VALUE(*this);
  return d_node->value<bool>();
}

template <>
RoundingMode
Term::value(uint8_t base) const
{
  (void) base;
  BITWUZLA_CHECK_NOT_NULL(d_node);
  BITWUZLA_CHECK_TERM_IS_RM_VALUE(*this);
  return s_rms.at(d_node->value<bzla::RoundingMode>());
}

// TODO support base -10 for signed decimal values
template <>
std::string
Term::value(uint8_t base) const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  BITWUZLA_CHECK(d_node->is_value()) << "expected value term";
  const auto &type = d_node->type();
  if (type.is_bool())
  {
    return d_node->value<bool>() ? "true" : "false";
  }
  else if (type.is_bv())
  {
    BITWUZLA_CHECK_VALUE_BASE(base);
    return d_node->value<bzla::BitVector>().str(base);
  }
  else if (type.is_fp())
  {
    const bzla::FloatingPoint &fp_value = d_node->value<bzla::FloatingPoint>();
    return fp_value.as_bv().str(2);
  }
  else if (type.is_rm())
  {
    std::stringstream ss;
    ss << s_rms.at(d_node->value<bzla::RoundingMode>());
    return ss.str();
  }
  else
  {
    BITWUZLA_CHECK(false) << "unsupported type encountered";
  }
  return std::string();
}

template <>
std::tuple<std::string, std::string, std::string>
Term::value(uint8_t base) const
{
  BITWUZLA_CHECK_NOT_NULL(d_node);
  BITWUZLA_CHECK_TERM_IS_FP(*this);
  BITWUZLA_CHECK_VALUE_BASE(base);
  const bzla::FloatingPoint &fp_value = d_node->value<bzla::FloatingPoint>();
  bzla::BitVector sign, exp, sig;
  bzla::FloatingPoint::ieee_bv_as_bvs(
      d_node->type(), fp_value.as_bv(), sign, exp, sig);
  return std::make_tuple(sign.str(base), exp.str(base), sig.str(base));
}

bool
operator==(const Term &a, const Term &b)
{
  if (a.d_node == nullptr)
  {
    return b.d_node == nullptr;
  }
  if (b.d_node == nullptr)
  {
    return false;
  }
  return *a.d_node == *b.d_node;
}

bool
operator!=(const Term &a, const Term &b)
{
  if (a.d_node == nullptr)
  {
    return b.d_node != nullptr;
    ;
  }
  if (b.d_node == nullptr)
  {
    return true;
  }
  return *a.d_node != *b.d_node;
}

std::ostream &
operator<<(std::ostream &out, const Term &term)
{
  if (term.d_node)
  {
    out << *term.d_node;
  }
  else
  {
    out << "(nil)";
  }
  return out;
}

/* Sort public -------------------------------------------------------------- */

Sort::Sort() : d_type(nullptr) {}

Sort::~Sort() {}

bool
Sort::is_null() const
{
  return d_type == nullptr;
}

uint64_t
Sort::id() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  return d_type->id();
}

uint64_t
Sort::bv_size() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  BITWUZLA_CHECK_SORT_IS_BV(*this);
  return d_type->bv_size();
}

uint64_t
Sort::fp_exp_size() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  BITWUZLA_CHECK_SORT_IS_FP(*this);
  return d_type->fp_exp_size();
}

uint64_t
Sort::fp_sig_size() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  BITWUZLA_CHECK_SORT_IS_FP(*this);
  return d_type->fp_sig_size();
}

Sort
Sort::array_index() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  BITWUZLA_CHECK_SORT_IS_ARRAY(*this);
  return d_type->array_index();
}

Sort
Sort::array_element() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  BITWUZLA_CHECK_SORT_IS_ARRAY(*this);
  return d_type->array_element();
}

std::vector<Sort>
Sort::fun_domain() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  BITWUZLA_CHECK_SORT_IS_FUN(*this);
  const std::vector<bzla::Type> types = d_type->fun_types();
  assert(types.size() > 0);
  std::vector<Sort> res;
  for (size_t i = 0, n = types.size() - 1; i < n; ++i)
  {
    res.push_back(types[i]);
  }
  return res;
}

Sort
Sort::fun_codomain() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  BITWUZLA_CHECK_SORT_IS_FUN(*this);
  const std::vector<bzla::Type> types = d_type->fun_types();
  assert(types.size() > 0);
  return types.back();
}

size_t
Sort::fun_arity() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  BITWUZLA_CHECK_SORT_IS_FUN(*this);
  return d_type->fun_arity();
}

std::optional<std::string>
Sort::uninterpreted_symbol() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  BITWUZLA_CHECK_SORT_IS_UNINTEPRETED(*this);
  return d_type->uninterpreted_symbol();
}

bool
Sort::is_array() const
{
  return d_type != nullptr && d_type->is_array();
}

bool
Sort::is_bool() const
{
  return d_type != nullptr && d_type->is_bool();
}

bool
Sort::is_bv() const
{
  return d_type != nullptr && d_type->is_bv();
}

bool
Sort::is_fp() const
{
  return d_type != nullptr && d_type->is_fp();
}

bool
Sort::is_fun() const
{
  return d_type != nullptr && d_type->is_fun();
}

bool
Sort::is_rm() const
{
  return d_type != nullptr && d_type->is_rm();
}

bool
Sort::is_uninterpreted() const
{
  return d_type != nullptr && d_type->is_uninterpreted();
}

std::string
Sort::str() const
{
  BITWUZLA_CHECK_NOT_NULL(d_type);
  if (!d_type)
  {
    return "(nil)";
  }
  return d_type->str();
}

bool
operator==(const Sort &a, const Sort &b)
{
  if (a.d_type == nullptr)
  {
    return b.d_type == nullptr;
    ;
  }
  if (b.d_type == nullptr)
  {
    return false;
  }
  return *a.d_type == *b.d_type;
}

bool
operator!=(const Sort &a, const Sort &b)
{
  if (a.d_type == nullptr)
  {
    return b.d_type != nullptr;
    ;
  }
  if (b.d_type == nullptr)
  {
    return true;
  }
  return *a.d_type != *b.d_type;
}

std::ostream &
operator<<(std::ostream &out, const Sort &sort)
{
  if (sort.d_type)
  {
    out << *sort.d_type;
  }
  else
  {
    out << "(nil)";
  }
  return out;
}

/* Terminator public -------------------------------------------------------- */

Terminator::~Terminator() {}

/* Terminator internal ------------------------------------------------------ */

class TerminatorInternal : public bzla::Terminator
{
 public:
  /**
   * Constructor.
   * @param terminator The associated user-facing terminator.
   */
  TerminatorInternal(bitwuzla::Terminator *terminator)
      : d_terminator(terminator)
  {
  }

  bool terminate() override
  {
    if (d_terminator == nullptr)
    {
      return false;
    }
    return d_terminator->terminate();
  }

 private:
  /** The associated user-facing terminator. */
  bitwuzla::Terminator *d_terminator;
};

/* Bitwuzla public ---------------------------------------------------------- */

Bitwuzla::Bitwuzla(const Options &options)
    : d_ctx(new bzla::SolvingContext(*options.d_options, "main")),
      d_last_check_sat(Result::UNKNOWN),
      d_n_sat_calls(0)
{
}

Bitwuzla::~Bitwuzla() {}

void
Bitwuzla::configure_terminator(Terminator *terminator)
{
  if (terminator == nullptr)
  {
    if (d_terminator != nullptr)
    {
      assert(d_terminator_internal);
      d_terminator_internal.reset(nullptr);
    }
  }
  else
  {
    d_terminator_internal.reset(new TerminatorInternal(terminator));
  }
  d_ctx->env().configure_terminator(d_terminator_internal.get());
  d_terminator = terminator;
}

void
Bitwuzla::push(uint32_t nlevels)
{
  BITWUZLA_CHECK_NOT_NULL(d_ctx);
  solver_state_change();
  for (uint32_t i = 0; i < nlevels; ++i)
  {
    d_ctx->push();
  }
}

void
Bitwuzla::pop(uint32_t nlevels)
{
  BITWUZLA_CHECK_NOT_NULL(d_ctx);
  BITWUZLA_CHECK(nlevels <= d_ctx->backtrack_mgr()->num_levels())
      << "number of context levels to pop (" << nlevels
      << ") greater than number of pushed context levels ("
      << d_ctx->backtrack_mgr()->num_levels() << ")";

  solver_state_change();
  for (uint32_t i = 0; i < nlevels; ++i)
  {
    d_ctx->pop();
  }
}

void
Bitwuzla::assert_formula(const Term &term)
{
  BITWUZLA_CHECK_NOT_NULL(d_ctx);
  BITWUZLA_CHECK_TERM_NOT_NULL(term);
  BITWUZLA_CHECK_TERM_IS_BOOL(term);
  BITWUZLA_CHECK_TERM_IS_NOT_VAR(term);
  solver_state_change();
  d_ctx->assert_formula(*term.d_node);
}

std::vector<Term>
Bitwuzla::get_assertions()
{
  BITWUZLA_CHECK_NOT_NULL(d_ctx);
  std::vector<Term> res;
  const bzla::backtrack::AssertionView &assertions = d_ctx->assertions();
  for (size_t i = 0, n = assertions.size(); i < n; ++i)
  {
    res.push_back(assertions[i]);
  }
  return res;
}

bool
Bitwuzla::is_unsat_assumption(const Term &term)
{
  BITWUZLA_CHECK_NOT_NULL(d_ctx);
  BITWUZLA_CHECK_OPT_PRODUCE_UNSAT_ASSUMPTIONS(d_ctx->options());
  BITWUZLA_CHECK_LAST_CALL_UNSAT("is unsat assumption");
  BITWUZLA_CHECK_TERM_NOT_NULL(term);
  BITWUZLA_CHECK_TERM_IS_BOOL(term);
  if (d_assumptions.find(term) == d_assumptions.end())
  {
    return false;
  }
  if (!d_uc_is_valid)
  {
    assert(d_unsat_core.empty());
    d_unsat_core  = Term::node_vector_to_terms(d_ctx->get_unsat_core());
    d_uc_is_valid = true;
  }
  return std::find(d_unsat_core.begin(), d_unsat_core.end(), term)
         != d_unsat_core.end();
}

std::vector<Term>
Bitwuzla::get_unsat_assumptions()
{
  BITWUZLA_CHECK_NOT_NULL(d_ctx);
  BITWUZLA_CHECK_OPT_PRODUCE_UNSAT_ASSUMPTIONS(d_ctx->options());
  BITWUZLA_CHECK_LAST_CALL_UNSAT("get unsat assumptions");
  if (!d_uc_is_valid)
  {
    assert(d_unsat_core.empty());
    d_unsat_core  = Term::node_vector_to_terms(d_ctx->get_unsat_core());
    d_uc_is_valid = true;
  }
  std::vector<Term> res;
  for (const auto &t : d_unsat_core)
  {
    if (d_assumptions.find(t) != d_assumptions.end())
    {
      res.push_back(t);
    }
  }
  return res;
}

std::vector<Term>
Bitwuzla::get_unsat_core()
{
  BITWUZLA_CHECK_NOT_NULL(d_ctx);
  BITWUZLA_CHECK_OPT_PRODUCE_UNSAT_CORES(d_ctx->options());
  BITWUZLA_CHECK_LAST_CALL_UNSAT("get unsat core");
  if (!d_uc_is_valid)
  {
    assert(d_unsat_core.empty());
    d_unsat_core  = Term::node_vector_to_terms(d_ctx->get_unsat_core());
    d_uc_is_valid = true;
  }
  return d_unsat_core;
}

void
Bitwuzla::simplify()
{
  BITWUZLA_CHECK_NOT_NULL(d_ctx);
  solver_state_change();
  d_ctx->preprocess();
}

Result
Bitwuzla::check_sat(const std::vector<Term> &assumptions)
{
  BITWUZLA_CHECK_NOT_NULL(d_ctx);
  solver_state_change();
  d_n_sat_calls += 1;
  d_assumptions.clear();
  d_unsat_core.clear();
  d_uc_is_valid = false;
  if (!assumptions.empty())
  {
    d_ctx->push();
    for (const Term &term : assumptions)
    {
      d_ctx->assert_formula(*term.d_node);
      d_assumptions.insert(term);
    }
    d_last_check_sat = s_results.at(d_ctx->solve());
    // Delay pop until other methods are called that change solver state. This
    // allows users to query values and unsat cores after a check-sat with
    // assumptions.
    d_pending_pop = true;
  }
  else
  {
    d_last_check_sat = s_results.at(d_ctx->solve());
  }
  return d_last_check_sat;
}

Term
Bitwuzla::get_value(const Term &term)
{
  BITWUZLA_CHECK_NOT_NULL(d_ctx);
  BITWUZLA_CHECK_TERM_NOT_NULL(term);
  BITWUZLA_CHECK_OPT_PRODUCE_MODELS(d_ctx->options());
  BITWUZLA_CHECK_LAST_CALL_SAT("get value");
  return d_ctx->get_value(*term.d_node);
}

void
Bitwuzla::print_formula(std::ostream &out, const std::string &format) const
{
  BITWUZLA_CHECK_STR_NOT_EMPTY(format);
  BITWUZLA_CHECK(format == "smt2") << "invalid format, expected 'smt2'";
  try
  {
    bzla::Printer::print_formula(out, d_ctx->assertions());
  }
  catch (bzla::printer::Exception &e)
  {
    throw Exception(e.msg());
  }
}

std::map<std::string, std::string>
Bitwuzla::statistics() const
{
  return d_ctx->env().statistics().get();
}

/* Bitwuzla private --------------------------------------------------------- */

void
Bitwuzla::solver_state_change()
{
  if (d_pending_pop)
  {
    d_ctx->pop();
    d_pending_pop = false;
  }
}

/* -------------------------------------------------------------------------- */

Sort
mk_array_sort(const Sort &index, const Sort &element)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(index);
  BITWUZLA_CHECK_SORT_NOT_NULL(element);
  BITWUZLA_CHECK(!index.is_array())
      << "array sorts not supported as index sort of array";
  return bzla::NodeManager::get().mk_array_type(*index.d_type, *element.d_type);
}

Sort
mk_bool_sort()
{
  return bzla::NodeManager::get().mk_bool_type();
}

Sort
mk_bv_sort(uint64_t size)
{
  BITWUZLA_CHECK_NOT_ZERO(size);
  return bzla::NodeManager::get().mk_bv_type(size);
}

Sort
mk_fp_sort(uint64_t exp_size, uint64_t sig_size)
{
  BITWUZLA_CHECK_GREATER_ONE(exp_size);
  BITWUZLA_CHECK_GREATER_ONE(sig_size);
  return bzla::NodeManager::get().mk_fp_type(exp_size, sig_size);
}

Sort
mk_fun_sort(const std::vector<Sort> &domain, const Sort &codomain)
{
  BITWUZLA_CHECK(domain.size() > 0) << "function arity must be > 0";
  BITWUZLA_CHECK_SORT_NOT_NULL(codomain);
  // domain sorts are checked to be not null in sort_vector_to_types()
  std::vector<bzla::Type> types = Sort::sort_vector_to_types(domain);
  types.push_back(*codomain.d_type);
  return bzla::NodeManager::get().mk_fun_type(types);
}

Sort
mk_rm_sort()
{
  return bzla::NodeManager::get().mk_rm_type();
}

Sort
mk_uninterpreted_sort(std::optional<const std::string> symbol)
{
  return bzla::NodeManager::get().mk_uninterpreted_type(symbol);
}

Term
mk_true()
{
  return bzla::NodeManager::get().mk_value(true);
}

Term
mk_false()
{
  return bzla::NodeManager::get().mk_value(false);
}

Term
mk_bv_zero(const Sort &sort)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_BV(sort);
  return bzla::NodeManager::get().mk_value(
      bzla::BitVector::mk_zero(sort.d_type->bv_size()));
}

Term
mk_bv_one(const Sort &sort)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_BV(sort);
  return bzla::NodeManager::get().mk_value(
      bzla::BitVector::mk_one(sort.d_type->bv_size()));
}

Term
mk_bv_ones(const Sort &sort)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_BV(sort);
  return bzla::NodeManager::get().mk_value(
      bzla::BitVector::mk_ones(sort.d_type->bv_size()));
}

Term
mk_bv_min_signed(const Sort &sort)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_BV(sort);
  return bzla::NodeManager::get().mk_value(
      bzla::BitVector::mk_min_signed(sort.d_type->bv_size()));
}

Term
mk_bv_max_signed(const Sort &sort)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_BV(sort);
  return bzla::NodeManager::get().mk_value(
      bzla::BitVector::mk_max_signed(sort.d_type->bv_size()));
}

Term
mk_bv_value(const Sort &sort, const std::string &value, uint8_t base)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_BV(sort);
  BITWUZLA_CHECK_STR_NOT_EMPTY(value);
  BITWUZLA_CHECK_VALUE_BASE(base);
  BITWUZLA_CHECK(bzla::util::is_valid_bv_str(value, base))
      << "invalid "
      << (base == 2 ? "binary" : (base == 10 ? "decimal" : "hexadecimal"))
      << " string";
  BITWUZLA_CHECK(
      bzla::BitVector::fits_in_size(sort.d_type->bv_size(), value, base))
      << "value '" << value << "' does not fit into a bit-vector of size '"
      << sort.d_type->bv_size() << "'";
  return bzla::NodeManager::get().mk_value(
      bzla::BitVector(sort.d_type->bv_size(), value, base));
}

Term
mk_bv_value_uint64(const Sort &sort, uint64_t value)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_BV(sort);
  BITWUZLA_CHECK(
      bzla::BitVector::fits_in_size(sort.d_type->bv_size(), value, false))
      << "value '" << value << "' does not fit into a bit-vector of size '"
      << sort.d_type->bv_size() << "'";
  return bzla::NodeManager::get().mk_value(
      bzla::BitVector::from_ui(sort.d_type->bv_size(), value));
}

Term
mk_bv_value_int64(const Sort &sort, int64_t value)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_BV(sort);
  BITWUZLA_CHECK(
      bzla::BitVector::fits_in_size(sort.d_type->bv_size(), value, true))
      << "value '" << value << "' does not fit into a bit-vector of size '"
      << sort.d_type->bv_size() << "'";
  return bzla::NodeManager::get().mk_value(
      bzla::BitVector::from_si(sort.d_type->bv_size(), value));
}

Term
mk_fp_pos_zero(const Sort &sort)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_FP(sort);
  return bzla::NodeManager::get().mk_value(
      bzla::FloatingPoint::fpzero(*sort.d_type, false));
}

Term
mk_fp_neg_zero(const Sort &sort)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_FP(sort);
  return bzla::NodeManager::get().mk_value(
      bzla::FloatingPoint::fpzero(*sort.d_type, true));
}

Term
mk_fp_pos_inf(const Sort &sort)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_FP(sort);
  return bzla::NodeManager::get().mk_value(
      bzla::FloatingPoint::fpinf(*sort.d_type, false));
}

Term
mk_fp_neg_inf(const Sort &sort)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_FP(sort);
  return bzla::NodeManager::get().mk_value(
      bzla::FloatingPoint::fpinf(*sort.d_type, true));
}

Term
mk_fp_nan(const Sort &sort)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_IS_FP(sort);
  return bzla::NodeManager::get().mk_value(
      bzla::FloatingPoint::fpnan(*sort.d_type));
}

Term
mk_fp_value(const Term &bv_sign,
            const Term &bv_exponent,
            const Term &bv_significand)
{
  BITWUZLA_CHECK_TERM_NOT_NULL(bv_sign);
  BITWUZLA_CHECK_TERM_NOT_NULL(bv_exponent);
  BITWUZLA_CHECK_TERM_NOT_NULL(bv_significand);
  BITWUZLA_CHECK_TERM_IS_BV_VALUE(bv_sign);
  BITWUZLA_CHECK_TERM_IS_BV_VALUE(bv_exponent);
  BITWUZLA_CHECK_TERM_IS_BV_VALUE(bv_significand);
  BITWUZLA_CHECK(bv_sign.d_node->type().bv_size() == 1)
      << "invalid bit-vector size for argument 'bv_sign', expected size 1";
  BITWUZLA_CHECK(bv_exponent.d_node->type().bv_size() > 1)
      << "invalid bit-vector size for argument 'bv_sign', expected size > 1";
  return bzla::NodeManager::get().mk_value(bzla::FloatingPoint(
      bzla::NodeManager::get().mk_fp_type(
          bv_exponent.d_node->type().bv_size(),
          bv_significand.d_node->type().bv_size() + 1),
      bv_sign.d_node->value<bzla::BitVector>()
          .bvconcat(bv_exponent.d_node->value<bzla::BitVector>())
          .ibvconcat(bv_significand.d_node->value<bzla::BitVector>())));
}

Term
mk_fp_value(const Sort &sort, const Term &rm, const std::string &real)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_TERM_NOT_NULL(rm);
  BITWUZLA_CHECK_SORT_IS_FP(sort);
  BITWUZLA_CHECK_TERM_IS_RM(rm);
  BITWUZLA_CHECK(bzla::util::is_valid_real_str(real)) << "invalid real string";

  if (rm.d_node->is_value())
  {
    return bzla::NodeManager::get().mk_value(bzla::FloatingPoint::from_real(
        *sort.d_type, rm.d_node->value<bzla::RoundingMode>(), real));
  }

  bzla::NodeManager &nm = bzla::NodeManager::get();

  bzla::Node rna = nm.mk_value(bzla::RoundingMode::RNA);
  bzla::Node rne = nm.mk_value(bzla::RoundingMode::RNE);
  bzla::Node rtn = nm.mk_value(bzla::RoundingMode::RTN);
  bzla::Node rtp = nm.mk_value(bzla::RoundingMode::RTP);
  bzla::Node rtz = nm.mk_value(bzla::RoundingMode::RTZ);

  bzla::Node fp_rna = nm.mk_value(bzla::FloatingPoint::from_real(
      *sort.d_type, rna.value<bzla::RoundingMode>(), real));
  bzla::Node fp_rne = nm.mk_value(bzla::FloatingPoint::from_real(
      *sort.d_type, rne.value<bzla::RoundingMode>(), real));
  bzla::Node fp_rtn = nm.mk_value(bzla::FloatingPoint::from_real(
      *sort.d_type, rtn.value<bzla::RoundingMode>(), real));
  bzla::Node fp_rtp = nm.mk_value(bzla::FloatingPoint::from_real(
      *sort.d_type, rtp.value<bzla::RoundingMode>(), real));
  bzla::Node fp_rtz = nm.mk_value(bzla::FloatingPoint::from_real(
      *sort.d_type, rtz.value<bzla::RoundingMode>(), real));

  bzla::Node cond = nm.mk_node(bzla::node::Kind::EQUAL, {*rm.d_node, rtp});
  bzla::Node ite  = nm.mk_node(bzla::node::Kind::ITE, {cond, fp_rtp, fp_rtz});

  cond = nm.mk_node(bzla::node::Kind::EQUAL, {*rm.d_node, rtn});
  ite  = nm.mk_node(bzla::node::Kind::ITE, {cond, fp_rtn, ite});

  cond = nm.mk_node(bzla::node::Kind::EQUAL, {*rm.d_node, rne});
  ite  = nm.mk_node(bzla::node::Kind::ITE, {cond, fp_rne, ite});

  cond = nm.mk_node(bzla::node::Kind::EQUAL, {*rm.d_node, rna});
  ite  = nm.mk_node(bzla::node::Kind::ITE, {cond, fp_rna, ite});

  return ite;
}

Term
mk_fp_value(const Sort &sort,
            const Term &rm,
            const std::string &num,
            const std::string &den)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_TERM_NOT_NULL(rm);
  BITWUZLA_CHECK_SORT_IS_FP(sort);
  BITWUZLA_CHECK_TERM_IS_RM(rm);
  BITWUZLA_CHECK(bzla::util::is_valid_real_str(num))
      << "invalid real string for argument 'num'";
  BITWUZLA_CHECK(bzla::util::is_valid_real_str(den))
      << "invalid real string for argument 'den'";

  if (rm.d_node->is_value())
  {
    return bzla::NodeManager::get().mk_value(bzla::FloatingPoint::from_rational(
        *sort.d_type, rm.d_node->value<bzla::RoundingMode>(), num, den));
  }

  bzla::NodeManager &nm = bzla::NodeManager::get();

  bzla::Node rna = nm.mk_value(bzla::RoundingMode::RNA);
  bzla::Node rne = nm.mk_value(bzla::RoundingMode::RNE);
  bzla::Node rtn = nm.mk_value(bzla::RoundingMode::RTN);
  bzla::Node rtp = nm.mk_value(bzla::RoundingMode::RTP);
  bzla::Node rtz = nm.mk_value(bzla::RoundingMode::RTZ);

  bzla::Node fp_rna = nm.mk_value(bzla::FloatingPoint::from_rational(
      *sort.d_type, rna.value<bzla::RoundingMode>(), num, den));
  bzla::Node fp_rne = nm.mk_value(bzla::FloatingPoint::from_rational(
      *sort.d_type, rne.value<bzla::RoundingMode>(), num, den));
  bzla::Node fp_rtn = nm.mk_value(bzla::FloatingPoint::from_rational(
      *sort.d_type, rtn.value<bzla::RoundingMode>(), num, den));
  bzla::Node fp_rtp = nm.mk_value(bzla::FloatingPoint::from_rational(
      *sort.d_type, rtp.value<bzla::RoundingMode>(), num, den));
  bzla::Node fp_rtz = nm.mk_value(bzla::FloatingPoint::from_rational(
      *sort.d_type, rtz.value<bzla::RoundingMode>(), num, den));

  bzla::Node cond = nm.mk_node(bzla::node::Kind::EQUAL, {*rm.d_node, rtp});
  bzla::Node ite  = nm.mk_node(bzla::node::Kind::ITE, {cond, fp_rtp, fp_rtz});

  cond = nm.mk_node(bzla::node::Kind::EQUAL, {*rm.d_node, rtn});
  ite  = nm.mk_node(bzla::node::Kind::ITE, {cond, fp_rtn, ite});

  cond = nm.mk_node(bzla::node::Kind::EQUAL, {*rm.d_node, rne});
  ite  = nm.mk_node(bzla::node::Kind::ITE, {cond, fp_rne, ite});

  cond = nm.mk_node(bzla::node::Kind::EQUAL, {*rm.d_node, rna});
  ite  = nm.mk_node(bzla::node::Kind::ITE, {cond, fp_rna, ite});

  return ite;
}

Term
mk_rm_value(RoundingMode rm)
{
  return bzla::NodeManager::get().mk_value(s_internal_rms.at(rm));
}

Term
mk_const_array(const Sort &sort, const Term &term)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_TERM_NOT_NULL(term);
  BITWUZLA_CHECK(sort.d_type->is_array())
      << "sort of constant array is not an array sort";
  BITWUZLA_CHECK(sort.d_type->array_element() == term.d_node->type())
      << "sort of constant array element does not match given array sort";
  return bzla::NodeManager::get().mk_const_array(*sort.d_type, *term.d_node);
}

Term
mk_term(Kind kind,
        const std::vector<Term> &args,
        const std::vector<uint64_t> &indices)
{
  switch (kind)
  {
    // left/right associative, chainable, pairwise
    case Kind::AND:
    case Kind::DISTINCT:
    case Kind::IMPLIES:
    case Kind::OR:
    case Kind::XOR:
    case Kind::BV_ADD:
    case Kind::BV_AND:
    case Kind::BV_CONCAT:
    case Kind::BV_MUL:
    case Kind::BV_OR:
    case Kind::BV_XOR:
    case Kind::EQUAL:
    case Kind::IFF:
    case Kind::BV_COMP:
    case Kind::FP_EQUAL:
    case Kind::FP_GEQ:
    case Kind::FP_GT:
    case Kind::FP_LEQ:
    case Kind::FP_LT:
    case Kind::EXISTS:
    case Kind::FORALL:
    case Kind::LAMBDA:
      BITWUZLA_CHECK_MK_TERM_ARGC(kind, true, 2, args.size());
      BITWUZLA_CHECK_MK_TERM_IDXC(kind, 0, indices.size());
      switch (kind)
      {
        case Kind::AND:
        case Kind::IFF:
        case Kind::IMPLIES:
        case Kind::OR:
        case Kind::XOR:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_bool, true);
          break;
        case Kind::DISTINCT:
        case Kind::EQUAL:
          BITWUZLA_CHECK_MK_TERM_ARGS_ANY_SORT(args, 0, true);
          break;
        case Kind::BV_CONCAT:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_bv, false);
          break;
        case Kind::FP_EQUAL:
        case Kind::FP_GEQ:
        case Kind::FP_GT:
        case Kind::FP_LEQ:
        case Kind::FP_LT:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_fp, true);
          break;
        case Kind::EXISTS:
        case Kind::FORALL:
          BITWUZLA_CHECK_TERM_IS_BOOL_AT_IDX(args, args.size() - 1);
          [[fallthrough]];
        case Kind::LAMBDA: {
          bzla::node::unordered_node_ref_set cache;
          for (size_t i = 0, n = args.size() - 1; i < n; ++i)
          {
            BITWUZLA_CHECK_TERM_IS_VAR_AT_IDX(args, i);
            BITWUZLA_CHECK(kind == Kind::LAMBDA
                           || !args[i].d_node->type().is_array())
                << "quantified variable of array sort not supported";
            BITWUZLA_CHECK(kind == Kind::LAMBDA
                           || !args[i].d_node->type().is_fun())
                << "quantified variable of function sort not supported";
            auto [it, inserted] = cache.insert(*args[i].d_node);
            BITWUZLA_CHECK(inserted) << "expected set of distinct variables";
          }
        }
        break;
        default: BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_bv, true);
      }
      if (kind == Kind::IFF)
      {
        return bzla::node::utils::mk_nary(bzla::node::Kind::EQUAL,
                                          Term::term_vector_to_nodes(args));
      }
      return bzla::node::utils::mk_nary(s_internal_kinds.at(kind),
                                        Term::term_vector_to_nodes(args));
    // unary
    case Kind::NOT:
    case Kind::BV_DEC:
    case Kind::BV_INC:
    case Kind::BV_NEG:
    case Kind::BV_NEG_OVERFLOW:
    case Kind::BV_NOT:
    case Kind::BV_REDAND:
    case Kind::BV_REDOR:
    case Kind::BV_REDXOR:
    case Kind::FP_ABS:
    case Kind::FP_IS_INF:
    case Kind::FP_IS_NAN:
    case Kind::FP_IS_NEG:
    case Kind::FP_IS_NORMAL:
    case Kind::FP_IS_POS:
    case Kind::FP_IS_SUBNORMAL:
    case Kind::FP_IS_ZERO:
    case Kind::FP_NEG:
      BITWUZLA_CHECK_MK_TERM_ARGC(kind, false, 1, args.size());
      BITWUZLA_CHECK_MK_TERM_IDXC(kind, 0, indices.size());
      switch (kind)
      {
        case Kind::NOT:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_bool, true);
          break;
        case Kind::BV_DEC:
        case Kind::BV_INC:
        case Kind::BV_NEG:
        case Kind::BV_NEG_OVERFLOW:
        case Kind::BV_NOT:
        case Kind::BV_REDAND:
        case Kind::BV_REDOR:
        case Kind::BV_REDXOR:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_bv, true);
          break;
        default: BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_fp, true);
      }
      break;
    // binary
    case Kind::ARRAY_SELECT:
    case Kind::BV_ASHR:
    case Kind::BV_NAND:
    case Kind::BV_NOR:
    case Kind::BV_ROL:
    case Kind::BV_ROR:
    case Kind::BV_SADD_OVERFLOW:
    case Kind::BV_SDIV_OVERFLOW:
    case Kind::BV_SDIV:
    case Kind::BV_SGE:
    case Kind::BV_SGT:
    case Kind::BV_SHL:
    case Kind::BV_SHR:
    case Kind::BV_SLE:
    case Kind::BV_SLT:
    case Kind::BV_SMOD:
    case Kind::BV_SMUL_OVERFLOW:
    case Kind::BV_SREM:
    case Kind::BV_SSUB_OVERFLOW:
    case Kind::BV_SUB:
    case Kind::BV_UADD_OVERFLOW:
    case Kind::BV_UDIV:
    case Kind::BV_UGE:
    case Kind::BV_UGT:
    case Kind::BV_ULE:
    case Kind::BV_ULT:
    case Kind::BV_UMUL_OVERFLOW:
    case Kind::BV_UREM:
    case Kind::BV_USUB_OVERFLOW:
    case Kind::BV_XNOR:
    case Kind::FP_MAX:
    case Kind::FP_MIN:
    case Kind::FP_REM:
    case Kind::FP_RTI:
    case Kind::FP_SQRT:
      BITWUZLA_CHECK_MK_TERM_ARGC(kind, false, 2, args.size());
      BITWUZLA_CHECK_MK_TERM_IDXC(kind, 0, indices.size());
      switch (kind)
      {
        case Kind::ARRAY_SELECT:
          BITWUZLA_CHECK_MK_TERM_ARGS_ANY_SORT(args, 1, true);
          BITWUZLA_CHECK_TERM_IS_ARRAY(args[0]);
          BITWUZLA_CHECK(args[1].d_node->type()
                         == args[0].d_node->type().array_index())
              << "sort of index term does not match index sort of array";
          break;
        case Kind::FP_MAX:
        case Kind::FP_MIN:
        case Kind::FP_REM:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_fp, true);
          break;
        case Kind::FP_RTI:
        case Kind::FP_SQRT:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 1, is_fp, true);
          BITWUZLA_CHECK_TERM_IS_RM_AT_IDX(args, 0);
          break;
        default: BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_bv, true);
      }
      break;
    // ternary
    case Kind::ITE:
    case Kind::ARRAY_STORE:
    case Kind::FP_ADD:
    case Kind::FP_DIV:
    case Kind::FP_FP:
    case Kind::FP_MUL:
    case Kind::FP_SUB:
      BITWUZLA_CHECK_MK_TERM_ARGC(kind, false, 3, args.size());
      BITWUZLA_CHECK_MK_TERM_IDXC(kind, 0, indices.size());
      switch (kind)
      {
        case Kind::ITE:
          BITWUZLA_CHECK_MK_TERM_ARGS_ANY_SORT(args, 1, true);
          BITWUZLA_CHECK_TERM_IS_BOOL_AT_IDX(args, 0);
          break;
        case Kind::ARRAY_STORE:
          BITWUZLA_CHECK_MK_TERM_ARGS_ANY_SORT(args, 0, false);
          BITWUZLA_CHECK_TERM_IS_ARRAY_AT_IDX(args, 0);
          BITWUZLA_CHECK(args[0].d_node->type().array_index()
                         == args[1].d_node->type())
              << "sort of index term does not match index sort of array";
          BITWUZLA_CHECK(args[0].d_node->type().array_element()
                         == args[2].d_node->type())
              << "sort of element term does not match element sort of array";
          break;
        case Kind::FP_FP:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_bv, false);
          BITWUZLA_CHECK(args[0].d_node->type().bv_size() == 1)
              << "expected bit-vector term of size 1 at index 0";
          break;
        default:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 1, is_fp, true);
          BITWUZLA_CHECK_TERM_IS_RM_AT_IDX(args, 0);
      }
      break;
    // quaternary
    case Kind::FP_FMA:
      BITWUZLA_CHECK_MK_TERM_ARGC(kind, false, 4, args.size());
      BITWUZLA_CHECK_MK_TERM_IDXC(kind, 0, indices.size());
      BITWUZLA_CHECK_MK_TERM_ARGS(args, 1, is_fp, true);
      BITWUZLA_CHECK_TERM_IS_RM_AT_IDX(args, 0);
      break;
    // nary
    case Kind::APPLY: {
      BITWUZLA_CHECK(args.size() > 1) << "expected at least two arguments";
      BITWUZLA_CHECK_TERM_IS_FUN_AT_IDX(args, 0);
      const bzla::Type &type_fun = args[0].d_node->type();
      size_t arity               = type_fun.fun_arity();
      BITWUZLA_CHECK_MK_TERM_ARGC(kind, true, arity + 1, args.size());
      BITWUZLA_CHECK_MK_TERM_IDXC(kind, 0, indices.size());
      size_t paramc = args.size() - 1;
      BITWUZLA_CHECK(paramc == arity)
          << "number of function arguments does not match function arity, "
             "expected '"
          << arity << "' but got '" << paramc << "'";
      const auto &types = type_fun.fun_types();
      for (size_t i = 1; i <= paramc; ++i)
      {
        BITWUZLA_CHECK_NOT_NULL_AT_IDX(args[i].d_node, i);
        BITWUZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(args, i);
        BITWUZLA_CHECK(types[i - 1] == args[i].d_node->type())
            << "sort of argument at index " << i
            << " does not match sort in function domain";
      }
    }
    break;

    // unary, indexed (1)
    case Kind::BV_REPEAT:
    case Kind::BV_ROLI:
    case Kind::BV_RORI:
    case Kind::BV_SIGN_EXTEND:
    case Kind::BV_ZERO_EXTEND:
      BITWUZLA_CHECK_MK_TERM_ARGC(kind, false, 1, args.size());
      BITWUZLA_CHECK_MK_TERM_IDXC(kind, 1, indices.size());
      BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_bv, true);
      if (kind == Kind::BV_REPEAT)
      {
        BITWUZLA_CHECK(((uint64_t) (UINT64_MAX / indices[0]))
                       >= args[0].d_node->type().bv_size())
            << "resulting bit-vector size exceeds maximum "
               "bit-vector size of "
            << UINT64_MAX;
      }
      else if (kind == Kind::BV_SIGN_EXTEND || kind == Kind::BV_ZERO_EXTEND)
      {
        BITWUZLA_CHECK(indices[0]
                       <= UINT64_MAX - args[0].d_node->type().bv_size())
            << "extending term of bit-vector size "
            << args[0].d_node->type().bv_size() << " with " << indices[0]
            << " bits exceeds maximum bit-vector size of " << UINT64_MAX;
      }
      break;
    // unary, indexed (2)
    case Kind::BV_EXTRACT:
    case Kind::FP_TO_FP_FROM_BV:
      BITWUZLA_CHECK_MK_TERM_ARGC(kind, false, 1, args.size());
      BITWUZLA_CHECK_MK_TERM_IDXC(kind, 2, indices.size());
      switch (kind)
      {
        case Kind::BV_EXTRACT:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_bv, true);
          BITWUZLA_CHECK(indices[0] < args[0].d_node->type().bv_size())
              << "upper index must be less than the bit-vector size of given "
                 "term";
          BITWUZLA_CHECK(indices[0] >= indices[1])
              << "upper index must be greater or equal to lower index";
          break;
        case Kind::FP_TO_FP_FROM_BV:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 0, is_bv, true);
          BITWUZLA_CHECK_GREATER_ONE(indices[0]);
          BITWUZLA_CHECK_GREATER_ONE(indices[1]);
          BITWUZLA_CHECK(indices[0] + indices[1]
                         == args[0].d_node->type().bv_size())
              << "size of bit-vector does not match given floating-point "
                 "format";
          break;
        default: assert(false);
      }
      break;
    // binary, indexed (1)
    case Kind::FP_TO_SBV:
    case Kind::FP_TO_UBV:
      BITWUZLA_CHECK_MK_TERM_ARGC(kind, false, 2, args.size());
      BITWUZLA_CHECK_MK_TERM_IDXC(kind, 1, indices.size());
      BITWUZLA_CHECK_MK_TERM_ARGS(args, 1, is_fp, true);
      BITWUZLA_CHECK_TERM_IS_RM_AT_IDX(args, 0);
      break;
    // binary, indexed (2)
    case Kind::FP_TO_FP_FROM_FP:
    case Kind::FP_TO_FP_FROM_SBV:
    case Kind::FP_TO_FP_FROM_UBV:
      BITWUZLA_CHECK_MK_TERM_ARGC(kind, false, 2, args.size());
      BITWUZLA_CHECK_MK_TERM_IDXC(kind, 2, indices.size());
      BITWUZLA_CHECK_GREATER_ONE(indices[0]);
      BITWUZLA_CHECK_GREATER_ONE(indices[1]);
      switch (kind)
      {
        case Kind::FP_TO_FP_FROM_FP:
          BITWUZLA_CHECK_MK_TERM_ARGS(args, 1, is_fp, true);
          break;
        default: BITWUZLA_CHECK_MK_TERM_ARGS(args, 1, is_bv, true);
      }
      BITWUZLA_CHECK_TERM_IS_RM_AT_IDX(args, 0);
      break;

    default:
      BITWUZLA_CHECK(false) << "unexpected operator kind '" << kind << "'";
  }

  return bzla::NodeManager::get().mk_node(
      s_internal_kinds.at(kind), Term::term_vector_to_nodes(args), indices);
}

Term
mk_const(const Sort &sort, std::optional<const std::string> symbol)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  return bzla::NodeManager::get().mk_const(*sort.d_type, symbol);
}

Term
mk_var(const Sort &sort, std::optional<const std::string> symbol)
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  BITWUZLA_CHECK_SORT_NOT_IS_FUN(sort);
  return bzla::NodeManager::get().mk_var(*sort.d_type, symbol);
}

Term
substitute_term(const Term &term, const std::unordered_map<Term, Term> &map)
{
  BITWUZLA_CHECK_TERM_NOT_NULL(term);
  std::vector<Term> terms = {term};
  substitute_terms(terms, map);
  return terms[0];
}

namespace {
Term
rebuild_term(const Term &term, const std::vector<Term> &children)
{
  if (children.size()) assert(term.num_children() == children.size());
  if (term.num_children() == 0)
  {
    assert(children.empty());
    return term;
  }
  else if ((term.kind() == Kind::FORALL || term.kind() == Kind::EXISTS)
           && !children[0].is_variable())
  {
    // if the variable of a quantifier is substituted by a non-variable,
    // we substitute it with its body
    return children[1];
  }
  else if (term.kind() == Kind::CONST_ARRAY)
  {
    assert(children.size() == 1);
    return bitwuzla::mk_const_array(term.sort(), children[0]);
  }
  else
  {
    return bitwuzla::mk_term(term.kind(), children, term.indices());
  }
}
}  // namespace

void
substitute_terms(std::vector<Term> &terms,
                 const std::unordered_map<Term, Term> &map)
{
  if (terms.empty() || map.empty())
  {
    return;
  }

  for (const auto &[k, v] : map)
  {
    BITWUZLA_CHECK_TERM_NOT_NULL(k);
    BITWUZLA_CHECK_TERM_NOT_NULL(v);
    BITWUZLA_CHECK(k.sort() == v.sort())
        << "invalid term substitution, mismatching sorts: " << k << " -> " << v;
  }

  std::vector<Term> visit;
  std::unordered_map<Term, Term> cache;

  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    BITWUZLA_CHECK_TERM_NOT_NULL_AT_IDX(terms, i);
    visit.push_back(terms[i]);
  }

  while (!visit.empty())
  {
    Term cur            = visit.back();
    auto [it, inserted] = cache.emplace(cur, Term());
    if (inserted)
    {
      for (size_t i = 0, n = cur.num_children(); i < n; ++i)
      {
        visit.push_back(cur[i]);
      }
      continue;
    }
    if (it->second.is_null())
    {
      Term result;
      auto iit = map.find(cur);
      if (iit != map.end())
      {
        result = iit->second;
      }
      else
      {
        std::vector<Term> children;
        for (size_t i = 0, n = cur.num_children(); i < n; ++i)
        {
          auto cit = cache.find(cur[i]);
          assert(cit != map.end());
          children.push_back(cit->second);
        }
        result = rebuild_term(cur, children);
      }
      it->second = result;
    }
    visit.pop_back();
  }

  for (size_t i = 0, n = terms.size(); i < n; ++i)
  {
    auto it = cache.find(terms[i]);
    assert(it != cache.end());
    terms[i] = it->second;
  }
}

/* Term private ------------------------------------------------------------- */

Term::Term(const bzla::Node &node) : d_node(new bzla::Node(node)) {}

std::vector<bzla::Node>
Term::term_vector_to_nodes(const std::vector<Term> &terms)
{
  std::vector<bzla::Node> res;
  for (const auto &term : terms)
  {
    res.emplace_back(*term.d_node);
  }
  return res;
}

std::vector<bitwuzla::Term>
Term::node_vector_to_terms(const std::vector<bzla::Node> &nodes)
{
  std::vector<bitwuzla::Term> res;
  for (const auto &node : nodes)
  {
    res.push_back(node);
  }
  return res;
}

/* Sort private ------------------------------------------------------------- */

Sort::Sort(const bzla::Type &type) : d_type(new bzla::Type(type)) {}

std::vector<bzla::Type>
Sort::sort_vector_to_types(const std::vector<Sort> &sorts)
{
  std::vector<bzla::Type> res;
  for (const auto &sort : sorts)
  {
    BITWUZLA_CHECK_SORT_NOT_NULL(sort);
    res.push_back(*sort.d_type);
  }
  return res;
}

/* -------------------------------------------------------------------------- */
}  // namespace bitwuzla
/* -------------------------------------------------------------------------- */

namespace std {

std::string
to_string(bitwuzla::RoundingMode rm)
{
  try
  {
    std::stringstream ss;
    ss << bitwuzla::s_internal_rms.at(rm);
    return ss.str();
  }
  catch (...)
  {
    throw bitwuzla::Exception("invalid rounding mode");
  }
}

std::string
to_string(bitwuzla::Kind kind)
{
  try
  {
    std::stringstream ss;
    if (kind == bitwuzla::Kind::IFF)
    {
      ss << "IFF";
    }
    else
    {
      ss << bitwuzla::s_internal_kinds.at(kind);
    }
    return ss.str();
  }
  catch (...)
  {
    throw bitwuzla::Exception("invalid term kind");
  }
}

std::string
to_string(bitwuzla::Result result)
{
  try
  {
    std::stringstream ss;
    ss << bitwuzla::s_internal_results.at(result);
    return ss.str();
  }
  catch (...)
  {
    throw bitwuzla::Exception("invalid result");
  }
}

size_t
std::hash<bitwuzla::Sort>::operator()(const bitwuzla::Sort &sort) const
{
  BITWUZLA_CHECK_SORT_NOT_NULL(sort);
  return std::hash<bzla::Type>{}(*sort.d_type);
}

size_t
std::hash<bitwuzla::Term>::operator()(const bitwuzla::Term &term) const
{
  BITWUZLA_CHECK_TERM_NOT_NULL(term);
  return std::hash<bzla::Node>{}(*term.d_node);
}

}  // namespace std
