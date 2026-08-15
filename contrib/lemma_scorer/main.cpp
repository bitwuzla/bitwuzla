/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include "env.h"
#include "main/error.h"
#include "node/node_kind.h"
#include "node/node_manager.h"
#include "option/option.h"
#include "sat/sat_solver_factory.h"
#include "solver/abstract/abstraction_lemma_scorer.h"

using namespace bzla;
using bzla::main::Error;

namespace {

/** The mode of operation of the lemma scorer. */
enum class Mode
{
  SCORE,
  RANK_SCORE,
  RANK_CIRCUIT_SIZE,
  VERIFY,
};

struct Options
{
  /** The operator kinds to score the lemma schemas of. */
  std::vector<node::Kind> kinds;
  /** The bit-width to score/verify the lemma schemas for. */
  uint64_t bv_size = 4;
  /** The bit-width to measure the circuit size of the lemma schemas for. */
  uint64_t circuit_bv_size = 32;
  /** The configured mode of operation. */
  Mode mode = Mode::SCORE;
};

/** The operator kinds with lemma schemas, and their command line values. */
const std::vector<std::pair<std::string, node::Kind>> g_kinds = {
    {"add", node::Kind::BV_ADD},
    {"mul", node::Kind::BV_MUL},
    {"udiv", node::Kind::BV_UDIV},
    {"urem", node::Kind::BV_UREM},
};

/** The supported modes of operation, and their command line values. */
const std::vector<std::pair<std::string, Mode>> g_modes = {
    {"score", Mode::SCORE},
    {"rank-score", Mode::RANK_SCORE},
    {"rank-circuit-size", Mode::RANK_CIRCUIT_SIZE},
    {"verify", Mode::VERIFY},
};

/**
 * Maximum bit-width for the modes that exhaustively enumerate all triplets
 * (x, s, t) of bit-vector values of the given bit-width.
 */
constexpr uint64_t k_max_score_bv_size = 8;

void
print_help()
{
  std::cout
      << "usage: bzla-lemma-scorer [<option>...]" << std::endl
      << std::endl
      << "Score, rank and verify the abstraction lemma schemas of bit-vector"
      << std::endl
      << "operators (see src/solver/abstract/abstraction_lemmas.h)."
      << std::endl
      << std::endl
      << "  -h, --help          print this message and exit" << std::endl
      << "  -k, --kind <K>      score the lemma schemas of operator kind <K>,"
      << std::endl
      << "                      may be given multiple times, one of:"
      << std::endl
      << "                        add, mul, udiv, urem" << std::endl
      << "                      (default: all of the above)" << std::endl
      << "  -b, --bv-size <n>   the bit-width lemmas are scored/verified for;"
      << std::endl
      << "                      scores are computed for a single bit-width,"
      << std::endl
      << "                      verification is from [3, <n>]" << std::endl
      << "                      (default: 4, maximum: " << k_max_score_bv_size
      << " for all modes but 'verify')" << std::endl
      << "  -c, --circuit-bv-size <n>" << std::endl
      << "                      the bit-width the circuit size of the lemma"
      << std::endl
      << "                      schemas is measured for, only used by mode"
      << std::endl
      << "                      'rank-circuit-size' (default: 32)" << std::endl
      << "  -m, --mode <M>      the mode of operation, one of:" << std::endl
      << "                        score              print the score of each"
      << " lemma schema" << std::endl
      << "                                           (default)" << std::endl
      << "                        rank-score         rank lemma schemas by"
      << " their score" << std::endl
      << "                        rank-circuit-size  rank lemma schemas by"
      << " the size of" << std::endl
      << "                                           their bit-blasted circuit"
      << std::endl
      << "                        verify             verify lemma schemas for "
         "bit-widths"
      << std::endl
      << "                                           [3, <bv-size>]"
      << std::endl;
}

/**
 * Parse the value of the option at position `i`, advances `i` to the value.
 * @param argc The number of command line arguments.
 * @param i    The position of the option in `argv`.
 * @param argv The command line arguments.
 * @return The value of the option.
 */
std::string
parse_arg_val(int32_t argc, int32_t& i, char* argv[])
{
  std::string arg(argv[i]);
  if (i + 1 >= argc)
  {
    Error() << "expected value for option `" << arg << "`";
  }
  return std::string(argv[++i]);
}

/**
 * Parse the numeric value of the option at position `i`, advances `i` to the
 * value.
 * @param argc The number of command line arguments.
 * @param i    The position of the option in `argv`.
 * @param argv The command line arguments.
 * @return The value of the option.
 */
uint64_t
parse_arg_uint64(int32_t argc, int32_t& i, char* argv[])
{
  std::string arg(argv[i]);
  std::string val = parse_arg_val(argc, i, argv);
  try
  {
    return std::stoull(val);
  }
  catch (const std::exception& e)
  {
    Error() << "expected numeric value for option `" << arg << "` but got `"
            << val << "`";
  }
}

/**
 * Look up the given command line value in the given map of values.
 * @param values The supported values, maps command line value to its
 *               representation.
 * @param arg    The option the value was given for.
 * @param val    The given command line value.
 * @return The representation of the given value.
 */
template <class T>
T
parse_value(const std::vector<std::pair<std::string, T>>& values,
            const std::string& arg,
            const std::string& val)
{
  auto it = std::find_if(values.begin(), values.end(), [&val](const auto& p) {
    return p.first == val;
  });
  if (it == values.end())
  {
    std::string expected;
    for (const auto& [name, value] : values)
    {
      expected += (expected.empty() ? "" : ", ") + name;
    }
    Error() << "invalid value `" << val << "` for option `" << arg
            << "`, expected one of: " << expected;
  }
  return it->second;
}

Options
parse_options(int32_t argc, char* argv[])
{
  Options opts;
  for (int32_t i = 1; i < argc; ++i)
  {
    std::string arg(argv[i]);
    if (arg == "-h" || arg == "--help")
    {
      print_help();
      std::exit(EXIT_SUCCESS);
    }
    else if (arg == "-k" || arg == "--kind")
    {
      opts.kinds.push_back(
          parse_value(g_kinds, arg, parse_arg_val(argc, i, argv)));
    }
    else if (arg == "-m" || arg == "--mode")
    {
      opts.mode = parse_value(g_modes, arg, parse_arg_val(argc, i, argv));
    }
    else if (arg == "-b" || arg == "--bv-size")
    {
      opts.bv_size = parse_arg_uint64(argc, i, argv);
    }
    else if (arg == "-c" || arg == "--circuit-bv-size")
    {
      opts.circuit_bv_size = parse_arg_uint64(argc, i, argv);
    }
    else
    {
      Error() << "invalid option `" << arg << "`, try `--help`";
    }
  }

  if (opts.kinds.empty())
  {
    for (const auto& [name, kind] : g_kinds)
    {
      opts.kinds.push_back(kind);
    }
  }

  if (opts.bv_size == 0)
  {
    Error() << "invalid bit-width `0`";
  }
  if (opts.circuit_bv_size == 0)
  {
    Error() << "invalid circuit bit-width `0`";
  }
  if (opts.mode != Mode::VERIFY && opts.bv_size > k_max_score_bv_size)
  {
    Error() << "bit-width " << opts.bv_size
            << " is too large for exhaustive scoring, maximum is "
            << k_max_score_bv_size;
  }

  return opts;
}

}  // namespace

int32_t
main(int32_t argc, char* argv[])
{
  Options opts = parse_options(argc, argv);

  option::Options options;
  NodeManager nm;
  sat::SatSolverFactory sat_factory(options);
  Env env(nm, sat_factory, options, "lemma-scorer");
  abstract::AbstractionLemmaScorer scorer(env, opts.kinds);

  switch (opts.mode)
  {
    case Mode::SCORE: scorer.score_lemmas(opts.bv_size); break;
    case Mode::RANK_SCORE: scorer.rank_lemmas_by_score(opts.bv_size); break;
    case Mode::RANK_CIRCUIT_SIZE:
      scorer.rank_lemmas_by_circuit_size(opts.bv_size, opts.circuit_bv_size);
      break;
    case Mode::VERIFY: scorer.verify_lemmas(opts.bv_size); break;
  }

  return EXIT_SUCCESS;
}
