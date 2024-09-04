/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_MAIN_OPTIONS_H_INCLUDED
#define BZLA_MAIN_OPTIONS_H_INCLUDED

#include <cstdint>
#include <string>
#include <vector>

namespace bzla::main {

struct Options
{
  bool print              = false;
  bool print_unsat_core   = false;
  bool print_model        = false;
  bool parse_only         = false;
  uint8_t bv_format       = 2;
  uint64_t time_limit     = 0;
  std::string infile_name = "<stdin>";
  std::string language    = "smt2";
};

/**
 * Parse command line options.
 *
 * @param argc Number of arguments in argv.
 * @param argv Command line arguments.
 * @param args Parsed library options.
 * @return Main options.
 */
Options parse_options(int32_t argc,
                      char* argv[],
                      std::vector<std::string>& args);

}  // namespace bzla::main

#endif
