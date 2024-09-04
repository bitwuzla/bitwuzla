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
#include <bitwuzla/cpp/parser.h>

#include <iostream>

#include "main/error.h"
#include "main/options.h"
#include "main/time_limit.h"

using namespace bzla::main;

int32_t
main(int32_t argc, char* argv[])
{
  bitwuzla::Options options;
  bitwuzla::TermManager tm;

  std::vector<std::string> args;
  bzla::main::Options main_options =
      bzla::main::parse_options(argc, argv, args);

  try
  {
    set_time_limit(main_options.time_limit);
    options.set(args);

    if (main_options.print_unsat_core)
    {
      options.set(bitwuzla::Option::PRODUCE_UNSAT_CORES, 1);
    }
    if (main_options.print_model)
    {
      options.set(bitwuzla::Option::PRODUCE_MODELS, 1);
    }

    std::cout << bitwuzla::set_bv_format(main_options.bv_format);
    bitwuzla::parser::Parser parser(
        tm, options, main_options.language, &std::cout);
    parser.configure_auto_print_model(main_options.print_model);
    parser.parse(main_options.infile_name,
                 main_options.print || main_options.parse_only);
    reset_time_limit();
    bitwuzla::Bitwuzla* bitwuzla = parser.bitwuzla().get();
    if (main_options.print)
    {
      if (!main_options.parse_only)
      {
        bitwuzla->simplify();
      }
      bitwuzla->print_formula(std::cout, "smt2");
    }

    if (main_options.print_unsat_core)
    {
      bitwuzla->print_unsat_core(std::cout);
    }

    if (options.get(bitwuzla::Option::VERBOSITY))
    {
      auto stats = bitwuzla->statistics();
      for (auto& [name, val] : stats)
      {
        std::cout << name << ": " << val << std::endl;
      }
    }
  }
  catch (const bitwuzla::parser::Exception& e)
  {
    Error() << e.msg();
  }
  catch (const bitwuzla::Exception& e)
  {
    // Remove the "invalid call to '...', prefix
    const std::string& msg = e.msg();
    size_t pos             = msg.find("', ");
    Error() << msg.substr(pos + 3);
  }
  std::exit(EXIT_SUCCESS);
}
