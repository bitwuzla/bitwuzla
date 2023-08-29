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

  std::vector<std::string> args;
  bzla::main::Options main_options =
      bzla::main::parse_options(argc, argv, args);

  try
  {
    set_time_limit(main_options.time_limit);
    options.set(args);

    std::cout << bitwuzla::set_bv_format(main_options.bv_format);
    bitwuzla::parser::Parser parser(
        options, main_options.infile_name, main_options.language, &std::cout);
    std::string err_msg =
        parser.parse(main_options.print || main_options.parse_only);
    reset_time_limit();
    if (!err_msg.empty())
    {
      Error() << err_msg;
    }
    bitwuzla::Bitwuzla* bitwuzla = parser.bitwuzla().get();
    if (main_options.print)
    {
      if (!main_options.parse_only)
      {
        bitwuzla->simplify();
      }
      bitwuzla->print_formula(std::cout, main_options.language);
    }
    else if (main_options.language == "btor2")
    {
      bitwuzla::Result res = bitwuzla->check_sat();
      std::cout << res << std::endl;
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
  catch (const bitwuzla::Exception& e)
  {
    // Remove the "invalid call to '...', prefix
    const std::string& msg = e.msg();
    size_t pos             = msg.find("', ");
    Error() << msg.substr(pos + 3);
  }
  std::exit(EXIT_SUCCESS);
}
