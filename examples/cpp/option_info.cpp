/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <bitwuzla/cpp/bitwuzla.h>

#include <iostream>

using namespace bitwuzla;

int
main()
{
  // First, create a Bitwuzla options instance.
  Options options;
  // Set some options to illustrate current vs default value.
  options.set(Option::PRODUCE_MODELS, true);
  options.set(Option::VERBOSITY, 2);
  options.set(Option::BV_SOLVER, "prop");

  // Then iterate over all available configuration options and extract info.
  for (int32_t i = 0; i < static_cast<int32_t>(Option::NUM_OPTS); ++i)
  {
    Option opt = static_cast<Option>(i);
    OptionInfo info(options, opt);
    std::cout << "- long name:   " << info.lng << std::endl;
    std::cout << "  short name:  " << (info.shrt ? info.shrt : "-")
              << std::endl;
    std::cout << "  kind:        ";
    if (info.kind == OptionInfo::Kind::BOOL)
    {
      std::cout << "bool" << std::endl;
      std::cout << "  values:" << std::endl;
      const auto& values = std::get<OptionInfo::Bool>(info.values);
      std::cout << "  + current:   " << (values.cur ? "true" : "false")
                << std::endl;
      std::cout << "  + default:   " << (values.dflt ? "true" : "false")
                << std::endl;
    }
    else if (info.kind == OptionInfo::Kind::NUMERIC)
    {
      std::cout << "numeric" << std::endl;
      std::cout << "  values:" << std::endl;
      const auto& values = std::get<OptionInfo::Numeric>(info.values);
      std::cout << "  + current:   " << values.dflt << std::endl;
      std::cout << "  + default:   " << values.cur << std::endl;
      std::cout << "  + min:       " << values.min << std::endl;
      std::cout << "  + max:       " << values.max << std::endl;
    }
    else
    {
      std::cout << "modes" << std::endl;
      std::cout << "  values:" << std::endl;
      const auto& values = std::get<OptionInfo::Mode>(info.values);
      std::cout << "  + current:   " << values.dflt << std::endl;
      std::cout << "  + default:   " << values.cur << std::endl;
      std::cout << "  + modes:     {";
      for (size_t i = 0, n = values.modes.size(); i < n; ++i)
      {
        std::cout << (i > 0 ? "," : "") << " " << values.modes[i];
      }
      std::cout << " }" << std::endl;
    }
    std::cout << "  description: " << info.description << std::endl;
    std::cout << std::endl;
  }
}
