/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PRINTER_BTOR2_PRINTER_H_INCLUDED
#define BZLA_PRINTER_BTOR2_PRINTER_H_INCLUDED

#include <ostream>

#include "node/node.h"

namespace bzla {

namespace backtrack {
class AssertionView;
}

class Btor2Printer
{
 public:
  /**
   * Print given assetions to given stream.
   * @param os         The output stream.
   * @param assertions The assertions.
   */
  static void print_formula(std::ostream& os,
                            const backtrack::AssertionView& assertions);
  static void print_formula(std::ostream& os,
                            const std::vector<Node>& assertions);
};

}  // namespace bzla
#endif
