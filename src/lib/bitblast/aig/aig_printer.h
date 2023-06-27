/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__BITBLAST_AIG_AIG_PRINTER_H
#define BZLA__BITBLAST_AIG_AIG_PRINTER_H

#include "bitblast/aig/aig_manager.h"

#include <vector>

namespace bzla::bb::aig {

class Smt2Printer
{
 public:
  static void print(std::stringstream& ss, const AigNode& n);
  static void print(std::stringstream& ss, const std::vector<AigNode>& bits);
};

}  // namespace bzla::bb::aig
#endif
