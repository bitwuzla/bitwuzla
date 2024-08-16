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

#include <string>
#include <vector>

#include "bitblast/aig/aig_node.h"

namespace bzla::bitblast::aig {

class AigPrinter
{
 public:
  /** Add output to print. */
  void add_output(const AigNode& output);

  /** Assign symbol to AIG node `n`. */
  void symbol(const AigNode& n, const std::string& symbol);

  /** Write AIG to file in AIGER format. */
  void write_aiger(const std::string& filename);

  /** Write AIG to file in DIMACS format*/
  void write_cnf(const std::string& filename);

 private:
  std::vector<AigNode> d_outputs;
  std::unordered_map<AigNode, std::string> d_symbols;
};

}  // namespace bzla::bitblast::aig
#endif
