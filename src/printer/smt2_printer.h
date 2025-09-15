/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PRINTER_PRINTER_H_INCLUDED
#define BZLA_PRINTER_PRINTER_H_INCLUDED

#include <ostream>

#include "node/node.h"
#include "node/unordered_node_ref_map.h"

namespace bzla {

namespace backtrack {
class AssertionView;
}

class Smt2Printer
{
 public:
  static void print(std::ostream& os, const Node& node);
  static void print(std::ostream& os, const Type& type);

  /**
   * Print given assetions to given stream.
   * @param os         The output stream.
   * @param assertions The assertions.
   */
  static void print_formula(std::ostream& os,
                            const backtrack::AssertionView& assertions);
  static void print_formula(std::ostream& os,
                            const std::vector<Node>& assertions);

 private:
  /**
   * Helper to print a node.
   * @param os         The output stream.
   * @param def_map    Map of expressions that shared across assertions to
   *                   symbols (to be printed as define-fun).
   * @param let_map    Map of expressions that are shared across expressions
   *                   with a binder scope or assertion (to be printed as let).
   * @param max_depth  The printing cutoff depth. Maximum depth to traversal
   *                   depth of `node` while printing.
   * @param no_lets    True if expressions should not be letified when printing.
   */
  static void print(std::ostream& os,
                    const Node& node,
                    node::unordered_node_ref_map<std::string>& def_map,
                    node::unordered_node_ref_map<std::string>& let_map,
                    size_t max_depth,
                    bool no_lets);

  /**
   * Helper to letify and print a node.
   * @param os         The output stream.
   * @param def_map    Map of expressions that shared across assertions to
   *                   symbols (to be printed as define-fun).
   * @param let_map    Map of expressions that are shared across expressions
   *                   with a binder scope or assertion (to be printed as let).
   * @param max_depth  The printing cutoff depth. Maximum depth to traversal
   *                   depth of `node` while printing.
   * @param no_lets    True if expressions should not be letified when printing.
   */
  static void letify(std::ostream& os,
                     const Node& node,
                     node::unordered_node_ref_map<std::string>& def_map,
                     node::unordered_node_ref_map<std::string>& let_map,
                     size_t max_depth,
                     bool no_lets);

  static void print_symbol(std::ostream& os, const Node& node);
};

}  // namespace bzla
#endif
