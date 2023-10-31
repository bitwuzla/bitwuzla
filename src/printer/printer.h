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
#include <unordered_map>

#include "node/node.h"
#include "node/unordered_node_ref_map.h"

namespace bzla {

namespace backtrack {
class AssertionView;
}

class Printer
{
 public:
  /** std::ios_base index for setting maximum print depth. */
  static int32_t s_stream_index_maximum_depth;
  /** std::ios_base index for setting the number format of bit-vector values. */
  static int32_t s_stream_index_bv_format;

  static void print(std::ostream& os, const Node& node);
  static void print(std::ostream& os, const Type& type);

  /**
   * Print given assetions to given stream.
   * @param os         The output stream.
   * @param assertions The assertions.
   */
  static void print_formula(std::ostream& os,
                            const backtrack::AssertionView& assertions);

 private:
  static void print(std::ostream& os,
                    const Node& node,
                    node::unordered_node_ref_map<std::string>& def_map,
                    node::unordered_node_ref_map<std::string>& let_map,
                    size_t max_depth);

  static void letify(std::ostream& os,
                     const Node& node,
                     node::unordered_node_ref_map<std::string>& def_map,
                     node::unordered_node_ref_map<std::string>& let_map,
                     size_t max_depth);

  static void print_symbol(std::ostream& os, const Node& node);
};

namespace printer {

/**
 * The exception thrown when the printer encounters an unrecoverable error,
 * e.g., when symbols do not comply with a language standard.
 */
class Exception : public std::exception
{
 public:
  /**
   * Constructor.
   * @param msg The exception message.
   */
  Exception(const std::string& msg) : d_msg(msg) {}
  /**
   * Get the exception message.
   * @return The exception message.
   */
  const std::string& msg() const { return d_msg; }

  const char* what() const noexcept override { return d_msg.c_str(); }

 private:
  /** The exception message. */
  std::string d_msg;
};

/** Struct to set maximum printing depth of nodes via stream manipulator. */
struct set_depth
{
  /**
   * Constructor.
   * @param depth The maximum printing depth.
   */
  set_depth(size_t depth) : d_depth(depth) {}
  /** @return The configured maximum printing depth. */
  size_t depth() const { return d_depth; }

 private:
  /** The configured maximum printing depth. */
  size_t d_depth;
};

std::ostream& operator<<(std::ostream& ostream, const set_depth& d);

/** Struct to set bit-vector number format of nodes via stream manipulator. */
struct set_bv_format
{
  /**
   * Constructor.
   * @param format The number format: 2 for binary, 10 for decimal and 16 for
   *               hexadecimal.
   */
  set_bv_format(uint8_t format) : d_format(format) {}
  /** @return The configured format. */
  uint8_t format() const { return d_format; }

 private:
  /** The configured number format. */
  uint8_t d_format;
};

std::ostream& operator<<(std::ostream& ostream, const set_bv_format& f);

}  // namespace printer

}  // namespace bzla
#endif
