#ifndef BZLA_PRINTER_PRINTER_H_INCLUDED
#define BZLA_PRINTER_PRINTER_H_INCLUDED

#include <ostream>
#include <unordered_map>

#include "node/node.h"
#include "node/unordered_node_ref_map.h"

namespace bzla {

class Printer
{
 public:
  /** std::ios_base index for setting maximum print depth. */
  static int32_t s_stream_index_maximum_depth;

  static void print(std::ostream& os, const Node& node);
  static void print(std::ostream& os, const Type& type);

 private:
  static void print(std::ostream& os,
                    const Node& node,
                    node::unordered_node_ref_map<std::string>& let_map,
                    size_t max_depth);

  static void letify(std::ostream& os,
                     const Node& node,
                     node::unordered_node_ref_map<std::string>& let_map,
                     size_t max_depth);

  static void print_symbol(std::ostream& os, const Node& node);
};

}  // namespace bzla
#endif
