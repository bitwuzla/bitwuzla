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

  static void print(std::ostream& os, const Node& node);
  static void print(std::ostream& os, const Type& type);

  static void print_formula(std::ostream& os,
                            const backtrack::AssertionView& assertions);

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

namespace printer {

/** Struct to set maximum printing depth of nodes via stream manipulator. */
struct set_depth
{
  set_depth(size_t depth) : d_depth(depth) {}
  size_t depth() const { return d_depth; }

 private:
  size_t d_depth;
};

std::ostream& operator<<(std::ostream& ostream, const set_depth& d);

}  // namespace printer

}  // namespace bzla
#endif
