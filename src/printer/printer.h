#ifndef BZLA_PRINTER_PRINTER_H_INCLUDED
#define BZLA_PRINTER_PRINTER_H_INCLUDED

#include <ostream>
#include <unordered_map>

#include "node/node.h"

namespace bzla {

class Printer
{
 public:
  static void print(std::ostream& os, const Node& node);
  static void print(std::ostream& os, const Type& type);

 private:
  static void print(std::ostream& os,
                    const Node& node,
                    std::unordered_map<std::reference_wrapper<const Node>,
                                       std::string,
                                       std::hash<Node>>& let_map);

  static void letify(std::ostream& os,
                     const Node& node,
                     std::unordered_map<std::reference_wrapper<const Node>,
                                        std::string,
                                        std::hash<Node>>& let_map);

  static void print_symbol(std::ostream& os, const Node& node);
};

}  // namespace bzla
#endif
