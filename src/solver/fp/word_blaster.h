#ifndef BZLA_SOLVER_FP_WORD_BLASTER_H_INCLUDED
#define BZLA_SOLVER_FP_WORD_BLASTER_H_INCLUDED

#include <unordered_map>
#include <vector>

#include "node/node.h"
#include "node/node_ref_vector.h"
#include "solver/fp/floating_point.h"

/* -------------------------------------------------------------------------- */

namespace bzla {
namespace fp {

class SymFpuSymTraits;

template <bool T>
class SymFpuSymBV;
class SymFpuSymRM;
class SymFpuSymProp;

class WordBlaster
{
 public:
  WordBlaster();
  ~WordBlaster();

  Node word_blast(const Node& node);
  Node get_word_blasted_node(const Node& node);
  void get_introduced_ufs(node::node_ref_vector& ufs);
  void add_additional_assertions();

 private:
  using SymUnpackedFloat = ::symfpu::unpackedFloat<SymFpuSymTraits>;
  using UnpackedFloatMap = std::unordered_map<Node, SymUnpackedFloat>;
  using SymFpuSymRMMap   = std::unordered_map<Node, SymFpuSymRM>;
  using SymFpuSymPropMap = std::unordered_map<Node, SymFpuSymProp>;
  using PackedFloatMap   = std::unordered_map<Node, SymFpuSymBV<false>>;
  using SymSBVMap        = std::unordered_map<Node, SymFpuSymBV<true>>;
  using SymUBVMap        = std::unordered_map<Node, SymFpuSymBV<false>>;

  struct Internal;

  const Node& min_max_uf(const Node& node);
  const Node& sbv_ubv_uf(const Node& node);

  std::unique_ptr<Internal> d_internal;

  std::unordered_map<Type, Node> d_min_max_uf_map;

  std::unordered_map<std::pair<Type, Type>, Node> d_sbv_ubv_uf_map;

  std::vector<Node> d_additional_assertions;
};

/* -------------------------------------------------------------------------- */
}  // namespace fp
}  // namespace bzla

#endif
