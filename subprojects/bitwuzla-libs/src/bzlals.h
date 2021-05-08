#ifndef BZLALS__BZLALS_H
#define BZLALS__BZLALS_H

#include <cstdint>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "bitvector.h"
#include "bitvector_node.h"

namespace bzlals {

class RNG;

struct BzlaLsMove;

class BzlaLs
{
 public:
  using ParentsMap =
      std::unordered_map<BitVectorNode*, std::unordered_set<BitVectorNode*>>;
  BzlaLs(uint64_t max_nprops);
  void register_root(BitVectorNode* root);
  void init_parents();
  const ParentsMap& get_parents() { return d_parents; }

 private:
  BzlaLsMove select_move(BitVectorNode* root, const BitVector& t_root);

  std::vector<BitVectorNode*> d_roots;
  ParentsMap d_parents;
  std::unique_ptr<RNG> d_rng;
  BitVector d_one;
  uint64_t d_max_nprops;
  uint64_t d_nprops = 0;
  uint64_t d_nmoves = 0;
};

}  // namespace bzlals
#endif
