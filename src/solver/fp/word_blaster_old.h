#ifndef BZLA_SOLVER_FP_WORD_BLASTER_OLD_H_INCLUDED
#define BZLA_SOLVER_FP_WORD_BLASTER_OLD_H_INCLUDED

extern "C" {
#include "bzlabv.h"
#include "bzlanode.h"
#include "bzlasort.h"
}

#include <unordered_map>
#include <vector>

#include "solver/fp/floating_point.h"

namespace bzla {
namespace fp {

class SymFpuSymTraitsOld;

/* -------------------------------------------------------------------------- */

// FIXME: temporary
struct BzlaSortHashFunction
{
  size_t operator()(BzlaSortId sort) const { return sort; }
};

// FIXME: temporary
struct BzlaSortPairHashFunction
{
  size_t operator()(const std::pair<BzlaSortId, BzlaSortId> &p) const
  {
    return p.first * 333444569u + p.second * 76891121u;
  }
};

// FIXME: temporary
struct BzlaNodeHashFunction
{
  size_t operator()(BzlaNode *exp) const { return bzla_node_hash_by_id(exp); }
};

/* -------------------------------------------------------------------------- */

template <bool T>
class SymFpuSymBVOld;
class SymFpuSymRMOld;
class SymFpuSymPropOld;

class WordBlasterOld
{
 public:
  WordBlasterOld(Bzla *bzla);
  ~WordBlasterOld();

  BzlaNode *word_blast(BzlaNode *node);
  BzlaNode *get_word_blasted_node(BzlaNode *node);
  void get_introduced_ufs(std::vector<BzlaNode *> &ufs);
  void add_additional_assertions();

  Bzla *get_bzla() { return d_bzla; }

  static void set_s_bzla(Bzla *bzla);

 private:
  using SymUnpackedFloat = ::symfpu::unpackedFloat<SymFpuSymTraitsOld>;
  using UnpackedFloatMap =
      std::unordered_map<BzlaNode *, SymUnpackedFloat, BzlaNodeHashFunction>;
  using SymFpuSymRMMap =
      std::unordered_map<BzlaNode *, SymFpuSymRMOld, BzlaNodeHashFunction>;
  using SymFpuSymPropMap =
      std::unordered_map<BzlaNode *, SymFpuSymPropOld, BzlaNodeHashFunction>;
  using PackedFloatMap =
      std::unordered_map<BzlaNode *, SymFpuSymBVOld<false>, BzlaNodeHashFunction>;
  using SymSBVMap =
      std::unordered_map<BzlaNode *, SymFpuSymBVOld<true>, BzlaNodeHashFunction>;
  using SymUBVMap =
      std::unordered_map<BzlaNode *, SymFpuSymBVOld<false>, BzlaNodeHashFunction>;

  struct Internal;

  BzlaNode *min_max_uf(BzlaNode *node);
  BzlaNode *sbv_ubv_uf(BzlaNode *node);

  std::unique_ptr<Internal> d_internal;

  std::unordered_map<BzlaSortId, BzlaNode *, BzlaSortHashFunction>
      d_min_max_uf_map;

  std::unordered_map<std::pair<BzlaSortId, BzlaSortId>,
                     BzlaNode *,
                     BzlaSortPairHashFunction>
      d_sbv_ubv_uf_map;

  std::vector<BzlaNode *> d_additional_assertions;
  Bzla *d_bzla;
};

}  // namespace fp
}  // namespace bzla

#endif
