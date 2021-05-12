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
  using NodesIdTable = std::vector<std::unique_ptr<BitVectorNode>>;
  using ParentsMap = std::unordered_map<uint32_t, std::unordered_set<uint32_t>>;

  enum NodeKind
  {
    /* bit-vector variables and constants */
    CONST,
    /* operators */
    ADD,
    AND,
    ASHR,
    CONCAT,
    // DEC,
    EXTRACT,
    EQ,
    // IMPLIES,
    ITE,
    // INC,
    MUL,
    // NAND,
    // NE,
    // NEG,
    // NOR,
    NOT,
    // OR,
    // REDAND,
    // REDOR,
    // SDIV,
    SEXT,
    // SGT,
    // SGE,
    SHL,
    SHR,
    SLT,
    // SLE,
    // SREM,
    // SUB,
    UDIV,
    // UGT,
    // UGE,
    ULT,
    // ULE,
    UREM,
    // XNOR,
    XOR,
    // ZEXT,
  };

  BzlaLs(uint64_t max_nprops, uint32_t seed = 1234);

  uint32_t mk_node(NodeKind kind,
                   uint32_t size,
                   const std::vector<uint32_t>& children);
  uint32_t mk_indexed_node(NodeKind kind,
                           uint32_t size,
                           uint32_t child0,
                           const std::vector<uint32_t>& indices);

  uint32_t mk_node(NodeKind kind,
                   const BitVector& assignment,
                   const BitVectorDomain& domain,
                   const std::vector<uint32_t>& children);
  uint32_t mk_indexed_node(NodeKind kind,
                           const BitVector& assignment,
                           const BitVectorDomain& domain,
                           uint32_t child0,
                           const std::vector<uint32_t>& indices);

  // void set_assignment(uint32_t node, const BitVector& assignment);
  // void set_domain(uint32_t node, const BitVectorDomain& domain);

  void register_root(uint32_t root);

  const NodesIdTable& get_nodes() { return d_nodes; }

  const ParentsMap& get_parents() { return d_parents; }

 private:
  BzlaLsMove select_move(BitVectorNode* root, const BitVector& t_root);

  std::unique_ptr<RNG> d_rng;

  NodesIdTable d_nodes;
  std::vector<uint32_t> d_roots;
  ParentsMap d_parents;

  BitVector d_one;

  uint64_t d_max_nprops;
  uint64_t d_nprops = 0;
  uint64_t d_nmoves = 0;
  uint32_t d_seed;
};

}  // namespace bzlals
#endif
