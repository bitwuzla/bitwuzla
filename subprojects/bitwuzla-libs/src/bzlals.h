#ifndef BZLALS__BZLALS_H
#define BZLALS__BZLALS_H

#include <cstdint>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace bzlabv {
class BitVector;
}

namespace bzlarng {
class RNG;
}

namespace bzlatest {
class TestBzlaLs;
}

namespace bzlals {

struct BzlaLsMove;
class BitVectorDomain;
class BitVectorNode;

class BzlaLs
{
  friend class ::bzlatest::TestBzlaLs;

 public:
  using NodesIdTable = std::vector<std::unique_ptr<BitVectorNode>>;
  using ParentsSet   = std::unordered_set<uint32_t>;
  using ParentsMap   = std::unordered_map<uint32_t, ParentsSet>;

  enum Result
  {
    SAT = 10,
    UNSAT = 20,
    UNKNOWN = 0,
  };

  enum OperatorKind
  {
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

  struct
  {
    uint64_t d_nprops   = 0;
    uint64_t d_nupdates = 0;
    uint64_t d_nmoves   = 0;

    uint64_t d_nprops_inv  = 0;
    uint64_t d_nprops_cons = 0;

    uint64_t d_nconf = 0;

#ifndef NDEBUG
    struct
    {
      uint64_t d_add     = 0;
      uint64_t d_and     = 0;
      uint64_t d_ashr    = 0;
      uint64_t d_concat  = 0;
      uint64_t d_extract = 0;
      uint64_t d_eq      = 0;
      uint64_t d_ite     = 0;
      uint64_t d_mul     = 0;
      uint64_t d_not     = 0;
      uint64_t d_sext    = 0;
      uint64_t d_shl     = 0;
      uint64_t d_shr     = 0;
      uint64_t d_slt     = 0;
      uint64_t d_udiv    = 0;
      uint64_t d_ult     = 0;
      uint64_t d_urem    = 0;
      uint64_t d_xor     = 0;
    } d_ninv;
    struct
    {
      uint64_t d_add     = 0;
      uint64_t d_and     = 0;
      uint64_t d_ashr    = 0;
      uint64_t d_concat  = 0;
      uint64_t d_extract = 0;
      uint64_t d_eq      = 0;
      uint64_t d_ite     = 0;
      uint64_t d_mul     = 0;
      uint64_t d_not     = 0;
      uint64_t d_sext    = 0;
      uint64_t d_shl     = 0;
      uint64_t d_shr     = 0;
      uint64_t d_slt     = 0;
      uint64_t d_udiv    = 0;
      uint64_t d_ult     = 0;
      uint64_t d_urem    = 0;
      uint64_t d_xor     = 0;
    } d_ncons;
#endif
  } d_statistics;

  BzlaLs(uint64_t max_nprops, uint64_t max_nupdates, uint32_t seed = 1234);
  ~BzlaLs();

  void set_max_nprops(uint64_t max) { d_max_nprops = max; }
  void set_max_nupdates(uint64_t max) { d_max_nupdates = max; }

  uint32_t mk_node(uint32_t size);
  uint32_t mk_node(OperatorKind kind,
                   uint32_t size,
                   const std::vector<uint32_t>& children);
  uint32_t mk_indexed_node(OperatorKind kind,
                           uint32_t size,
                           uint32_t child0,
                           const std::vector<uint32_t>& indices);

  uint32_t mk_node(const ::bzlabv::BitVector& assignment,
                   const BitVectorDomain& domain);
  uint32_t mk_node(OperatorKind kind,
                   const BitVectorDomain& domain,
                   const std::vector<uint32_t>& children);
  uint32_t mk_indexed_node(OperatorKind kind,
                           const BitVectorDomain& domain,
                           uint32_t child0,
                           const std::vector<uint32_t>& indices);

  uint32_t invert_node(uint32_t id);

  const ::bzlabv::BitVector& get_assignment(uint32_t id) const;
  void set_assignment(uint32_t id, const ::bzlabv::BitVector& assignment);
  const BitVectorDomain& get_domain(uint32_t node) const;
  // void set_domain(uint32_t node, const BitVectorDomain& domain);

  /** Fix domain bit of given node at index 'idx' to 'value'. */
  void fix_bit(uint32_t id, uint32_t idx, bool value);

  void register_root(uint32_t root);
  bool all_roots_sat() const { return d_roots.empty(); }
  uint32_t get_num_roots_unsat() const { return d_roots.size(); }

  // TODO: incremental case:
  //       - we need to be able to unregister roots (assumptions)
  //       - we might want to exclude nodes that are not in the formula from
  //         cone updates

  uint32_t get_arity(uint32_t id) const;
  uint32_t get_child(uint32_t id, uint32_t idx) const;

  Result move();

  void set_log_level(uint32_t level) { d_log_level = level; }

 private:
  BitVectorNode* get_node(uint32_t id) const;
  bool is_leaf_node(const BitVectorNode* node) const;
  bool is_root_node(const BitVectorNode* node) const;
  void update_roots(uint32_t id);
  uint64_t update_cone(BitVectorNode* node,
                       const ::bzlabv::BitVector& assignment);
  BzlaLsMove select_move(BitVectorNode* root,
                         const ::bzlabv::BitVector& t_root);

  std::unique_ptr<::bzlarng::RNG> d_rng;

  NodesIdTable d_nodes;
  std::unordered_set<uint32_t> d_roots;
  ParentsMap d_parents;

  std::unique_ptr<::bzlabv::BitVector> d_one;

  uint32_t d_log_level = 0;

  uint64_t d_max_nprops   = 0;
  uint64_t d_max_nupdates = 0;

  uint32_t d_seed;
};

}  // namespace bzlals
#endif
