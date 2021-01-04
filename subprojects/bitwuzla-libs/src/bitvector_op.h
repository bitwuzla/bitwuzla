#ifndef BZLALS__BITVECTOR_OP_H
#define BZLALS__BITVECTOR_OP_H

#include "bitvector.h"
#include "bitvector_domain.h"

namespace bzlals {

class BitVectorOp
{
 public:
  /* Constructor. */
  BitVectorOp(uint32_t size)
      : d_assignment(BitVector::mk_zero(size)), d_domain(BitVectorDomain(size))
  {
  }
  BitVectorOp(const BitVector& assignment, const BitVectorDomain& domain)
      : d_assignment(assignment), d_domain(domain)
  {
  }
  /* Destructor. */
  virtual ~BitVectorOp() {}

  virtual bool is_invertible(const BitVector& t, uint32_t pos_x) = 0;
  BitVectorOp*& operator[](uint32_t pos) const;
  uint32_t get_arity() const { return 2; }

 protected:
  BitVector d_assignment;
  BitVectorDomain d_domain;
  std::unique_ptr<BitVectorOp*[]> d_children = nullptr;
};

class BitVectorAdd : public BitVectorOp
{
 public:
  BitVectorAdd(uint32_t size);
  BitVectorAdd(const BitVector& assignment, const BitVectorDomain& domain);
  bool is_invertible(const BitVector& t, uint32_t pos_x);
};

}  // namespace bzlals
#endif
