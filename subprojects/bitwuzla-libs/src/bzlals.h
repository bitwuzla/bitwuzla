#ifndef BZLALS__BZLALS_H
#define BZLALS__BZLALS_H

#include <cstdint>

#include "bitvector.h"
#include "bitvector_op.h"

namespace bzlals {

class BzlaLsMove
{
 public:
  BzlaLsMove(uint64_t nprops, BitVectorOp* input, BitVector assignment)
      : d_nprops(nprops), d_input(input), d_assignment(assignment)
  {
  }

 private:
  uint64_t d_nprops;
  BitVectorOp* d_input;
  BitVector d_assignment;
};

}  // namespace bzlals
#endif
