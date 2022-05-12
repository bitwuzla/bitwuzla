#ifndef BZLA__BB_BITBLAST_H
#define BZLA__BB_BITBLAST_H

#include <cassert>
#include <cstddef>
#include <vector>

#include "bitvector.h"

namespace bzla::bb {

/**
 * Interface for providing bit-level operations used by the bit-blaster
 * interface.
 */
template <class T>
class BitInterface
{
 public:
  /** Create bit representing false. */
  T mk_false();
  /** Create bit representing true. */
  T mk_true();
  /** Create constant representing a bit. */
  T mk_bit();
  /** Create negation of bit `a`. */
  T mk_not(const T& a);
  /** Create logical and of bits `a` and `b`. */
  T mk_and(const T& a, const T& b);
  /** Create logical or of bits `a` and `b`. */
  T mk_or(const T& a, const T& b);
  /** Create equality of bits `a` and `b`. */
  T mk_iff(const T& a, const T& b);
  /** Create if-then-else over condition `c`, if branch `a` and then `b`. */
  T mk_ite(const T& c, const T& a, const T& b);
};

}  // namespace bzla::bb
#endif
