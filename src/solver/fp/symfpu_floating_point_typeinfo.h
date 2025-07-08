/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_FP_SYMFPU_FLOATING_POINT_TYPEINFO_H_INCLUDED
#define BZLA_SOLVER_FP_SYMFPU_FLOATING_POINT_TYPEINFO_H_INCLUDED

#include "type/type.h"

namespace bzla {

/* -------------------------------------------------------------------------- */

/**
 * Wrapper for floating-point types providing the interface required by symFPU.
 */
class SymFPUFloatingPointTypeInfo
{
 public:
  /**
   * Constructor.
   * @param type The Bitwuzla floating-point type.
   */
  SymFPUFloatingPointTypeInfo(const Type& type);
  /**
   * Constructor.
   * @param esize The size of the exponent.
   * @param ssize The size of the significand.
   */
  SymFPUFloatingPointTypeInfo(uint32_t esize, uint32_t ssize);
  /** Copy constructor. */
  SymFPUFloatingPointTypeInfo(const SymFPUFloatingPointTypeInfo& other);
  /** Destructor. */
  ~SymFPUFloatingPointTypeInfo();

  /** @return The associated floating-point type. */
  const Type& type() const;

  /**
   * Get a string representation of this floating-point type info.
   * @return The string representation.
   */
  std::string str() const;

  /* symFPU interface --------------------------------------------- */

  /** @return The exponent size of this format. */
  uint32_t exponentWidth() const { return d_esize; }
  /** @return The significand size of this format (incl. the sign bit). */
  uint32_t significandWidth() const { return d_ssize; }
  /**
   * @return The bit-width of the IEEE-754 representation of a floating-point
   *         of this size.
   */
  uint32_t packedWidth() const { return d_esize + d_ssize; }
  /**
   * @return The exponent size of this format in the IEEE-754 representation
   *         (same as exponentWidth()).
   */
  uint32_t packedExponentWidth() const { return d_esize; }
  /**
   * @return The actual significand size of this format in the IEEE-754
   *         representation (without sign bit).
   */
  uint32_t packedSignificandWidth() const { return d_ssize - 1; }

 private:
  /** The size of exponent. */
  uint32_t d_esize;
  /** The size of significand. */
  uint32_t d_ssize;
  /** The wrapped floating-point type. */
  Type d_type;
};

std::ostream& operator<<(std::ostream& out,
                         const SymFPUFloatingPointTypeInfo& type);

/* -------------------------------------------------------------------------- */
}  // namespace bzla

#endif
