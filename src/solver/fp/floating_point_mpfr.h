/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_FP_FLOATING_POINT_MPFR_H_INCLUDED
#define BZLA_SOLVER_FP_FLOATING_POINT_MPFR_H_INCLUDED

#include <mpfr.h>

#include <array>
#include <memory>

#include "bv/bitvector.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "type/type.h"

namespace bzla {

class NodeManager;

/* -------------------------------------------------------------------------- */

class FloatingPointMPFR
{
  friend fp::WordBlaster;

 public:
  /**
   * Convenience helper to split an IEEE-754 bit-vector into its components
   * (sign, exponent, significand).
   * @param type The floating-point type.
   * @param bv   The IEEE-754 bit-vector representation of a floating-point.
   * @param sign The output parameter for the sign bit.
   * @param exp  The output parameter for the exponent bit-vector.
   * @param sig  The output parameter for the significand bit-vector.
   */
  static void ieee_bv_as_bvs(const Type &type,
                             const BitVector &bv,
                             BitVector &sign,
                             BitVector &exp,
                             BitVector &sig);
  /**
   * Create a floating-point of given type converted from the given real
   * constant represented as a decimal string w.r.t. to the given rounding
   * mode.
   * @param type The type.
   * @param rm   The rounding mode.
   * @param real A string representing the real to convert from.
   * @return A floating-point of given type converted from the given real.
   */
  static FloatingPointMPFR from_real(NodeManager &nm,
                                     const Type &type,
                                     const RoundingMode rm,
                                     const std::string &real);
  /**
   * Create a floating-point of given type converted from the given rational
   * constant represented as a numerator and denominator decimal string w.r.t.
   * to the given rounding mode.
   * @param type The type.
   * @param rm  The rounding mode.
   * @param num A string representing the numerator of the rational.
   * @param den A string representing the denominator of the rational.
   * @return A floating-point of given type converted from the given rational.
   */
  static FloatingPointMPFR from_rational(NodeManager &nm,
                                         const Type &type,
                                         const RoundingMode rm,
                                         const std::string &num,
                                         const std::string &den);

  /**
   * Create a floating-point of given type representing zero.
   * @param type The type.
   * @param sign False for +zero and true for -zero.
   * @return A floating-point of given type representing zero.
   */
  static FloatingPointMPFR fpzero(const Type &type, bool sign);

  /**
   * Create a floating-point of given type representing infinity.
   * @param type The type.
   * @param sign False for +inf and true for -inf.
   * @return A floating-point of given type representing infinity.
   */
  static FloatingPointMPFR fpinf(const Type &type, bool sign);

  /**
   * Create a floating-point of given type representing nan.
   * @param type The type.
   * @return A floating-point of given type representing nan.
   */
  static FloatingPointMPFR fpnan(const Type &type);

  /**
   * Create a floating-point from its IEEE-754 bit-vector representation given
   * as sign bit, exponent bits, and significand bits.
   * @param sign A bit-vector of size 1 representing the sign bit.
   * @param exp A bit-vector representing the exponent.
   * @param sig A bit-vector representing the significand.
   * @return The floating-point corresponding to the given IEEE-754 bit-vector
   *         representation.
   */
  static FloatingPointMPFR fpfp(NodeManager &nm,
                                const BitVector &sign,
                                const BitVector &exp,
                                const BitVector &sig);
  /**
   * Constructor.
   * Create new nullary floating-point of given type.
   * @param type The floating-point type.
   */
  FloatingPointMPFR(const Type &type);
  /**
   * Constructor.
   * Create new nullary floating-point of given size.
   * @param size The floating-point size.
   */
  FloatingPointMPFR(const FloatingPointTypeInfo &size);
  // /**
  //  * Constructor.
  //  * Create new floating-point of given type, wrapping the given symFPU
  //  * unpacked float.
  //  * @param type The floating-point type.
  //  * @param uf The symFPU unpacked float.
  //  */
  // FloatingPointMPFR(const Type &type, const UnpackedFloat &uf);
  /**
   * Constructor.
   * Create new floating-point of given type from an IEEE-754 bit-vector.
   * @param type The type.
   * @param bv The IEEE-754 bit-vector representation of the floating-point.
   */
  FloatingPointMPFR(const Type &type, const BitVector &bv);
  /**
   * Constructor.
   * Create new floating-point of given type converted from the given
   * floating-point constant w.r.t. to the given rounding mode.
   * @param type The type.
   * @param rm The rounding mode.
   * @param fp The floating-point to convert from.
   */
  FloatingPointMPFR(const Type &type,
                    const RoundingMode rm,
                    const FloatingPointMPFR &fp);
  /**
   * Constructor.
   * Create new floating-point of given type converted from the given
   * bit-vector constant (interpreted as signed or unsigned machine integer)
   * w.r.t. to the given rounding mode.
   * @param type The type.
   * @param rm The rounding mode.
   * @param bv The bit-vector to convert from (interpreted as signed if `sign`
   *           is true).
   * @param sign True if `bv` is to be interpreted as signed machine integer,
   *             else unsigned.
   */
  FloatingPointMPFR(const Type &type,
                    const RoundingMode rm,
                    const BitVector &bv,
                    bool sign);

  /** Copy constructor. */
  FloatingPointMPFR(const FloatingPointMPFR &other);
  /** Copy assignment. */
  FloatingPointMPFR &operator=(const FloatingPointMPFR &other);
  /** Destructor. */
  ~FloatingPointMPFR();

  /** @return The exponent size of this floating-point. */
  uint64_t get_exponent_size() const;
  /** @return The significand size of this floating-point. */
  uint64_t get_significand_size() const;

  /** @return The size of this floating-point. */
  FloatingPointTypeInfo *size() const;
  // /** @return The wrapped symFPU unpacked float. */
  // UnpackedFloat *unpacked() const;
  // /**
  //  * Set the wrapped symFPU unpacked float.
  //  * @param uf The unpacked float to wrap.
  //  */
  // void set_unpacked(const UnpackedFloat &uf);

  /** @return The hash value of this floating-point. */
  size_t hash() const;

  /**
   * Get a string representation of this floating-point value.
   * @param bv_format The output format for bit-vector values: `2` for binary,
   *                  and `10` for decimal.
   * @note Hexadecimal bv format is not supported, as it requires mixing binary
   *       and hex format (hex values are only printed in hex if their size
   *       is divisible by 4).
   * @return The string representation.
   */
  std::string str(uint8_t bv_format = 2) const;

  std::string to_real_str() const;

  /**
   * Equality comparison operator.
   * @note This compares for "syntactic" equality, i.e., if the underlying
   *       floating-point representation represents the same value, this will
   *       return true. Consequently, this will NOT return true when comparing
   *       NaN with any other value than NaN.
   * @param other The floating-point to compare this floating-point to.
   */
  bool operator==(const FloatingPointMPFR &other) const;
  /**
   * Disequality comparison operator.
   * @note This is dual to `operator==` and compares for "syntactic" equality.
   * @param other The floating-point to compare this floating-point to.
   */
  bool operator!=(const FloatingPointMPFR &other) const;

  /** @return True if this floating-point represents a zero value. */
  bool fpiszero() const;

  /** @return True if this floating-point represents a normal value. */
  bool fpisnormal() const;

  /** @return True if this floating-point represents a subnormal value. */
  bool fpissubnormal() const;

  /** @return True if this floating-point represents a nan value. */
  bool fpisnan() const;

  /** @return True if this floating-point represents a infinite value. */
  bool fpisinf() const;

  /** @return True if this floating-point represents a negative value. */
  bool fpisneg() const;

  /** @return True if this floating-point represents a positive value. */
  bool fpispos() const;

  /** @return True if this floating-point is equal to `fp`. */
  bool fpeq(const FloatingPointMPFR &fp) const;

  /** @return True if this floating-point is less than `fp`. */
  bool fplt(const FloatingPointMPFR &fp) const;

  /** @return True if this floating-point is less than or equal `fp`. */
  bool fple(const FloatingPointMPFR &fp) const;

  /** @return True if this floating-point is less than `fp`. */
  bool fpgt(const FloatingPointMPFR &fp) const;

  /** @return True if this floating-point is less than or equal `fp`. */
  bool fpge(const FloatingPointMPFR &fp) const;

  /**
   * Create a floating-point representing the absolute value of this
   * floating-point.
   * @return The absolute value of this floating-point.
   */
  FloatingPointMPFR fpabs() const;

  /**
   * Create a floating-point representing the negation of this
   * floating-point.
   * @return The negation of this floating-point.
   */
  FloatingPointMPFR fpneg() const;

  /**
   * Create a floating-point representing the square root of this
   * floating-point w.r.t. to the given rounding mode.
   * @param rm The rounding mode.
   * @return The square root of the given floating-point.
   */
  FloatingPointMPFR fpsqrt(const RoundingMode rm) const;

  /**
   * Create a floating-point representing the round-to-integral of this
   * floating-point w.r.t. to the given rounding mode.
   * @param rm The rounding mode.
   * @param fp The floating-point.
   * @return The round-to-integral of the given floating-point.
   */
  FloatingPointMPFR fprti(const RoundingMode rm) const;

  /**
   * Create a floating-point representing the remainder operation of this and
   * the given floating-point.
   * @param fp The other operand.
   * @return The result of the remainder operation.
   */
  FloatingPointMPFR fprem(const FloatingPointMPFR &fp) const;

  /**
   * Create a floating-point representing the addition of this and the  given
   * floating-point w.r.t. given rounding mode.
   * @param rm The rounding mode.
   * @param fp The other operand.
   * @return The addition of the operands.
   */
  FloatingPointMPFR fpadd(const RoundingMode rm,
                          const FloatingPointMPFR &fp) const;

  /**
   * Create a floating-point representing the multiplication of this and the
   * given floating-point w.r.t. to the given rounding mode.
   * @param rm The rounding mode.
   * @param fp The other operand.
   * @return The multiplication of the operands.
   */
  FloatingPointMPFR fpmul(const RoundingMode rm,
                          const FloatingPointMPFR &fp) const;

  /**
   * Create a floating-point representing the division of this and the given
   * floating-point constants w.r.t. to the given rounding mode.
   * @param rm The rounding mode.
   * @param fp The other operand.
   * @return The result of the division.
   */
  FloatingPointMPFR fpdiv(const RoundingMode rm,
                          const FloatingPointMPFR &fp) const;

  /**
   * Create a floating-point representing the fused multiplication and addition
   * operation of this and the given floating-point constants w.r.t. to the
   * given rounding mode.
   * @param rm The rounding mode.
   * @param fp0 The operand to the multiplication.
   * @param fp1 The operand to the addition.
   * @return The result of the division.
   */
  FloatingPointMPFR fpfma(const RoundingMode rm,
                          const FloatingPointMPFR &fp0,
                          const FloatingPointMPFR &fp1) const;

  /** @return The IEEE-754 bit-vector representation of  this floating-point. */
  BitVector as_bv() const;

 private:
  static inline std::array<uint32_t, 6> s_hash_primes = {
      333444569u, 111130391u, 22237357u, 33355519u, 456790003u, 76891121u};

  /**
   * Helper to create a floating-point from its unpacked bit-vector
   * representation given as sign bit, exponent bits, and significand bits.
   *
   * This unpacked representation accounts for additional bits required for the
   * exponent to allow subnormals to be normalized.
   *
   * @note This should NOT be used to create a literal from its IEEE-754
   *       bit-vector representation -- for this, fpfp() is to be used.
   *
   * @param sign A bit-vector of size 1 representing the sign bit.
   * @param exp  A bit-vector representing the unpacked exponent.
   * @param sig  A bit-vector representing the unpacked significand.
   * @return The floating-point corresponding to the given unpacked bit-vector
   *         representation.
   */
  static FloatingPointMPFR from_unpacked(NodeManager &nm,
                                         const BitVector &sign,
                                         const BitVector &exp,
                                         const BitVector &sig);
  /**
   * Helper for constructors from real and rational strings.
   * @param type The floating-point type.
   * @param rm   The rounding mode.
   * @param num  The string denoting the numerator.
   * @param den  The string denoting the denominator, nullptr for from real.
   * @return The constructed floating-point.
   */
  static FloatingPointMPFR convert_from_rational_aux(NodeManager &nm,
                                                     const Type &type,
                                                     const RoundingMode rm,
                                                     const char *num,
                                                     const char *den);

  std::unique_ptr<FloatingPointTypeInfo> d_size;
  mpfr_t d_mpfr;
};

std::ostream &operator<<(std::ostream &out, const FloatingPointMPFR &fp);

/* -------------------------------------------------------------------------- */
}  // namespace bzla

namespace std {

/** Hash function. */
template <>
struct hash<bzla::FloatingPointMPFR>
{
  size_t operator()(const bzla::FloatingPointMPFR &fp) const;
};

}  // namespace std

#endif
