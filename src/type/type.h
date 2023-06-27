/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_TYPE_TYPE_H_INCLUDED
#define BZLA_TYPE_TYPE_H_INCLUDED

#include <cstdint>
#include <optional>
#include <ostream>
#include <vector>

namespace bzla {

namespace type {
class TypeData;
class TypeManager;
}  // namespace type

class Type
{
  friend type::TypeManager;
  friend bool operator==(const Type& a, const Type& b);
  friend bool operator!=(const Type& a, const Type& b);

 public:
  Type() = default;
  ~Type();
  Type(const Type& other);
  Type& operator=(const Type& other);
  Type(Type&& other);
  Type& operator=(Type&& other);

  /**
   * @return True if this type is a Boolean type.
   */
  bool is_bool() const;

  /**
   * @return True if this type is a bit-vector type.
   */
  bool is_bv() const;

  /**
   * @return True if this type is a floating-point type.
   */
  bool is_fp() const;

  /**
   * @return True if this type is a rounding mode type.
   */
  bool is_rm() const;

  /**
   * @return True if this type is an array type.
   */
  bool is_array() const;

  /**
   * @return True if this type is a function type.
   */
  bool is_fun() const;

  /**
   * @return True if this type is an uninterpreted type.
   */
  bool is_uninterpreted() const;

  /**
   * @return The size of this bit-vector type.
   */
  uint64_t bv_size() const;

  /**
   * @return The Exponent size of this floating-point type.
   */
  uint64_t fp_exp_size() const;

  /**
   * @return The significand size of this floating-point type.
   */
  uint64_t fp_sig_size() const;

  /**
   * @return The size of the IEEE bit-vector representation of this
   *         floating-point type.
   */
  uint64_t fp_ieee_bv_size() const;

  /**
   * @return The index type of this array type.
   */
  const Type& array_index() const;

  /**
   * @return The element type of this array type.
   */
  const Type& array_element() const;

  /** @return The arity of this function type. */
  size_t fun_arity() const;

  /**
   * @return The domain types and codomain type of this function type.
   * @note Last element in vector is codomain type.
   */
  const std::vector<Type>& fun_types() const;

  /**
   * @return The symbol of this uninterpreted type if defined, and else an
   *         empty string.
   */
  const std::optional<std::string>& uninterpreted_symbol() const;

  /**
   * @return The id of this type.
   */
  uint64_t id() const;

  /**
   * @return True if this type is a null type.
   */
  bool is_null() const;

  /**
   * @return String representation of this type.
   */
  std::string str() const;

 private:
  Type(type::TypeData* d);

  /** Type payload */
  type::TypeData* d_data = nullptr;
};

/**
 * Syntactical equality operator.
 *
 * @param a The first type to compare.
 * @param b The second type to compare.
 * @return True if the types are equal.
 */
bool operator==(const Type& a, const Type& b);

/**
 * Syntactical disequality operator.
 *
 * @param a The first type to compare.
 * @param b The second type to compare.
 * @return True if the types are disequal.
 */
bool operator!=(const Type& a, const Type& b);

/** Print type to stream. */
std::ostream& operator<<(std::ostream& out, const Type& type);

}  // namespace bzla

namespace std {

template <>
struct hash<bzla::Type>
{
  size_t operator()(const bzla::Type& type) const;
};

template <>
struct hash<bzla::Type*>
{
  size_t operator()(const bzla::Type* type) const;
};

}  // namespace std

#endif
