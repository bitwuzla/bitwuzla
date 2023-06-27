/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_TYPE_TYPE_DATA_H_INCLUDED
#define BZLA_TYPE_TYPE_DATA_H_INCLUDED

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace bzla {

class Type;

namespace type {

class TypeManager;

class TypeData
{
  friend TypeManager;

 public:
  enum class Kind
  {
    BOOL,
    BV,
    FP,
    RM,
    ARRAY,
    FUN,
    UNINTERPRETED,
  };

  TypeData() = delete;
  ~TypeData();

  /**
   * @return The type id.
   */
  uint64_t get_id() const;

  /**
   * @return The type kind.
   */
  Kind get_kind() const;

  /**
   * Return the types for function and array types.
   *
   * @return The vector of stored types.
   */
  const std::vector<Type>& get_types() const;

  /**
   * Return the symbol for uninterpreted types.
   *
   * @return The symbol.
   */
  const std::optional<std::string>& get_symbol() const;

  /**
   * @return The size of a bit-vector type.
   */
  uint64_t get_bv_size() const;

  /**
   * @return The exponent size of a floating-point type.
   */
  uint64_t get_fp_exp_size() const;

  /**
   * @return The significand size of a floating-point type.
   */
  uint64_t get_fp_sig_size() const;

  /** Increase the reference count by one. */
  void inc_ref();

  /**
   * Decrease the reference count by one.
   *
   * If reference count becomes zero, this type data object will be
   * automatically garbage collected.
   */
  void dec_ref();

 private:
  /** Constructor. */
  TypeData(TypeManager* mgr, Kind kind, const std::vector<Type>& types = {});
  /** Constructor for creating bit-vector type data. */
  TypeData(TypeManager* mgr, uint64_t size);
  /** Constructor for creating floating-point type data. */
  TypeData(TypeManager* mgr, uint64_t exp_size, uint64_t sig_size);
  /** Constructor for uninterpreted type data. */
  TypeData(TypeManager* mgr,
           const std::optional<std::string>& symbol = std::nullopt);

  /** Pointer to type manager that owns this object. */
  TypeManager* d_mgr = nullptr;
  /** Type id. */
  uint64_t d_id = 0;
  /** Type kind. */
  Kind d_kind;
  /** Reference count. */
  uint32_t d_refs = 0;

  /**
   * Variant that either stores the
   * (1) size of a bit-vector type (for Kind::BV)
   * (2) exponent and significand size of a floating-point type (for Kind::FP)
   * (3) types for array and function types (for Kind::ARRAY, Kind::FUN).
   * (4) the symbol for uninterpreted types (Kind::UNINTERPRETED)
   */
  std::variant<uint64_t,
               std::pair<uint64_t, uint64_t>,
               std::vector<Type>,
               std::optional<std::string>>
      d_data;
};

/**
 * Hash struct used for hash consing type data.
 */
struct TypeDataHash
{
  static constexpr std::array<size_t, 4> s_primes = {
      333444569u, 76891121u, 456790003u, 111130391u};
  size_t operator()(const TypeData* d) const;
};

/**
 * Comparison struct used for hash consing type data.
 */
struct TypeDataKeyEqual
{
  bool operator()(const TypeData* d0, const TypeData* d1) const;
};

}  // namespace type
}  // namespace bzla
#endif
