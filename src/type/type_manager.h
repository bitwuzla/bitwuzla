/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_TYPE_TYPE_MANAGER_H_INCLUDED
#define BZLA_TYPE_TYPE_MANAGER_H_INCLUDED

#include <memory>
#include <optional>
#include <unordered_set>
#include <vector>

#include "type/type_data.h"

namespace bzla {

class Type;

namespace type {

class TypeManager
{
  friend TypeData;

 public:
  ~TypeManager();

  /**
   * @return Boolean type.
   */
  Type mk_bool_type();

  /**
   * Create bit-vector type.
   *
   * @param size Size of the bit-vector type.
   * @return Bit-vector type of given size.
   */
  Type mk_bv_type(uint64_t size);

  /**
   * Create floating-point type.
   *
   * @param exp_size Exponent size.
   * @param sig_size Significand size.
   * @return Floating-point type of given format.
   */
  Type mk_fp_type(uint64_t exp_size, uint64_t sig_size);

  /**
   * @return Rounding mode type.
   */
  Type mk_rm_type();

  /**
   * Create array type.
   *
   * @param index Index type.
   * @param element Element type.
   * @return Array type of given index and element type.
   */
  Type mk_array_type(const Type& index, const Type& elem);

  /**
   * Create function type.
   *
   * @param types Domain types and codomain type of function with the codomain
   *              type being the last element of the vector.
   * @return Function type of given domain and codomain types.
   */
  Type mk_fun_type(const std::vector<Type>& types);

  /**
   * Create uninterpreted type.
   * @param symbol The symbol of the uninterpreted type.
   * @return The uninterpreted type.
   */
  Type mk_uninterpreted_type(
      const std::optional<std::string>& symbol = std::nullopt);

 private:
  /** Initialize type data. */
  void init_id(TypeData* d);

  /** Helper function to check whether type data already exists. */
  TypeData* find_or_create(TypeData* d);

  /** Find or create new boolean, rounding mode, array, or function type. */
  TypeData* find_or_create_type(TypeData::Kind kind,
                                const std::vector<Type>& types = {});

  /** Find or create new bit-vector type. */
  TypeData* find_or_create_bv_type(uint64_t size);

  /** Find or create new floating-point type. */
  TypeData* find_or_create_fp_type(uint64_t exp_size, uint64_t sig_size);

  /**
   * Garbage collect type data.
   *
   * @note This will recursively delete all type data objects for which the
   *       reference count becomes zero.
   *
   * @param d Type data to delete.
   */
  void garbage_collect(TypeData* d);

  /** Type id counter. */
  uint64_t d_type_id_counter = 1;

  /** Indicates whether type manager is in garbage collection mode. */
  bool d_in_gc_mode = false;

  /** Maps type id-1 to type data and stores all created type data. */
  std::vector<std::unique_ptr<TypeData>> d_node_data;

  /** Cache used for hash consing type data. */
  std::unordered_set<TypeData*, TypeDataHash, TypeDataKeyEqual> d_unique_types;
};

}  // namespace type
}  // namespace bzla
#endif
