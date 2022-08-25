#ifndef BZLA_TYPE_MANAGER_H_INCLUDED
#define BZLA_TYPE_MANAGER_H_INCLUDED

#include <memory>
#include <unordered_set>
#include <vector>

#include "type/type_data.h"

namespace bzla::type {

class Type;

class TypeManager
{
  friend class TypeData;

 public:
  /** Create boolean type. */
  Type mk_bool_type();

  /** Create bit-vector type of size `size`. */
  Type mk_bv_type(uint64_t size);

  /**
   * Create floating-point type with exponent size `exp_size` and significand
   * size `sig_size`.
   */
  Type mk_fp_type(uint64_t exp_size, uint64_t sig_size);

  /** Create rounding mode type. */
  Type mk_rm_type();

  /** Create array type with index type `index` and element type `elem`. */
  Type mk_array_type(const Type& index, const Type& elem);

  /**
   * Create function type with codomain `types[:-1]` and domain `types[-1]`.
   *
   * Note: Last type in `types` corresponds to function domain type.
   */
  Type mk_fun_type(const std::vector<Type>& types);

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
   * Garbage collect given type data.
   *
   * Travers type data structure and deletes all unused type data nodes.
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

}  // namespace bzla::type

#endif
