#ifndef BZLA_TYPE_H_INCLUDED
#define BZLA_TYPE_H_INCLUDED

#include <cstdint>
#include <vector>

namespace bzla::type {

class TypeData;
class TypeManager;

class Type
{
  friend class TypeManager;

 public:
  Type() = default;
  ~Type();
  Type(const Type& other);
  Type& operator=(const Type& other);
  Type(Type&& other);
  Type& operator=(Type&& other);

  /** Check whether this is boolean type. */
  bool is_bool() const;

  /** Check whether this is bit-vector type. */
  bool is_bv() const;

  /** Check whether this is floating-point type. */
  bool is_fp() const;

  /** Check whether this is rounding mode type. */
  bool is_rm() const;

  /** Check whether this is an array type. */
  bool is_array() const;

  /** Check whether this is a function type. */
  bool is_fun() const;

  /** Return size of bit-vector type. */
  uint64_t get_bv_size() const;

  /** Return exponent size of floating-point type. */
  uint64_t get_fp_exp_size() const;

  /** Return significand size of floating-point type. */
  uint64_t get_fp_sig_size() const;

  /** Return index type of array type. */
  const Type& get_array_index() const;

  /** Return element type of array type. */
  const Type& get_array_element() const;

  /**
   * Return codomain and domain types of function type.
   *
   * Last type in vector is domain type.
   */
  const std::vector<Type>& get_fun_types() const;

  /** Return id of type. */
  uint64_t get_id() const;

  /** Check whether Type is a null type. */
  bool is_null() const;

  bool operator==(const Type& other) const;
  bool operator!=(const Type& other) const;

 private:
  Type(TypeData* d);

  TypeData* d_data = nullptr;
};

}  // namespace bzla::type

namespace std {

template <>
struct hash<bzla::type::Type>
{
  size_t operator()(const bzla::type::Type& type) const;
};

template <>
struct hash<bzla::type::Type*>
{
  size_t operator()(const bzla::type::Type* type) const;
};

}  // namespace std

#endif
