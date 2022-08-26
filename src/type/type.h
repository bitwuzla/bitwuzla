#ifndef BZLA_TYPE_TYPE_H_INCLUDED
#define BZLA_TYPE_TYPE_H_INCLUDED

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
   * @return The size of this bit-vector type.
   */
  uint64_t get_bv_size() const;

  /**
   * @return The Exponent size of this floating-point type.
   */
  uint64_t get_fp_exp_size() const;

  /**
   * @return The significand size of this floating-point type.
   */
  uint64_t get_fp_sig_size() const;

  /**
   * @return The index type of this array type.
   */
  const Type& get_array_index() const;

  /**
   * @return The element type of this array type.
   */
  const Type& get_array_element() const;

  /**
   * @return The codomain types and domain type of this function type.
   * @note Last element in vector is domain type.
   */
  const std::vector<Type>& get_fun_types() const;

  /**
   * @return The id of this type.
   */
  uint64_t get_id() const;

  /**
   * @return True if this type is a null type.
   */
  bool is_null() const;

  /**
   * Syntactical equality operator.
   *
   * @param other The type to compare against.
   * @return True if this type and other are equal.
   */
  bool operator==(const Type& other) const;

  /**
   * Syntactical disequality operator.
   *
   * @param other The type to compare against.
   * @return True if this type and other are disequal.
   */
  bool operator!=(const Type& other) const;

 private:
  Type(TypeData* d);

  /** Type payload */
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
