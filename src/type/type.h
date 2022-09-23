#ifndef BZLA_TYPE_TYPE_H_INCLUDED
#define BZLA_TYPE_TYPE_H_INCLUDED

#include <cstdint>
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
   * @return The index type of this array type.
   */
  const Type& array_index() const;

  /**
   * @return The element type of this array type.
   */
  const Type& array_element() const;

  /**
   * @return The codomain types and domain type of this function type.
   * @note Last element in vector is domain type.
   */
  const std::vector<Type>& fun_types() const;

  /**
   * @return The id of this type.
   */
  uint64_t id() const;

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
  Type(type::TypeData* d);

  /** Type payload */
  type::TypeData* d_data = nullptr;
};

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
