#ifndef BZLA_TYPE_TYPE_DATA_H_INCLUDED
#define BZLA_TYPE_TYPE_DATA_H_INCLUDED

#include <cstddef>
#include <cstdint>
#include <vector>

namespace bzla::type {

class Type;
class TypeManager;

class TypeData
{
  friend class TypeManager;

 public:
  enum class Kind
  {
    BOOL,
    BV,
    FP,
    RM,
    ARRAY,
    FUN
  };

  TypeData() = delete;
  ~TypeData();

  /** Return type id. */
  uint64_t get_id() const;

  /** Return type kind. */
  Kind get_kind() const;

  /** Return type vector (for array and function types). */
  const std::vector<Type>& get_types() const;

  /** Return size of bit-vector type. */
  uint64_t get_bv_size() const;

  /** Return exponent size of floating-point type. */
  uint64_t get_fp_exp_size() const;

  /** Return significand size of floating-point type. */
  uint64_t get_fp_sig_size() const;

  // Reference counting
  void inc_ref();
  void dec_ref();

 private:
  TypeData(TypeManager* mgr, Kind kind, const std::vector<Type>& types = {});
  TypeData(TypeManager* mgr, uint64_t size);
  TypeData(TypeManager* mgr, uint64_t exp_size, uint64_t sig_size);

  /** Pointer to type manager that owns this object. */
  TypeManager* d_mgr = nullptr;

  /** Type id. */
  uint64_t d_id = 0;
  /** Type kind. */
  Kind d_kind;
  /** Reference count. */
  uint32_t d_refs = 0;

  union
  {
    /** Size of bit-vector type. */
    uint64_t d_bv_size;
    struct
    {
      /** Exponent size of floating-point type. */
      uint64_t d_fp_exp_size;
      /** Significand size of floating-point type. */
      uint64_t d_fp_sig_size;
    };
    /** Types for array and function types. */
    std::vector<Type> d_types;
  };
};

struct TypeDataHash
{
  static constexpr size_t s_primes[4] = {
      333444569u, 76891121u, 456790003u, 111130391u};
  size_t operator()(const TypeData* d) const;
};

struct TypeDataKeyEqual
{
  bool operator()(const TypeData* d0, const TypeData* d1) const;
};

}  // namespace bzla::type

#endif
