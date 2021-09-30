#ifndef BZLALS__GMP_MPZ_H
#define BZLALS__GMP_MPZ_H

#include <gmpxx.h>

#include <cstdint>

namespace bzla {

/**
 * A GMP mpz_t wrapper.
 * We use this to avoid having to include gmp headers in header files.
 */
struct GMPMpz
{
  /** Construct a zero-initialized GMP value. */
  GMPMpz() { mpz_init(d_mpz); }
  /** Copy constructor. */
  GMPMpz(const GMPMpz& other) { mpz_init_set(d_mpz, other.d_mpz); }
  /**
   * Construct a GMP value from string, given in the specified base.
   * base: 2 for binary, 10 for decimal, 16 for hexadecimal
   */
  GMPMpz(uint64_t size, const std::string& value, uint32_t base)
  {
    mpz_init_set_str(d_mpz, value.c_str(), base);
    /* BitVector asserts that given string must fit into bv after conversion.
     * However, we still need to normalize negative values. Negative values are
     * represented as "-xxx" (where xxx is the binary representation of the
     * absolute value of 'value') in GMP when created from mpz_init_set_str. */
    mpz_fdiv_r_2exp(d_mpz, d_mpz, size);
  }
  /** Construct a GMP value from given uint64 value. */
  GMPMpz(uint64_t size, uint64_t value, bool sign = false)
  {
    if (sign)
    {
      mpz_init_set_si(d_mpz, value);
    }
    else
    {
      mpz_init_set_ui(d_mpz, value);
    }
    mpz_fdiv_r_2exp(d_mpz, d_mpz, size);
  }

  /** Destructor. */
  ~GMPMpz() { mpz_clear(d_mpz); }

  /** Copy assignment operator. */
  GMPMpz& operator=(const GMPMpz& other)
  {
    mpz_set(d_mpz, other.d_mpz);
    return *this;
  }
  /** The GMP integer value. */
  mpz_t d_mpz;
};

}  // namespace bzla
#endif
