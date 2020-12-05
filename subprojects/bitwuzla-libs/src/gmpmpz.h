#ifndef BZLALS__GMP_MPZ_H
#define BZLALS__GMP_MPZ_H

#include <gmpxx.h>

#include <cstdint>

namespace bzlals {

/**
 * A GMP mpz_t wrapper.
 * We use this to avoid having to include gmp headers in header files.
 */
struct GMPMpz
{
  /** Construct a zero-initialized GMP value. */
  GMPMpz() { mpz_init(d_mpz); }
  /** Construct a GMP value from given binary string. */
  GMPMpz(const std::string& value)
  {
    mpz_init_set_str(d_mpz, value.c_str(), 2);
  }
  /** Construct a GMP value from given uint64 value. */
  GMPMpz(uint64_t size, uint64_t value)
  {
    mpz_init_set_ui(d_mpz, value);
    mpz_fdiv_r_2exp(d_mpz, d_mpz, size);
  }

  /** Destructor. */
  ~GMPMpz() { mpz_clear(d_mpz); }

  /** The GMP integer value. */
  mpz_t d_mpz;
};

}
#endif
