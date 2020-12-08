#include "bitvector.h"

#include <cassert>
#include <sstream>

#include "gmpmpz.h"
#include "gmprandstate.h"
#include "rng.h"

namespace bzlals {

namespace {
bool
is_bin_str(std::string str)
{
  for (const char& c : str)
  {
    if (c != '0' && c != '1') return false;
  }
  return true;
}

#if !defined(__GNUC__) && !defined(__clang__)
static uint32_t
clz_limb(uint32_t nbits_per_limb, mp_limb_t limb)
{
  uint32_t w;
  mp_limb_t mask;
  mp_limb_t one = 1u;
  for (w = 0, mask = 0; w < nbits_per_limb; ++w)
  {
    mask += (one << w);
    if ((limb & ~mask) == 0) break;
  }
  return nbits_per_limb - 1 - w;
}
#endif
}  // namespace

BitVector
BitVector::mk_true()
{
  return mk_one(1);
}

BitVector
BitVector::mk_false()
{
  return mk_zero(1);
}

BitVector
BitVector::mk_zero(uint32_t size)
{
  return BitVector(size);
}

BitVector
BitVector::mk_one(uint32_t size)
{
  return BitVector(size, 1);
}

BitVector
BitVector::mk_ones(uint32_t size)
{
  BitVector res = BitVector::mk_one(size);
  mpz_mul_2exp(res.d_val->d_mpz, res.d_val->d_mpz, size);
  mpz_sub_ui(res.d_val->d_mpz, res.d_val->d_mpz, 1);
  return res;
}

BitVector
BitVector::mk_min_signed(uint32_t size)
{
  BitVector res = BitVector::mk_zero(size);
  res.set_bit(size - 1, true);
  return res;
}

BitVector
BitVector::mk_max_signed(uint32_t size)
{
  BitVector res = BitVector::mk_ones(size);
  res.set_bit(size - 1, false);
  return res;
}

BitVector
BitVector::bvite(const BitVector& c, const BitVector& t, const BitVector& e)
{
  assert(t.d_size == e.d_size);
  // TODO
}

BitVector::BitVector() : d_size(0), d_val(nullptr) {}

BitVector::BitVector(uint32_t size) : d_size(size)
{
  assert(size > 0);
  d_val.reset(new GMPMpz());
}

BitVector::BitVector(uint32_t size, const RNG& rng) : BitVector(size)
{
  mpz_urandomb(d_val->d_mpz, rng.d_gmp_state->d_gmp_randstate, size);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, size);
}

// BitVector::BitVector(uint32_t size, RNG& rng, const BitVector& from, const
// BitVector& to, bool is_signed = false){} BitVector::BitVector(uint32_t size,
// RNG& rng, uint32_t idx_hi, uint32_t idx_lo){}

BitVector::BitVector(uint32_t size, const std::string& value) : d_size(size)
{
  assert(value.size() <= size);
  assert(is_bin_str(value));
  d_val.reset(new GMPMpz(value));
}

BitVector::BitVector(uint32_t size, uint64_t value) : d_size(size)
{
  assert(size > 0);
  d_val.reset(new GMPMpz(size, value));
}

BitVector::BitVector(const BitVector& other)
{
  d_size = other.d_size;
  d_val.reset(new GMPMpz());
  mpz_set(d_val->d_mpz, other.d_val->d_mpz);
}

BitVector::~BitVector() {}

BitVector&
BitVector::operator=(const BitVector& other)
{
  if (&other == this) return *this;
  d_size = other.d_size;
  d_val.reset(new GMPMpz());
  mpz_set(d_val->d_mpz, other.d_val->d_mpz);
  return *this;
}

std::string
BitVector::to_string() const
{
  std::stringstream res;
  char* tmp     = mpz_get_str(0, 2, d_val->d_mpz);
  uint32_t n    = strlen(tmp);
  uint32_t diff = d_size - n;
  assert(n <= d_size);
  res << std::string(diff, '0') << tmp;
  assert(res.str().size() == d_size);
  free(tmp);
  return res.str();
}

uint64_t
BitVector::to_uint64() const
{
  assert(d_size <= 64);
  return mpz_get_ui(d_val->d_mpz);
}

int32_t
BitVector::compare(const BitVector& other) const
{
  assert(d_size == other.d_size);
  return mpz_cmp(d_val->d_mpz, other.d_val->d_mpz);
}

int32_t
BitVector::signed_compare(const BitVector& other) const
{
  assert(d_size == other.d_size);

  uint32_t msb_a = get_bit(d_size - 1);
  uint32_t msb_b = other.get_bit(d_size - 1);

  if (msb_a && !msb_b)
  {
    return -1;
  }
  if (!msb_a && msb_b)
  {
    return 1;
  }
  return compare(other);
}

bool
BitVector::get_bit(uint32_t idx) const
{
  return mpz_tstbit(d_val->d_mpz, idx);
}

void
BitVector::set_bit(uint32_t idx, bool value)
{
  if (value)
  {
    mpz_setbit(d_val->d_mpz, idx);
  }
  else
  {
    mpz_clrbit(d_val->d_mpz, idx);
  }
}

void
BitVector::flip_bit(uint32_t idx)
{
  mpz_combit(d_val->d_mpz, idx);
}

bool
BitVector::is_true() const
{
  if (d_size > 1) return false;
  return get_bit(0);
}

bool
BitVector::is_false() const
{
  if (d_size > 1) return false;
  return !get_bit(0);
}

bool
BitVector::is_zero() const
{
  return mpz_cmp_ui(d_val->d_mpz, 0) == 0;
}

bool
BitVector::is_ones() const
{
  uint32_t n = mpz_size(d_val->d_mpz);
  if (n == 0) return false;  // zero
  uint64_t m = d_size / mp_bits_per_limb;
  if (d_size % mp_bits_per_limb) m += 1;
  if (m != n) return false;  // less limbs used than expected, not ones
  uint64_t max = mp_bits_per_limb == 64 ? UINT64_MAX : UINT32_MAX;
  for (uint32_t i = 0; i < n - 1; ++i)
  {
    mp_limb_t limb = mpz_getlimbn(d_val->d_mpz, i);
    if (((uint64_t) limb) != max) return false;
  }
  mp_limb_t limb = mpz_getlimbn(d_val->d_mpz, n - 1);
  if (d_size == (uint32_t) mp_bits_per_limb) return ((uint64_t) limb) == max;
  m = mp_bits_per_limb - d_size % mp_bits_per_limb;
  return ((uint64_t) limb) == (max >> m);
}

bool
BitVector::is_one() const
{
  return mpz_cmp_ui(d_val->d_mpz, 1) == 0;
}

bool
BitVector::is_min_signed() const
{
  if (mpz_scan1(d_val->d_mpz, 0) != d_size - 1) return false;
  return true;
}

bool
BitVector::is_max_signed() const
{
  if (mpz_scan0(d_val->d_mpz, 0) != d_size - 1) return false;
  return true;
}

bool
BitVector::is_uadd_overflow(const BitVector& other) const
{
  // TODO
  return false;
}

bool
BitVector::is_umul_overflow(const BitVector& other) const
{
  // TODO
  return false;
}

uint32_t
BitVector::count_trailing_zeros() const
{
  uint32_t res = mpz_scan1(d_val->d_mpz, 0);
  if (res > d_size) res = d_size;
  return res;
}

uint32_t
BitVector::count_leading_zeros() const
{
  count_leading(true);
}

uint32_t
BitVector::count_leading_ones() const
{
  count_leading(false);
}

BitVector
BitVector::bvneg() const
{
  BitVector res = bvnot();
  mpz_add_ui(res.d_val->d_mpz, res.d_val->d_mpz, 1);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvnot() const
{
  BitVector res(d_size);
  mpz_com(res.d_val->d_mpz, d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvinc() const
{
  BitVector res(d_size);
  mpz_add_ui(res.d_val->d_mpz, d_val->d_mpz, 1);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvdec() const
{
  BitVector res(d_size);
  mpz_sub_ui(res.d_val->d_mpz, d_val->d_mpz, 1);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvredand() const
{
  return is_ones() ? mk_true() : mk_false();
}

BitVector
BitVector::bvredor() const
{
  mp_limb_t limb;
  for (size_t i = 0, n = mpz_size(d_val->d_mpz); i < n; ++i)
  {
    limb = mpz_getlimbn(d_val->d_mpz, i);
    if (((uint64_t) limb) != 0) return mk_true();
  }
  return mk_false();
}

BitVector
BitVector::bvadd(const BitVector& other) const
{
  assert(d_size == other.d_size);
  BitVector res(d_size);
  mpz_add(res.d_val->d_mpz, d_val->d_mpz, other.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvsub(const BitVector& other) const
{
  assert(d_size == other.d_size);
  BitVector res(d_size);
  mpz_sub(res.d_val->d_mpz, d_val->d_mpz, other.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvand(const BitVector& other) const
{
  assert(d_size == other.d_size);
  BitVector res(d_size);
  mpz_and(res.d_val->d_mpz, d_val->d_mpz, other.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvimplies(const BitVector& other) const
{
  assert(d_size == other.d_size);
  assert(d_size == 1);
  assert(other.d_size == 1);
  return is_false() || other.is_true() ? mk_true() : mk_false();
}

BitVector
BitVector::bvnand(const BitVector& other) const
{
  assert(d_size == other.d_size);
  BitVector res(d_size);
  mpz_and(res.d_val->d_mpz, d_val->d_mpz, other.d_val->d_mpz);
  mpz_com(res.d_val->d_mpz, res.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvnor(const BitVector& other) const
{
  assert(d_size == other.d_size);
  BitVector res(d_size);
  mpz_ior(res.d_val->d_mpz, d_val->d_mpz, other.d_val->d_mpz);
  mpz_com(res.d_val->d_mpz, res.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvor(const BitVector& other) const
{
  assert(d_size == other.d_size);
  BitVector res(d_size);
  mpz_ior(res.d_val->d_mpz, d_val->d_mpz, other.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvxnor(const BitVector& other) const
{
  assert(d_size == other.d_size);
  BitVector res(d_size);
  mpz_xor(res.d_val->d_mpz, d_val->d_mpz, other.d_val->d_mpz);
  mpz_com(res.d_val->d_mpz, res.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvxor(const BitVector& other) const
{
  assert(d_size == other.d_size);
  BitVector res(d_size);
  mpz_xor(res.d_val->d_mpz, d_val->d_mpz, other.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bveq(const BitVector& other) const
{
  assert(d_size == other.d_size);
  return mpz_cmp(d_val->d_mpz, other.d_val->d_mpz) == 0 ? mk_true()
                                                        : mk_false();
}

BitVector
BitVector::bvne(const BitVector& other) const
{
  assert(d_size == other.d_size);
  return mpz_cmp(d_val->d_mpz, other.d_val->d_mpz) != 0 ? mk_true()
                                                        : mk_false();
}

BitVector
BitVector::bvult(const BitVector& other) const
{
  assert(d_size == other.d_size);
  return mpz_cmp(d_val->d_mpz, other.d_val->d_mpz) < 0 ? mk_true() : mk_false();
}

BitVector
BitVector::bvule(const BitVector& other) const
{
  assert(d_size == other.d_size);
  return mpz_cmp(d_val->d_mpz, other.d_val->d_mpz) <= 0 ? mk_true()
                                                        : mk_false();
}

BitVector
BitVector::bvugt(const BitVector& other) const
{
  assert(d_size == other.d_size);
  return mpz_cmp(d_val->d_mpz, other.d_val->d_mpz) > 0 ? mk_true() : mk_false();
}

BitVector
BitVector::bvuge(const BitVector& other) const
{
  return mpz_cmp(d_val->d_mpz, other.d_val->d_mpz) >= 0 ? mk_true()
                                                        : mk_false();
}

BitVector
BitVector::bvslt(const BitVector& other) const
{
  assert(d_size == other.d_size);
  bool msb       = get_bit(d_size - 1);
  bool msb_other = other.get_bit(d_size - 1);
  if (msb && !msb_other)
  {
    return mk_true();
  }
  if (!msb && msb_other)
  {
    return mk_false();
  }
  return bvult(other);
}

BitVector
BitVector::bvsle(const BitVector& other) const
{
  assert(d_size == other.d_size);
  bool msb       = get_bit(d_size - 1);
  bool msb_other = other.get_bit(d_size - 1);
  if (msb && !msb_other)
  {
    return mk_true();
  }
  if (!msb && msb_other)
  {
    return mk_false();
  }
  return bvule(other);
}

BitVector
BitVector::bvsgt(const BitVector& other) const
{
  assert(d_size == other.d_size);
  bool msb       = get_bit(d_size - 1);
  bool msb_other = other.get_bit(d_size - 1);
  if (msb && !msb_other)
  {
    return mk_false();
  }
  if (!msb && msb_other)
  {
    return mk_true();
  }
  return bvugt(other);
}

BitVector
BitVector::bvsge(const BitVector& other) const
{
  assert(d_size == other.d_size);
  bool msb       = get_bit(d_size - 1);
  bool msb_other = other.get_bit(d_size - 1);
  if (msb && !msb_other)
  {
    return mk_false();
  }
  if (!msb && msb_other)
  {
    return mk_true();
  }
  return bvuge(other);
}

BitVector
BitVector::bvshl(uint32_t shift) const
{
  BitVector res(d_size);
  if (shift >= d_size) return res;
  mpz_mul_2exp(res.d_val->d_mpz, d_val->d_mpz, shift);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvshl(const BitVector& other) const
{
  assert(d_size == other.d_size);
  uint32_t shift;
  if (other.shift_is_uint64(&shift))
  {
    return bvshl(shift);
  }
  return BitVector(d_size);
}

BitVector
BitVector::bvshr(uint32_t shift) const
{
  BitVector res(d_size);
  if (shift >= d_size) return res;
  mpz_fdiv_q_2exp(res.d_val->d_mpz, d_val->d_mpz, shift);
  return res;
}

BitVector
BitVector::bvshr(const BitVector& other) const
{
  assert(d_size == other.d_size);
  uint32_t shift;
  if (other.shift_is_uint64(&shift))
  {
    return bvshr(shift);
  }
  return BitVector(d_size);
}

BitVector
BitVector::bvashr(const BitVector& other) const
{
  assert(d_size == other.d_size);
  if (get_bit(d_size - 1))
  {
    return bvnot().bvshr(other).bvnot();
  }
  return bvshr(other);
}

BitVector
BitVector::bvmul(const BitVector& other) const
{
  assert(d_size == other.d_size);
  // TODO
}

BitVector
BitVector::bvudiv(const BitVector& other) const
{
  assert(d_size == other.d_size);
  // TODO
}

BitVector
BitVector::bvurem(const BitVector& other) const
{
  assert(d_size == other.d_size);
  // TODO
}

BitVector
BitVector::bvsdiv(const BitVector& other) const
{
  assert(d_size == other.d_size);
  // TODO
}

BitVector
BitVector::bvsrem(const BitVector& other) const
{
  assert(d_size == other.d_size);
  // TODO
}

BitVector
BitVector::bvconcat(const BitVector& other) const
{
  uint32_t size = d_size + other.d_size;
  BitVector res(size);
  mpz_mul_2exp(res.d_val->d_mpz, d_val->d_mpz, other.d_size);
  mpz_add(res.d_val->d_mpz, res.d_val->d_mpz, other.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, size);
  return res;
}

BitVector
BitVector::bvextract(uint32_t idx_hi, uint32_t idx_lo) const
{
  uint32_t size = idx_hi - idx_lo + 1;
  BitVector res(size);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, d_val->d_mpz, idx_hi + 1);
  mpz_fdiv_q_2exp(res.d_val->d_mpz, res.d_val->d_mpz, idx_lo);
  return res;
}

BitVector
BitVector::bvzext(uint32_t n) const
{
  // TODO
}

BitVector
BitVector::bvsext(uint32_t n) const
{
  // TODO
}

uint32_t
BitVector::count_leading(bool zeros) const
{
  uint32_t res = 0;
  mp_limb_t limb;

  uint32_t nbits_per_limb = mp_bits_per_limb;
  /* The number of bits that spill over into the most significant limb,
   * assuming that all bits are represented). Zero if the bit-width is a
   * multiple of n_bits_per_limb. */
  uint32_t nbits_rem = d_size % nbits_per_limb;
  /* The number of limbs required to represent the actual value.
   * Zero limbs are disregarded. */
  uint32_t n_limbs = get_limb(&limb, nbits_rem, zeros);
  if (n_limbs == 0) return d_size;
#if defined(__GNUC__) || defined(__clang__)
  res = nbits_per_limb == 64 ? __builtin_clzll(limb) : __builtin_clz(limb);
#else
  res = clz_limb(nbits_per_limb, limb);
#endif
  /* Number of limbs required when representing all bits. */
  uint32_t n_limbs_total = d_size / nbits_per_limb + 1;
  uint32_t nbits_pad     = nbits_per_limb - nbits_rem;
  res += (n_limbs_total - n_limbs) * nbits_per_limb - nbits_pad;
  return res;
}

uint32_t
BitVector::get_limb(void* limb, uint32_t nbits_rem, bool zeros) const
{
  mp_limb_t* gmp_limb = static_cast<mp_limb_t*>(limb);
  /* GMP normalizes the limbs, the left most (most significant) is never 0 */
  uint32_t i, n_limbs, n_limbs_total;
  mp_limb_t res = 0u, mask;

  n_limbs = mpz_size(d_val->d_mpz);

  /* for leading zeros */
  if (zeros)
  {
    *gmp_limb = n_limbs ? mpz_getlimbn(d_val->d_mpz, n_limbs - 1) : 0;
    return n_limbs;
  }

  /* for leading ones */
  n_limbs_total = d_size / mp_bits_per_limb + (nbits_rem ? 1 : 0);
  if (n_limbs != n_limbs_total)
  {
    /* no leading ones, simulate */
    *gmp_limb = nbits_rem ? ~(~((mp_limb_t) 0) << nbits_rem) : ~((mp_limb_t) 0);
    return n_limbs_total;
  }
  mask = ~((mp_limb_t) 0) << nbits_rem;
  for (i = 0; i < n_limbs; i++)
  {
    res = mpz_getlimbn(d_val->d_mpz, n_limbs - 1 - i);
    if (nbits_rem && i == 0)
    {
      res = res | mask;
    }
    res = ~res;
    if (res > 0) break;
  }
  *gmp_limb = res;
  return n_limbs - i;
}

bool
BitVector::shift_is_uint64(uint32_t* res) const
{
  if (d_size <= 64)
  {
    *res = to_uint64();
    return true;
  }

  uint32_t clz = count_leading_zeros();
  if (clz < d_size - 64) return false;

  BitVector shift = bvextract(clz < d_size ? d_size - 1 - clz : 0, 0);
  assert(shift.d_size <= 64);
  *res = shift.to_uint64();
  return true;
}

}  // namespace bzlals
