/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "ls/bv/bitvector_domain.h"

#include <algorithm>
#include <cassert>
#include <iostream>

#include "rng/rng.h"
#include "util/wheel_factorizer.h"

namespace bzla {
namespace ls {

/*----------------------------------------------------------------------------*/

BitVectorDomain::BitVectorDomain(uint64_t size)
    : d_lo(BitVector::mk_zero(size)), d_hi(BitVector::mk_ones(size))
{
}

BitVectorDomain::BitVectorDomain(const BitVector &lo, const BitVector &hi)
    : d_lo(lo), d_hi(hi)
{
  assert(lo.size() == hi.size());
  d_has_fixed_bits = !d_lo.is_zero() || !d_hi.is_ones();
}

BitVectorDomain::BitVectorDomain(const std::string &value)
{
  uint64_t size = value.size();
  assert(size > 0);
  std::string lo(value);
  std::string hi(value);
  std::replace(lo.begin(), lo.end(), 'x', '0');
  std::replace(hi.begin(), hi.end(), 'x', '1');
  d_lo             = BitVector(size, lo);
  d_hi             = BitVector(size, hi);
  d_has_fixed_bits = !d_lo.is_zero() || !d_hi.is_ones();
}

BitVectorDomain::BitVectorDomain(const BitVector &bv) : d_lo(bv), d_hi(bv)
{
  d_has_fixed_bits = true;
}

BitVectorDomain::BitVectorDomain(uint64_t size, uint64_t value)
    : BitVectorDomain(BitVector::from_ui(size, value))
{
}

BitVectorDomain::BitVectorDomain(const BitVectorDomain &other)
    : d_lo(other.d_lo), d_hi(other.d_hi)
{
  d_has_fixed_bits = other.d_has_fixed_bits;
  assert(d_has_fixed_bits == (!d_lo.is_zero() || !d_hi.is_ones()));
}

BitVectorDomain::~BitVectorDomain() {}

uint64_t
BitVectorDomain::size() const
{
  assert(!is_null());
  assert(d_lo.size() == d_hi.size());
  return d_lo.size();
}

bool
BitVectorDomain::is_valid() const
{
  assert(!is_null());
  return d_lo.bvnot().ibvor(d_hi).is_ones();
}

bool
BitVectorDomain::is_fixed() const
{
  assert(!is_null());
  return d_lo.compare(d_hi) == 0;
}

bool
BitVectorDomain::has_fixed_bits() const
{
  assert(!is_null());
  assert(is_valid());
  return d_has_fixed_bits;
}

bool
BitVectorDomain::has_fixed_bits_true() const
{
  assert(!is_null());
  assert(is_valid());
  return d_has_fixed_bits && !d_lo.is_zero();
}

bool
BitVectorDomain::has_fixed_bits_false() const
{
  assert(!is_null());
  assert(is_valid());
  return d_has_fixed_bits && !d_hi.is_ones();
}

bool
BitVectorDomain::has_fixed_bits_true_only() const
{
  assert(!is_null());
  assert(is_valid());
  if (!has_fixed_bits_true()) return false;
  BitVector lo_not = d_lo.bvnot();
  return lo_not.bvand(d_hi).compare(lo_not) == 0;
}

bool
BitVectorDomain::has_fixed_bits_false_only() const
{
  assert(!is_null());
  assert(is_valid());
  if (!has_fixed_bits_false()) return false;
  BitVector hi_not = d_hi.bvnot();
  return hi_not.bvor(d_lo).compare(hi_not) == 0;
}

bool
BitVectorDomain::is_fixed_bit(uint64_t idx) const
{
  assert(!is_null());
  assert(idx < size());
  return d_lo.bit(idx) == d_hi.bit(idx);
}

bool
BitVectorDomain::is_fixed_bit_true(uint64_t idx) const
{
  assert(!is_null());
  assert(idx < size());
  bool b = d_lo.bit(idx);
  if (!b) return false;
  return b == d_hi.bit(idx);
}

bool
BitVectorDomain::is_fixed_bit_false(uint64_t idx) const
{
  assert(!is_null());
  assert(idx < size());
  bool b = d_lo.bit(idx);
  if (b) return false;
  return b == d_hi.bit(idx);
}

void
BitVectorDomain::fix_bit(uint64_t idx, bool value)
{
  assert(!is_null());
  assert(idx < size());
  d_lo.set_bit(idx, value);
  d_hi.set_bit(idx, value);
  d_has_fixed_bits = true;
}

void
BitVectorDomain::fix(const BitVector &val)
{
  assert(!is_null());
  assert(val.size() == size());
  d_lo.iset(val);
  d_hi.iset(val);
  d_has_fixed_bits = true;
}

bool
BitVectorDomain::match_fixed_bits(const BitVector &bv) const
{
  assert(!is_null());
  return bv.bvand(d_hi).ibvor(d_lo).compare(bv) == 0;
}

BitVector
BitVectorDomain::get_copy_with_fixed_bits(const BitVector &bv) const
{
  assert(!is_null());
  return bv.bvand(d_hi).ibvor(d_lo);
}

BitVectorDomain &
BitVectorDomain::operator=(const BitVectorDomain &other)
{
  if (&other == this) return *this;
  assert(!other.is_null());
  d_lo             = other.d_lo;
  d_hi             = other.d_hi;
  d_has_fixed_bits = other.d_has_fixed_bits;
  return *this;
}

bool
BitVectorDomain::operator==(const BitVectorDomain &other) const
{
  assert(!is_null());
  assert(!other.is_null());
  return d_lo.compare(other.d_lo) == 0 && d_hi.compare(other.d_hi) == 0;
}

BitVectorDomain
BitVectorDomain::bvnot() const
{
  assert(!is_null());
  return BitVectorDomain(d_hi.bvnot(), d_lo.bvnot());
}

BitVectorDomain
BitVectorDomain::bvshl(const BitVector &shift) const
{
  assert(!is_null());
  assert(shift.size() == size());
  return BitVectorDomain(d_lo.bvshl(shift), d_hi.bvshl(shift));
}

BitVectorDomain
BitVectorDomain::bvshr(const BitVector &shift) const
{
  assert(!is_null());
  assert(shift.size() == size());
  return BitVectorDomain(d_lo.bvshr(shift), d_hi.bvshr(shift));
}

BitVectorDomain
BitVectorDomain::bvashr(const BitVector &shift) const
{
  assert(!is_null());
  assert(shift.size() == size());
  return BitVectorDomain(d_lo.bvashr(shift), d_hi.bvashr(shift));
}

BitVectorDomain
BitVectorDomain::bvconcat(const BitVector &bv) const
{
  assert(!is_null());
  return BitVectorDomain(d_lo.bvconcat(bv), d_hi.bvconcat(bv));
}

BitVectorDomain
BitVectorDomain::bvconcat(const BitVectorDomain &d) const
{
  assert(!is_null());
  return BitVectorDomain(d_lo.bvconcat(d.lo()), d_hi.bvconcat(d.hi()));
}

BitVectorDomain
BitVectorDomain::bvextract(uint64_t idx_hi, uint64_t idx_lo) const
{
  assert(!is_null());
  assert(idx_hi >= idx_lo);
  return BitVectorDomain(d_lo.bvextract(idx_hi, idx_lo),
                         d_hi.bvextract(idx_hi, idx_lo));
}

BitVector
BitVectorDomain::get_factor(RNG *rng,
                            const BitVector &num,
                            const BitVector &excl_min,
                            uint64_t limit) const
{
  WheelFactorizer wf(num, limit);
  std::vector<BitVector> factors;

  while (true)
  {
    const BitVector *fact = wf.next();
    if (!fact) break;
    factors.emplace_back(*fact);
    if (rng == nullptr) break;
  }

  /* Pick factor from stack. Random (combination) if 'rng' is given. */
  if (!factors.empty())
  {
    size_t n_factors = factors.size();
    if (rng)
    {
      /* To determine all possible combinations can be very expensive. We'll
       * try for a limited number of times, and if none matches, we return 0. */
      for (size_t cnt = 0; cnt < 1000; ++cnt)
      {
        /* number of factors to combine */
        size_t n = rng->pick<size_t>(1, n_factors);
        /* Move selected factors to front of the stack and combine.
         * This ensures that we don't pick a factor twice, e.g., 2 2 3 can be
         * combined into { 2, 3, 2*2, 2*3, 2*2*3 }. */
        BitVector mul(num.size());
        for (size_t i = 0; i < n; ++i)
        {
          size_t j = rng->pick<size_t>(i, n_factors - 1);
          if (i != j)
          {
            std::swap(factors[i], factors[j]);
          }
          if (!mul.is_zero())
          {
            assert(!factors[i].is_umul_overflow(mul));
            BitVector tmp = factors[i].bvmul(mul);
            if (tmp.compare(num) > 0)
            {
              continue;
            }
            mul.iset(tmp);
          }
          else
          {
            mul.iset(factors[i]);
          }
        }
        assert(!mul.is_null());
        if (mul.compare(excl_min) > 0 && match_fixed_bits(mul))
        {
          return mul;
        }
      }
    }
    else
    {
      assert(n_factors == 1);
      return factors[0];
    }
  }
  return BitVector();
}

std::string
BitVectorDomain::str() const
{
  assert(!is_null());
  std::string res(d_lo.str());
  std::string hi(d_hi.str());
  for (size_t i = 0, n = size(); i < n; ++i)
  {
    if (res[i] != hi[i])
    {
      if (res[i] == '0' && hi[i] == '1')
      {
        res[i] = 'x';
      }
      else
      {
        assert(res[i] == '1' && hi[i] == '0');
        res[i] = 'i';
      }
    }
  }
  return res;
}

/*----------------------------------------------------------------------------*/

BitVectorDomainGenerator::BitVectorDomainGenerator(
    const BitVectorDomain &domain)
    : BitVectorDomainGenerator(domain, nullptr, domain.d_lo, domain.d_hi)
{
}

BitVectorDomainGenerator::BitVectorDomainGenerator(
    const BitVectorDomain &domain, const BitVector &min, const BitVector &max)
    : BitVectorDomainGenerator(domain, nullptr, min, max)
{
}

BitVectorDomainGenerator::BitVectorDomainGenerator(
    const BitVectorDomain &domain, RNG *rng)
    : BitVectorDomainGenerator(domain, rng, domain.d_lo, domain.d_hi)
{
}

BitVectorDomainGenerator::BitVectorDomainGenerator(
    const BitVectorDomain &domain,
    RNG *rng,
    const BitVector &min,
    const BitVector &max)
    : d_domain(domain), d_rng(rng)
{
  uint64_t cnt          = 0;
  uint64_t size         = domain.size();
  const BitVector &hi   = d_domain.d_hi;
  const BitVector &lo   = d_domain.d_lo;
  const BitVector &mmin = lo.compare(min) <= 0 ? min : lo;
  const BitVector &mmax = hi.compare(max) >= 0 ? max : hi;

  d_bits.reset(nullptr);
  d_bits_min.reset(nullptr);
  d_bits_max.reset(nullptr);

  for (size_t i = 0; i < size; ++i)
  {
    if (!d_domain.is_fixed_bit(i)) cnt += 1;
  }

  if (cnt && mmin.compare(hi) <= 0 && mmax.compare(lo) >= 0)
  {
    assert(mmin.compare(lo) >= 0);
    assert(mmax.compare(hi) <= 0);

    /* Set unconstrained bits to the minimum value that corresponds to a
     * generated value >= mmin. */
    d_bits_min.reset(new BitVector(BitVector::mk_zero(cnt)));
    for (uint64_t i = 0, j = 0, j0 = 0; i < size; ++i)
    {
      uint64_t idx_i = size - 1 - i;
      bool bit       = mmin.bit(idx_i);
      if (!d_domain.is_fixed_bit(idx_i))
      {
        assert(j < cnt);
        d_bits_min->set_bit(cnt - 1 - j, bit);
        if (!bit) j0 = j;
        j += 1;
      }
      else if (d_domain.is_fixed_bit_true(idx_i) && !bit)
      {
        break;
      }
      else if (d_domain.is_fixed_bit_false(idx_i) && bit)
      {
        assert(j > 0);
        assert(!d_bits_min->bit(cnt - j0 - 1));
        d_bits_min->set_bit(cnt - j0 - 1, true);
        for (uint64_t k = j0 + 1; k < cnt; ++k)
        {
          d_bits_min->set_bit(cnt - 1 - k, false);
        }
        break;
      }
    }

    /* Set unconstrained bits to the maximum value that corresponds to a
     * generated value <= mmax. */
    d_bits_max.reset(new BitVector(BitVector::mk_ones(cnt)));
    for (uint64_t i = 0, j = 0, j0 = 0; i < size; ++i)
    {
      uint64_t idx_i = size - 1 - i;
      bool bit       = mmax.bit(idx_i);
      if (!d_domain.is_fixed_bit(idx_i))
      {
        assert(j < cnt);
        d_bits_max->set_bit(cnt - 1 - j, bit);
        if (bit) j0 = j;
        j += 1;
      }
      else if (d_domain.is_fixed_bit_true(idx_i) && !bit)
      {
        assert(j > 0);
        assert(d_bits_max->bit(cnt - j0 - 1));
        d_bits_max->set_bit(cnt - j0 - 1, false);
        for (uint64_t k = j0 + 1; k < cnt; ++k)
        {
          d_bits_max->set_bit(cnt - 1 - k, true);
        }
        break;
      }
      else if (d_domain.is_fixed_bit_false(idx_i) && bit)
      {
        break;
      }
    }

    /* If bits_min > bits_max, we can't generate any value. */
    if (d_bits_min->compare(*d_bits_max) <= 0)
    {
      d_bits.reset(new BitVector(*d_bits_min));
    }
  }
#ifndef NDEBUG
  d_min = mmin;
  d_max = mmax;
#endif
}

BitVectorDomainGenerator::~BitVectorDomainGenerator() {}

bool
BitVectorDomainGenerator::has_next() const
{
  assert(d_bits == nullptr
         || (d_bits_min && d_bits->compare(*d_bits_min) >= 0));
  return d_bits && d_bits->compare(*d_bits_max) <= 0;
}

bool
BitVectorDomainGenerator::has_random() const
{
  assert(d_bits == nullptr
         || (d_bits_min && d_bits_min->compare(*d_bits_min) >= 0));
  assert(!d_bits_min || d_bits_max);
  return d_bits_min && d_bits_min->compare(*d_bits_max) <= 0;
}

BitVector
BitVectorDomainGenerator::next()
{
  assert(has_next());
  return generate_next(false);
}

BitVector
BitVectorDomainGenerator::random()
{
  assert(has_random());
  return generate_next(true);
}

BitVector
BitVectorDomainGenerator::generate_next(bool random)
{
  assert(random || d_bits);

  uint64_t size = d_domain.size();
  BitVector res(d_domain.d_lo);

  /* Random always resets d_bits to a random value between d_bits_min and
   * d_bits_max. */
  if (random)
  {
    assert(d_rng);
    assert(d_bits_min);
    assert(d_bits_max);
    if (d_bits == nullptr) d_bits.reset(new BitVector(d_bits_min->size()));
    assert(d_bits->size() == d_bits_min->size());
    d_bits->iset(*d_rng, *d_bits_min, *d_bits_max, false);
  }

  for (uint64_t i = 0, j = 0; i < size; ++i)
  {
    if (!d_domain.is_fixed_bit(i))
    {
      res.set_bit(i, d_bits->bit(j++));
    }
  }

  /* If bits is ones, we enumerated all values. */
  if (d_bits->compare(*d_bits_max) == 0)
  {
    /* random never terminates and bits start again at bits_min. */

    if (random)
    {
      d_bits->iset(*d_bits_min);
    }
    else
    {
      d_bits.reset(nullptr);
    }
  }
  else
  {
    d_bits->ibvinc();
  }

  assert(d_bits == nullptr || d_bits->compare(*d_bits_min) >= 0);
  assert(d_bits == nullptr || d_bits->compare(*d_bits_max) <= 0);
#ifndef NDEBUG
  assert(res.compare(d_min) >= 0);
  assert(res.compare(d_max) <= 0);
#endif
  return res;
}

BitVectorDomainDualGenerator::BitVectorDomainDualGenerator(
    const BitVectorDomain &domain,
    const BitVector *min_lo,
    const BitVector *max_lo,
    const BitVector *min_hi,
    const BitVector *max_hi)
    : BitVectorDomainDualGenerator(
        domain, nullptr, min_lo, max_lo, min_hi, max_hi)
{
}

BitVectorDomainDualGenerator::BitVectorDomainDualGenerator(
    const BitVectorDomain &domain,
    RNG *rng,
    const BitVector *min_lo,
    const BitVector *max_lo,
    const BitVector *min_hi,
    const BitVector *max_hi)
    : d_rng(rng)
{
  assert(!max_lo || !min_lo || max_lo->compare(*min_lo) >= 0);
  assert(!max_hi || !min_hi || max_hi->compare(*min_hi) >= 0);
  uint64_t size = domain.size();
  assert(!max_lo || max_lo->compare(BitVector::mk_max_signed(size)) <= 0);
  assert(!min_hi || min_hi->compare(BitVector::mk_min_signed(size)) >= 0);

  d_gen_lo.reset(nullptr);
  d_gen_hi.reset(nullptr);

  if (min_lo || max_lo)
  {
    d_gen_lo.reset(new BitVectorDomainGenerator(
        domain,
        rng,
        min_lo ? *min_lo : BitVector::mk_zero(size),
        max_lo ? *max_lo : BitVector::mk_max_signed(size)));
    d_gen_cur = d_gen_lo.get();
  }
  if (min_hi || max_hi)
  {
    d_gen_hi.reset(new BitVectorDomainGenerator(
        domain,
        rng,
        min_hi ? *min_hi : BitVector::mk_min_signed(size),
        max_hi ? *max_hi : BitVector::mk_ones(size)));
    if (d_gen_cur == nullptr) d_gen_cur = d_gen_hi.get();
  }
}

BitVectorDomainDualGenerator::~BitVectorDomainDualGenerator() {}

bool
BitVectorDomainDualGenerator::has_next()
{
  if (d_gen_cur == nullptr) return false;
  if (!d_gen_cur->has_next())
  {
    if (d_gen_cur == d_gen_lo.get() && d_gen_hi)
    {
      d_gen_cur = d_gen_hi.get();
      return d_gen_cur->has_next();
    }
    return false;
  }
  return true;
}

bool
BitVectorDomainDualGenerator::has_random()
{
  if (d_gen_cur == nullptr) return false;
  if (!d_gen_cur->has_random())
  {
    if (d_gen_cur == d_gen_lo.get() && d_gen_hi)
    {
      d_gen_cur = d_gen_hi.get();
      return d_gen_cur->has_random();
    }
    return false;
  }
  return true;
}

BitVector
BitVectorDomainDualGenerator::next()
{
  assert(has_next());
  return d_gen_cur->next();
}

BitVector
BitVectorDomainDualGenerator::random()
{
  bool has_random_lo = d_gen_lo ? d_gen_lo->has_random() : false;
  bool has_random_hi = d_gen_hi ? d_gen_hi->has_random() : false;
  if (has_random_lo && has_random_hi)
  {
    return d_rng->flip_coin() ? d_gen_lo->random() : d_gen_hi->random();
  }
  if (has_random_lo)
  {
    return d_gen_lo->random();
  }
  assert(has_random_hi);
  return d_gen_hi->random();
}

BitVectorDomainSignedGenerator::BitVectorDomainSignedGenerator(
    const BitVectorDomain &domain)
    : BitVectorDomainSignedGenerator(domain,
                                     nullptr,
                                     BitVector::mk_min_signed(domain.size()),
                                     BitVector::mk_max_signed(domain.size()))
{
}

BitVectorDomainSignedGenerator::BitVectorDomainSignedGenerator(
    const BitVectorDomain &domain, const BitVector &min, const BitVector &max)
    : BitVectorDomainSignedGenerator(domain, nullptr, min, max)
{
}

BitVectorDomainSignedGenerator::BitVectorDomainSignedGenerator(
    const BitVectorDomain &domain, RNG *rng)
    : BitVectorDomainSignedGenerator(domain,
                                     rng,
                                     BitVector::mk_min_signed(domain.size()),
                                     BitVector::mk_max_signed(domain.size()))
{
}

BitVectorDomainSignedGenerator::BitVectorDomainSignedGenerator(
    const BitVectorDomain &domain,
    RNG *rng,
    const BitVector &min,
    const BitVector &max)
    : d_rng(rng)
{
  uint64_t size          = domain.size();
  BitVector zero         = BitVector::mk_zero(size);
  BitVector ones         = BitVector::mk_ones(size);
  int32_t min_scomp_zero = min.signed_compare(zero);
  int32_t max_scomp_zero = max.signed_compare(zero);

  d_gen_lo.reset(nullptr);
  d_gen_hi.reset(nullptr);

  if (min_scomp_zero < 0)
  {
    d_gen_lo.reset(new BitVectorDomainGenerator(
        domain, rng, min, max_scomp_zero < 0 ? max : ones));
    d_gen_cur = d_gen_lo.get();
  }
  if (max_scomp_zero >= 0)
  {
    d_gen_hi.reset(new BitVectorDomainGenerator(
        domain, rng, min_scomp_zero >= 0 ? min : zero, max));
    if (d_gen_cur == nullptr) d_gen_cur = d_gen_hi.get();
  }
}

BitVectorDomainSignedGenerator::~BitVectorDomainSignedGenerator() {}

bool
BitVectorDomainSignedGenerator::has_next()
{
  if (d_gen_cur == nullptr) return false;
  if (!d_gen_cur->has_next())
  {
    if (d_gen_cur == d_gen_lo.get() && d_gen_hi)
    {
      d_gen_cur = d_gen_hi.get();
      return d_gen_cur->has_next();
    }
    return false;
  }
  return true;
}

bool
BitVectorDomainSignedGenerator::has_random()
{
  if (d_gen_cur == nullptr) return false;
  if (!d_gen_cur->has_random())
  {
    if (d_gen_cur == d_gen_lo.get() && d_gen_hi)
    {
      d_gen_cur = d_gen_hi.get();
      return d_gen_cur->has_random();
    }
    return false;
  }
  return true;
}

BitVector
BitVectorDomainSignedGenerator::next()
{
  assert(has_next());
  return d_gen_cur->next();
}

BitVector
BitVectorDomainSignedGenerator::random()
{
  bool has_random_lo = d_gen_lo ? d_gen_lo->has_random() : false;
  bool has_random_hi = d_gen_hi ? d_gen_hi->has_random() : false;
  if (has_random_lo && has_random_hi)
  {
    return d_rng->flip_coin() ? d_gen_lo->random() : d_gen_hi->random();
  }
  if (has_random_lo)
  {
    return d_gen_lo->random();
  }
  assert(has_random_hi);
  return d_gen_hi->random();
}

std::ostream &
operator<<(std::ostream &out, const BitVectorDomain &d)
{
  out << d.str();
  return out;
}

}  // namespace ls
}  // namespace bzla
