/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "bv/domain/bitvector_domain.h"

#include <algorithm>
#include <cassert>
#include <iostream>

#include "bv/bitvector.h"
#include "bv/bounds/bitvector_bounds.h"
#include "bv/domain/wheel_factorizer.h"
#include "rng/rng.h"

namespace bzla {

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
{
  if (!other.is_null())
  {
    d_lo             = other.d_lo;
    d_hi             = other.d_hi;
    d_has_fixed_bits = other.d_has_fixed_bits;
    assert(d_has_fixed_bits == (!d_lo.is_zero() || !d_hi.is_ones()));
  }
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
  if (is_null())
  {
    return other.is_null();
  }
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
                            const BitVectorBounds &bounds,
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
        if (match_fixed_bits(mul) && bounds.contains(mul))
        {
          return mul;
        }
      }
    }
    else
    {
      assert(n_factors == 1);
      if (match_fixed_bits(factors[0]) && bounds.contains(factors[0]))
      {
        return factors[0];
      }
    }
  }
  return BitVector();
}

std::string
BitVectorDomain::str() const
{
  if (is_null())
  {
    return "(nil)";
  }
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

/* --- BitVectorDomainGenerator --------------------------------------------- */

BitVectorDomainGenerator::BitVectorDomainGenerator(
    const BitVectorDomain &domain)
    : BitVectorDomainGenerator(domain, nullptr, BitVectorRange(domain))
{
}

BitVectorDomainGenerator::BitVectorDomainGenerator(
    const BitVectorDomain &domain, const BitVectorRange &range)
    : BitVectorDomainGenerator(domain, nullptr, range)
{
}

BitVectorDomainGenerator::BitVectorDomainGenerator(
    const BitVectorDomain &domain, RNG *rng)
    : BitVectorDomainGenerator(domain, rng, BitVectorRange(domain))
{
}

BitVectorDomainGenerator::BitVectorDomainGenerator(
    const BitVectorDomain &domain, RNG *rng, const BitVectorRange &range)
    : d_domain(domain), d_rng(rng)
{
  assert(!range.empty());

  uint64_t size         = domain.size();
  const BitVector &hi   = d_domain.d_hi;
  const BitVector &lo   = d_domain.d_lo;

  if (d_domain.is_fixed())
  {
    d_is_fixed = true;
    if (lo.compare(range.d_min) >= 0 && lo.compare(range.d_max) <= 0)
    {
      d_bits     = &d_domain.d_lo;
      d_bits_min = &d_domain.d_lo;
      d_bits_max = &d_domain.d_lo;
    }
#ifndef NDEBUG
    d_min = lo;
    d_max = hi;
#endif
    return;
  }

  uint64_t cnt          = 0;  // the number of bits that are not fixed
  const BitVector &mmin = lo.compare(range.d_min) <= 0 ? range.d_min : lo;
  const BitVector &mmax = hi.compare(range.d_max) >= 0 ? range.d_max : hi;
#ifndef NDEBUG
  d_min = mmin;
  d_max = mmax;
#endif

  if (!d_domain.d_has_fixed_bits)
  {
    d__bits_min = range.d_min;
    d__bits_max = range.d_max;
    d_bits      = &d__bits_min;
    d_bits_min  = &d__bits_min;
    d_bits_max  = &d__bits_max;
    return;
  }

  d_has_fixed_bits = true;
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
    d__bits_min = BitVector::mk_zero(cnt);
    d_bits_min  = &d__bits_min;
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
    d__bits_max = BitVector::mk_ones(cnt);
    d_bits_max  = &d__bits_max;
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
      d__bits = BitVector(*d_bits_min);
      d_bits  = &d__bits;
    }
  }
}

BitVectorDomainGenerator::~BitVectorDomainGenerator() {}

bool
BitVectorDomainGenerator::has_next() const
{
  assert(d_bits == nullptr
         || (d_bits_min && d_bits->compare(*d_bits_min) >= 0));
  return d_bits && (d_is_fixed || d_bits->compare(*d_bits_max) <= 0);
}

bool
BitVectorDomainGenerator::has_random() const
{
  assert(d_bits == nullptr
         || (d_bits_min && d_bits_min->compare(*d_bits_min) >= 0));
  assert(!d_bits_min || d_bits_max);
  return d_bits_min && (d_is_fixed || d_bits_min->compare(*d_bits_max) <= 0);
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

  // Note: Random does not change the value of `d_bits` in order to not disturb
  // sequences generated via calls to `next()` if calls to `random()` are
  // interleaved.

  if (d_is_fixed)
  {
    BitVector res = *d_bits;
    if (!random)
    {
      d_bits = nullptr;
    }
    return res;
  }

  uint64_t size = d_domain.size();

  if (!d_has_fixed_bits)
  {
    if (random)
    {
      assert(d_rng);
      assert(d_bits_min);
      assert(d_bits_max);
      return BitVector(size, *d_rng, *d_bits_min, *d_bits_max);
    }

    BitVector res = *d_bits;
    if (d_bits->compare(*d_bits_max) == 0)
    {
      d_bits = nullptr;
    }
    else
    {
      d_bits->ibvinc();
    }
    return res;
  }

  BitVector res(d_domain.d_lo);
  if (random)
  {
    assert(d_rng);
    assert(d_bits_min);
    assert(d_bits_max);
    BitVector tmp(d_bits_min->size(), *d_rng, *d_bits_min, *d_bits_max);
    for (uint64_t i = 0, j = 0; i < size; ++i)
    {
      if (!d_domain.is_fixed_bit(i))
      {
        res.set_bit(i, tmp.bit(j++));
      }
    }
    return res;
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
    d_bits = nullptr;
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

/* --- BitVectorDomainDualGenerator ----------------------------------------- */

BitVectorDomainDualGenerator::BitVectorDomainDualGenerator(
    const BitVectorDomain &domain, const BitVectorBounds &bounds, RNG *rng)
    : d_rng(rng)
{
  assert(bounds.valid());

  d_gen_lo.reset(nullptr);
  d_gen_hi.reset(nullptr);

  if (bounds.has_lo())
  {
    d_gen_lo.reset(new BitVectorDomainGenerator(domain, rng, bounds.d_lo));
    d_gen_cur = d_gen_lo.get();
  }
  if (bounds.has_hi())
  {
    d_gen_hi.reset(new BitVectorDomainGenerator(domain, rng, bounds.d_hi));
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

/* --- BitVectorDomainSignedGenerator --------------------------------------- */
BitVectorDomainSignedGenerator::BitVectorDomainSignedGenerator(
    const BitVectorDomain &domain)
    : BitVectorDomainSignedGenerator(
          domain,
          nullptr,
          BitVectorRange(BitVector::mk_min_signed(domain.size()),
                         BitVector::mk_max_signed(domain.size())))
{
}

BitVectorDomainSignedGenerator::BitVectorDomainSignedGenerator(
    const BitVectorDomain &domain, const BitVectorRange &range)
    : BitVectorDomainSignedGenerator(domain, nullptr, range)
{
}

BitVectorDomainSignedGenerator::BitVectorDomainSignedGenerator(
    const BitVectorDomain &domain, RNG *rng)
    : BitVectorDomainSignedGenerator(
          domain,
          rng,
          BitVectorRange(BitVector::mk_min_signed(domain.size()),
                         BitVector::mk_max_signed(domain.size())))
{
}

BitVectorDomainSignedGenerator::BitVectorDomainSignedGenerator(
    const BitVectorDomain &domain, RNG *rng, const BitVectorRange &range)
    : d_rng(rng)
{
  uint64_t size          = domain.size();
  BitVector zero         = BitVector::mk_zero(size);
  BitVector ones         = BitVector::mk_ones(size);
  int32_t min_scomp_zero = range.d_min.signed_compare(zero);
  int32_t max_scomp_zero = range.d_max.signed_compare(zero);

  d_gen_lo.reset(nullptr);
  d_gen_hi.reset(nullptr);

  if (min_scomp_zero < 0)
  {
    d_gen_lo.reset(new BitVectorDomainGenerator(
        domain,
        rng,
        BitVectorRange(range.d_min, max_scomp_zero < 0 ? range.d_max : ones)));
    d_gen_cur = d_gen_lo.get();
  }
  if (max_scomp_zero >= 0)
  {
    d_gen_hi.reset(new BitVectorDomainGenerator(
        domain,
        rng,
        BitVectorRange(min_scomp_zero >= 0 ? range.d_min : zero, range.d_max)));
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

}  // namespace bzla
