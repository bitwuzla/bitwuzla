/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2021 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "ls/bv/bitvector_node.h"

#include <cassert>
#include <iostream>
#include <sstream>

#include "rng/rng.h"

namespace bzla {
namespace ls {

/* -------------------------------------------------------------------------- */

// Note: These 3 macros should never be (member) functions:
//       - some values can be moved with std::move
//       - for BV_NODE_CACHE_INVERSE_IF, we don't want unnecessary calls to,
//       e.g., gen.random(), when passed as an argument value (we only want it
//       evaluated when it is indeed an invertibility check)
#define BV_NODE_CACHE_CONSISTENT(val) d_consistent.reset(new BitVector(val))
#define BV_NODE_CACHE_INVERSE(val) d_inverse.reset(new BitVector(val))
#define BV_NODE_CACHE_INVERSE_IF(val) \
  if (!is_essential_check)            \
  {                                   \
    BV_NODE_CACHE_INVERSE(val);       \
  }

/* -------------------------------------------------------------------------- */

BitVectorNode::BitVectorNode(RNG* rng, uint64_t size)
    : BitVectorNode(rng, BitVector::mk_zero(size), BitVectorDomain(size))
{
}

BitVectorNode::BitVectorNode(RNG* rng, uint64_t size, BitVectorNode* child0)
    : BitVectorNode(rng, BitVectorDomain(size), child0)
{
}

BitVectorNode::BitVectorNode(RNG* rng,
                             uint64_t size,
                             BitVectorNode* child0,
                             BitVectorNode* child1)
    : BitVectorNode(rng, BitVectorDomain(size), child0, child1)
{
}

BitVectorNode::BitVectorNode(RNG* rng,
                             uint64_t size,
                             BitVectorNode* child0,
                             BitVectorNode* child1,
                             BitVectorNode* child2)
    : BitVectorNode(rng, BitVectorDomain(size), child0, child1, child2)
{
}

BitVectorNode::BitVectorNode(RNG* rng,
                             const BitVector& assignment,
                             const BitVectorDomain& domain)
    : Node<BitVector>(rng, assignment, domain.is_fixed()), d_domain(domain)
{
  assert(assignment.size() == domain.size());
  assert(domain.match_fixed_bits(assignment));
}

BitVectorNode::BitVectorNode(RNG* rng,
                             const BitVectorDomain& domain,
                             BitVectorNode* child0)
    : Node<BitVector>(rng, domain.lo(), child0, domain.is_fixed()),
      d_domain(domain)
{
  assert(rng);
}

BitVectorNode::BitVectorNode(RNG* rng,
                             const BitVectorDomain& domain,
                             BitVectorNode* child0,
                             BitVectorNode* child1)
    : Node<BitVector>(rng, domain.lo(), child0, child1, domain.is_fixed()),
      d_domain(domain)
{
  assert(rng);
}

BitVectorNode::BitVectorNode(RNG* rng,
                             const BitVectorDomain& domain,
                             BitVectorNode* child0,
                             BitVectorNode* child1,
                             BitVectorNode* child2)
    : Node<BitVector>(
        rng, domain.lo(), child0, child1, child2, domain.is_fixed()),
      d_domain(domain)
{
  assert(rng);
}

bool
BitVectorNode::is_inequality() const
{
  return kind() == NodeKind::BV_SLT || kind() == NodeKind::BV_ULT;
}

bool
BitVectorNode::is_not() const
{
  return kind() == NodeKind::BV_NOT;
}

bool
BitVectorNode::is_value_false() const
{
  assert(!d_is_value || d_domain.size() > 1 || !d_domain.is_fixed_bit_true(0));
  return d_is_value && d_assignment.is_false();
}

void
BitVectorNode::set_assignment(const BitVector& assignment)
{
  assert(d_domain.match_fixed_bits(assignment));
  d_assignment.iset(assignment);
}

std::string
BitVectorNode::str() const
{
  return (d_symbol ? *d_symbol + " " : "") + "[" + std::to_string(d_id) + "] "
         + "(" + std::to_string(d_normalized_id) + ") " + std::to_string(kind())
         + ": " + d_domain.str() + " (" + d_assignment.str() + ")";
}

std::vector<std::string>
BitVectorNode::log() const
{
  std::vector<std::string> res;
  for (uint32_t i = 0, n = arity(); i < n; ++i)
  {
    BitVectorNode& c = *child(i);
    {
      std::stringstream ss;
      ss << "      |- node[" << i << "]: " << c << std::endl;
      res.push_back(ss.str());
    }
    if (c.min_u())
    {
      std::stringstream ss;
      ss << "           + min_u: " << *c.min_u() << std::endl;
      res.push_back(ss.str());
    }
    if (c.max_u())
    {
      std::stringstream ss;
      ss << "           + max_u: " << *c.max_u() << std::endl;
      res.push_back(ss.str());
    }
    if (c.min_s())
    {
      std::stringstream ss;
      ss << "           + min_s: " << *c.min_s() << std::endl;
      res.push_back(ss.str());
    }
    if (c.max_s())
    {
      std::stringstream ss;
      ss << "           + max_s: " << *c.max_s() << std::endl;
      res.push_back(ss.str());
    }
  }
  return res;
}

BitVectorNode*
BitVectorNode::child(uint64_t pos) const
{
  assert(dynamic_cast<BitVectorNode*>(d_children[pos]) != nullptr);
  return reinterpret_cast<BitVectorNode*>(d_children[pos]);
}

void
BitVectorNode::register_extract(BitVectorNode* node)
{
  assert(node->kind() == NodeKind::BV_EXTRACT);
  d_extracts.push_back(static_cast<BitVectorExtract*>(node));
}

void
BitVectorNode::fix_bit(uint64_t idx, bool value)
{
  assert(idx < d_domain.size());
  d_domain.fix_bit(idx, value);
}

void
BitVectorNode::update_bounds(const BitVector& min,
                             const BitVector& max,
                             bool min_is_exclusive,
                             bool max_is_exclusive,
                             bool is_signed)
{
  assert(!min.is_null());
  assert(!max.is_null());
  assert(size() == min.size());
  assert(size() == max.size());
  assert(is_signed || min.compare(max) <= 0);
  assert(!is_signed || min.signed_compare(max) <= 0);

  if (is_signed)
  {
    if (!d_min_s || d_min_s->signed_compare(min) < 0)
    {
      if (min_is_exclusive)
      {
        assert(!min.is_max_signed());
        d_min_s.reset(new BitVector(min.bvinc()));
      }
      else
      {
        d_min_s.reset(new BitVector(min));
      }
    }
    if (!d_max_s || d_max_s->signed_compare(max) > 0)
    {
      if (max_is_exclusive)
      {
        assert(!max.is_min_signed());
        d_max_s.reset(new BitVector(max.bvdec()));
      }
      else
      {
        d_max_s.reset(new BitVector(max));
      }
    }
  }
  else
  {
    if (!d_min_u || d_min_u->compare(min) < 0)
    {
      if (min_is_exclusive)
      {
        assert(!min.is_ones());
        d_min_u.reset(new BitVector(min.bvinc()));
      }
      else
      {
        d_min_u.reset(new BitVector(min));
      }
    }
    if (!d_max_u || d_max_u->compare(max) > 0)
    {
      if (max_is_exclusive)
      {
        assert(!max.is_zero());
        d_max_u.reset(new BitVector(max.bvdec()));
      }
      else
      {
        d_max_u.reset(new BitVector(max));
      }
    }
  }
}

void
BitVectorNode::reset_bounds()
{
  d_min_u = nullptr;
  d_max_u = nullptr;
  d_min_s = nullptr;
  d_max_s = nullptr;
}

void
BitVectorNode::tighten_bounds(BitVector* min_u,
                              BitVector* max_u,
                              BitVector* min_s,
                              BitVector* max_s,
                              BitVector& res_min_u,
                              BitVector& res_max_u,
                              BitVector& res_min_s,
                              BitVector& res_max_s)
{
  BitVector* mmin;
  BitVector* mmax;
  // unsigned
  if (min_u)
  {
    assert(max_u);
    mmin = min_u;
    mmax = max_u;
    if (d_min_u && d_min_u->compare(*min_u) > 0)
    {
      mmin = d_min_u.get();
    }
    if (d_max_u && d_max_u->compare(*max_u) < 0)
    {
      mmax = d_max_u.get();
    }
    if (mmin->compare(*mmax) > 0)
    {
      // conflict
      res_min_u = BitVector();
      res_max_u = BitVector();
    }
    else
    {
      if (mmin != &res_min_u) res_min_u = *mmin;
      if (mmax != &res_max_u) res_max_u = *mmax;
    }
  }
  // signed
  if (min_s)
  {
    assert(max_s);
    mmin = min_s;
    mmax = max_s;
    if (d_min_s && d_min_s->signed_compare(*min_s) > 0)
    {
      mmin = d_min_s.get();
    }
    if (d_max_s && d_max_s->signed_compare(*max_s) < 0)
    {
      mmax = d_max_s.get();
    }
    if (mmin->signed_compare(*mmax) > 0)
    {
      // conflict
      res_min_s = BitVector();
      res_max_s = BitVector();
    }
    else
    {
      if (mmin != &res_min_s) res_min_s = *mmin;
      if (mmax != &res_max_s) res_max_s = *mmax;
    }
  }
}

void
BitVectorNode::normalize_bounds(BitVector* min_u,
                                BitVector* max_u,
                                BitVector* min_s,
                                BitVector* max_s,
                                BitVector& res_min_lo,
                                BitVector& res_max_lo,
                                BitVector& res_min_hi,
                                BitVector& res_max_hi)
{
  assert(!min_u || min_u->size() == size());
  assert(!max_u || max_u->size() == size());
  assert(!min_s || min_s->size() == size());
  assert(!max_s || max_s->size() == size());

  assert(res_min_lo.is_null());
  assert(res_max_lo.is_null());
  assert(res_min_hi.is_null());
  assert(res_max_hi.is_null());

  uint64_t size        = this->size();
  BitVector zero       = BitVector::mk_zero(size);
  BitVector ones       = BitVector::mk_ones(size);
  BitVector min_signed = BitVector::mk_min_signed(size);
  BitVector max_signed = BitVector::mk_max_signed(size);
  BitVector *min_lo = nullptr, *max_lo = nullptr;
  BitVector *min_hi = nullptr, *max_hi = nullptr;

  if (min_u || max_u)
  {
    int32_t min_comp_max_signed = min_u ? min_u->compare(max_signed) : -1;
    int32_t max_comp_max_signed = max_u ? max_u->compare(max_signed) : 1;

    if (min_comp_max_signed <= 0)
    {
      min_lo = min_u ? min_u : &zero;
      max_lo = max_comp_max_signed <= 0 ? max_u : &max_signed;
    }
    if (max_comp_max_signed > 0)
    {
      min_hi = min_comp_max_signed > 0 ? min_u : &min_signed;
      max_hi = max_u ? max_u : &ones;
    }
  }
  if (min_s || max_s)
  {
    int32_t min_scomp_zero = min_s ? min_s->signed_compare(zero) : -1;
    int32_t max_scomp_zero = max_s ? max_s->signed_compare(zero) : 1;
    BitVector *minu = nullptr, *maxu = nullptr;
    BitVector *mins = nullptr, *maxs = nullptr;

    if (min_scomp_zero < 0)
    {
      mins = min_s ? min_s : &min_signed;
      maxs = max_scomp_zero < 0 ? max_s : &ones;
    }
    if (max_scomp_zero >= 0)
    {
      minu = min_scomp_zero >= 0 ? min_s : &zero;
      maxu = max_s ? max_s : &max_signed;
    }
    assert(!mins || maxs);
    assert(!minu || maxu);

    if (!min_u && !max_u)
    {
      min_hi = mins;
      max_hi = maxs;
      min_lo = minu;
      max_lo = maxu;
    }
    else
    {
      if (min_hi)
      {
        if (!mins)
        {
          min_hi = nullptr;
          max_hi = nullptr;
        }
        else
        {
          if (max_hi && mins->compare(*max_hi) > 0)
          {
            min_hi = nullptr;
            max_hi = nullptr;
          }
          else if (!min_hi || mins->compare(*min_hi) > 0)
          {
            min_hi = mins;
          }
        }
      }
      if (max_hi)
      {
        if (!maxs)
        {
          min_hi = nullptr;
          max_hi = nullptr;
        }
        else
        {
          if (min_hi && maxs->compare(*min_hi) < 0)
          {
            min_hi = nullptr;
            max_hi = nullptr;
          }
          else if (!max_hi || maxs->compare(*max_hi) < 0)
          {
            max_hi = maxs;
          }
        }
      }
      if (min_lo)
      {
        if (!minu)
        {
          min_lo = nullptr;
          max_lo = nullptr;
        }
        else
        {
          if (max_lo && minu->compare(*max_lo) > 0)
          {
            min_lo = nullptr;
            max_lo = nullptr;
          }
          else if (!min_lo || minu->compare(*min_lo) > 0)
          {
            min_lo = minu;
          }
        }
      }
      if (max_lo)
      {
        if (!maxu)
        {
          min_lo = nullptr;
          max_lo = nullptr;
        }
        else
        {
          if (min_lo && maxu->compare(*min_lo) < 0)
          {
            min_lo = nullptr;
            max_lo = nullptr;
          }
          else if (!max_lo || maxu->compare(*max_lo) < 0)
          {
            max_lo = maxu;
          }
        }
      }
    }
  }
  assert(!min_lo || max_lo);
  assert(!min_hi || max_hi);
  if (min_lo && max_lo && min_lo->compare(*max_lo) > 0)
  {
    min_lo = nullptr;
    max_lo = nullptr;
  }
  if (min_hi && max_hi && min_hi->compare(*max_hi) > 0)
  {
    min_hi = nullptr;
    max_hi = nullptr;
  }

  if (min_lo) res_min_lo = *min_lo;
  if (max_lo) res_max_lo = *max_lo;
  if (min_hi) res_min_hi = *min_hi;
  if (max_hi) res_max_hi = *max_hi;

  assert(res_min_lo.is_null() || !res_max_lo.is_null());
  assert(res_min_hi.is_null() || !res_max_hi.is_null());
}

void
BitVectorNode::compute_normalized_bounds(const BitVector& s,
                                         const BitVector& t,
                                         uint64_t pos_x,
                                         BitVector& res_min_lo,
                                         BitVector& res_max_lo,
                                         BitVector& res_min_hi,
                                         BitVector& res_max_hi)
{
  // the current unsigned bounds on x wrt. s, t and the current bounds on x
  BitVector min_u, max_u;
  // the current signed bounds on x wrt. s, t and the current bounds on x
  BitVector min_s, max_s;

  res_min_lo = BitVector();
  res_max_lo = BitVector();
  res_min_hi = BitVector();
  res_max_hi = BitVector();

  compute_min_max_bounds(s, t, pos_x, min_u, max_u, min_s, max_s);
  assert(min_u.is_null() == max_u.is_null());
  assert(min_s.is_null() == max_s.is_null());
  if (min_u.is_null() && min_s.is_null())
  {
    return;  // conflict
  }

  BitVectorNode* op_x = child(pos_x);
  op_x->normalize_bounds(min_u.is_null() ? op_x->min_u() : &min_u,
                         max_u.is_null() ? op_x->max_u() : &max_u,
                         min_s.is_null() ? op_x->min_s() : &min_s,
                         max_s.is_null() ? op_x->max_s() : &max_s,
                         res_min_lo,
                         res_max_lo,
                         res_min_hi,
                         res_max_hi);
}

void
BitVectorNode::compute_min_max_bounds(const BitVector& s,
                                      const BitVector& t,
                                      uint64_t pos_x,
                                      BitVector& res_min_u,
                                      BitVector& res_max_u,
                                      BitVector& res_min_s,
                                      BitVector& res_max_s)
{
  (void) s;
  (void) t;
  (void) pos_x;
  (void) res_min_u;
  (void) res_max_u;
  (void) res_min_s;
  (void) res_max_s;
  assert(false);
}

bool
BitVectorNode::is_in_bounds(const BitVector& bv,
                            const BitVector& min_lo,
                            const BitVector& max_lo,
                            const BitVector& min_hi,
                            const BitVector& max_hi)
{
  assert(!min_lo.is_null() || !min_hi.is_null());
  assert(min_lo.is_null() == max_lo.is_null());
  assert(min_hi.is_null() == max_hi.is_null());
  return (!min_lo.is_null() && bv.compare(min_lo) >= 0
          && bv.compare(max_lo) <= 0)
         || (!min_hi.is_null() && bv.compare(min_hi) >= 0
             && bv.compare(max_hi) <= 0);
}

std::ostream&
operator<<(std::ostream& out, const BitVectorNode& node)
{
  out << node.str();
  return out;
}

/* -------------------------------------------------------------------------- */

BitVectorAdd::BitVectorAdd(RNG* rng,
                           uint64_t size,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == child0->size());
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorAdd::BitVectorAdd(RNG* rng,
                           const BitVectorDomain& domain,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == child0->size());
  _evaluate_and_set_domain();
}

void
BitVectorAdd::_evaluate()
{
  d_assignment.ibvadd(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorAdd::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorAdd::evaluate()
{
  _evaluate();
}

bool
BitVectorAdd::is_invertible(const BitVector& t,
                            uint64_t pos_x,
                            bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: true
   * IC:    mcb(x, t - s)
   *
   * Inverse value: t - s
   */

  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  BitVector sub      = t.bvsub(s);

  if (child(pos_x)->domain().has_fixed_bits())
  {
    const BitVectorDomain& x = child(pos_x)->domain();
    if (!x.match_fixed_bits(sub))
    {
      return false;
    }
  }
  // Inverse value: t - s
  BV_NODE_CACHE_INVERSE_IF(std::move(sub));
  return true;
}

bool
BitVectorAdd::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC   : true
   *
   * Consistent value: random value
   */

  (void) t;
  (void) pos_x;

  const BitVectorDomain& x = child(pos_x)->domain();
  if (x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      BV_NODE_CACHE_CONSISTENT(x.lo());
    }
    else
    {
      BitVectorDomainGenerator gen(x, d_rng);
      // Consistent value: random value
      BV_NODE_CACHE_CONSISTENT(gen.random());
    }
  }
  else
  {
    // Consistent value: random value
    BV_NODE_CACHE_CONSISTENT(BitVector(x.size(), *d_rng));
  }
  return true;
}

const BitVector&
BitVectorAdd::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(t.compare(d_inverse->bvadd(s)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorAdd::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorAnd::BitVectorAnd(RNG* rng,
                           uint64_t size,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == child0->size());
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorAnd::BitVectorAnd(RNG* rng,
                           const BitVectorDomain& domain,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == child0->size());
  _evaluate_and_set_domain();
}

void
BitVectorAnd::_evaluate()
{
  d_assignment.ibvand(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorAnd::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorAnd::evaluate()
{
  _evaluate();
}

void
BitVectorAnd::compute_min_max_bounds(const BitVector& s,
                                     const BitVector& t,
                                     uint64_t pos_x,
                                     BitVector& res_min_u,
                                     BitVector& res_max_u,
                                     BitVector& res_min_s,
                                     BitVector& res_max_s)
{
  assert(res_min_u.is_null());
  assert(res_max_u.is_null());
  assert(res_min_s.is_null());
  assert(res_max_s.is_null());
  BitVectorNode* op_x      = child(pos_x);
  const BitVectorDomain& x = op_x->domain();
  d_lo                     = x.lo().bvor(t);
  d_hi                     = x.hi().bvand(s.bvxnor(t));
  res_min_u                = d_lo;
  res_max_u                = d_hi;
  op_x->tighten_bounds(&res_min_u,
                       &res_max_u,
                       nullptr,
                       nullptr,
                       res_min_u,
                       res_max_u,
                       res_min_s,
                       res_max_s);
}

bool
BitVectorAnd::is_invertible(const BitVector& t,
                            uint64_t pos_x,
                            bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: (t & s) = t
   * IC:    IC_wo && ((s & hi_x) & m) = (t & m)
   *        with m = ~(lo_x ^ hi_x)  ... mask out all non-const bits
   * TODO: + bounds
   *
   * Inverse value: (t & s) | (~s & rand)
   * TODO: + bounds
   */

  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  BitVectorNode* op_x      = child(pos_x);
  const BitVectorDomain& x = op_x->domain();
  BitVector* min_u         = op_x->min_u();
  BitVector* max_u         = op_x->max_u();
  BitVector* min_s         = op_x->min_s();
  BitVector* max_s         = op_x->max_s();

  // IC_wo: (t & s) = t
  bool ic               = t.bvand(s).compare(t) == 0;
  bool x_has_fixed_bits = x.has_fixed_bits();

  // IC: IC_wo && ((s & hi_x) & m) = (t & m)
  if (ic && x_has_fixed_bits)
  {
    if (x.is_fixed() && x.lo().bvand(s).compare(t) != 0)
    {
      return false;
    }
    // m = ~(lo_x ^ hi_x)  ... mask out all non-const bits
    BitVector mask = x.lo().bvxnor(x.hi());
    ic             = s.bvand(x.hi()).ibvand(mask).compare(t.bvand(mask)) == 0;
  }

  if (ic)
  {
    if (min_u || max_u || min_s || max_s)
    {
      BitVector min_lo, max_lo, min_hi, max_hi;
      compute_normalized_bounds(s, t, pos_x, min_lo, max_lo, min_hi, max_hi);
      if (min_hi.is_null() && max_hi.is_null() && min_lo.is_null()
          && max_lo.is_null())
      {
        return false;
      }
      assert(!d_lo.is_null() && !d_hi.is_null());
      if (d_lo.compare(d_hi) == 0)
      {
        BV_NODE_CACHE_INVERSE_IF(d_lo);
        return true;
      }
      BitVectorDomain tmp(x.lo().bvor(t), x.hi().bvand(s.bvxnor(t)));
      BitVectorDomainDualGenerator gen(tmp,
                                       d_rng,
                                       min_lo.is_null() ? nullptr : &min_lo,
                                       max_lo.is_null() ? nullptr : &max_lo,
                                       min_hi.is_null() ? nullptr : &min_hi,
                                       max_hi.is_null() ? nullptr : &max_hi);
      if (!gen.has_random())
      {
        return false;
      }
      BV_NODE_CACHE_INVERSE_IF(gen.random());
      return true;
    }

    if (!is_essential_check)
    {
      BitVector rand;
      if (x_has_fixed_bits)
      {
        if (x.is_fixed())
        {
          rand = x.lo();
        }
        else
        {
          BitVectorDomainGenerator gen(x, d_rng);
          assert(gen.has_random());
          rand = gen.random();
        }
      }
      else
      {
        rand = BitVector(t.size(), *d_rng);
      }
      BV_NODE_CACHE_INVERSE(t.bvand(s).bvor(s.bvnot().ibvand(rand)));
    }
    return true;
  }

  return false;
}

bool
BitVectorAnd::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    t & hi_x = t
   *
   * Consistent value: t | rand
   */

  // CC: t & hi_x = t
  const BitVectorDomain& x = child(pos_x)->domain();
  if (x.has_fixed_bits())
  {
    if (t.compare(t.bvand(x.hi())) == 0)
    {
      if (x.is_fixed())
      {
        BV_NODE_CACHE_CONSISTENT(x.lo());
      }
      else
      {
        BitVectorDomainGenerator gen(x, d_rng);
        BV_NODE_CACHE_CONSISTENT(gen.random().ibvor(t));
      }
      return true;
    }
    return false;
  }
  BV_NODE_CACHE_CONSISTENT(BitVector(x.size(), *d_rng).ibvor(t));
  return true;
}

const BitVector&
BitVectorAnd::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(t.compare(d_inverse->bvand(s)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorAnd::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorConcat::BitVectorConcat(RNG* rng,
                                 uint64_t size,
                                 BitVectorNode* child0,
                                 BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == child0->size() + child1->size());
  _evaluate_and_set_domain();
}

BitVectorConcat::BitVectorConcat(RNG* rng,
                                 const BitVectorDomain& domain,
                                 BitVectorNode* child0,
                                 BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(domain.size() == child0->size() + child1->size());
  _evaluate_and_set_domain();
}

void
BitVectorConcat::_evaluate()
{
  d_assignment.ibvconcat(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorConcat::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorConcat::evaluate()
{
  _evaluate();
}

bool
BitVectorConcat::is_invertible(const BitVector& t,
                               uint64_t pos_x,
                               bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: pos_x = 0: s = t[size(s) - 1 : 0]
   *        pos_x = 1: s = t[size(t) - 1 : size(t) - size(s)]
   * IC:    IC_wo && mcb(x, tx)
   *
   * Inverse value:
   *   pos_x = 0: t[size(t) - 1: size(s)]
   *   pos_x = 1: t[size(x) - 1: 0]
   */
  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();
  BitVector tx;
  bool ic_wo;

  uint64_t bw_t = t.size();
  uint64_t bw_s = s.size();

  // IC_wo
  if (pos_x == 0)
  {
    // pos_x = 0: s = t[size(s) - 1 : 0]
    ic_wo = t.bvextract(bw_s - 1, 0).compare(s) == 0;
    tx    = t.bvextract(bw_t - 1, bw_s);
  }
  else
  {
    // pos_x = 1: s = t[size(t) - 1 : size(t) - size(s)]
    assert(pos_x == 1);
    ic_wo = t.bvextract(bw_t - 1, bw_t - bw_s).compare(s) == 0;
    tx    = t.bvextract(bw_t - bw_s - 1, 0);
  }

  // IC: IC_wo && mcb(x, tx)
  if (ic_wo)
  {
    if (x.has_fixed_bits() && !x.match_fixed_bits(tx))
    {
      return false;
    }
    BV_NODE_CACHE_INVERSE_IF(std::move(tx));
    return true;
  }
  return false;
}

bool
BitVectorConcat::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    mcb(x, tx)
   *        with pos_x = 0: tx = t[size(t) - 1 : size(t) - size(x)]
   *             pos_x = 1: tx = t[size(x) - 1 : 0]
   *
   * Consistent value:
   *   pos_x = 0: t[msb, bw_x]
   *   pos_x = 1: t[bw_x - 1, 0]
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t bw_t            = t.size();
  uint64_t bw_x            = x.size();

  // CC: mcb(x, tx)
  if (pos_x == 0)
  {
    // Consistent value: pos_x = 0: tx = t[size(t) - 1 : size(t) - size(x)]
    BitVector tx = t.bvextract(bw_t - 1, bw_t - bw_x);
    if (!x.has_fixed_bits() || x.match_fixed_bits(tx))
    {
      d_consistent.reset(new BitVector(tx));
      return true;
    }
    return false;
  }
  // Consistent value: pos_x = 1: tx = t[size(x) - 1 : 0]
  BitVector tx = t.bvextract(bw_x - 1, 0);
  if (!x.has_fixed_bits() || x.match_fixed_bits(tx))
  {
    d_consistent.reset(new BitVector(tx));
    return true;
  }
  return false;
}

const BitVector&
BitVectorConcat::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(pos_x == 1 || t.compare(d_inverse->bvconcat(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvconcat(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorConcat::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorEq::BitVectorEq(RNG* rng,
                         uint64_t size,
                         BitVectorNode* child0,
                         BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == 1);
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorEq::BitVectorEq(RNG* rng,
                         const BitVectorDomain& domain,
                         BitVectorNode* child0,
                         BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == 1);
  _evaluate_and_set_domain();
}

void
BitVectorEq::_evaluate()
{
  d_assignment.ibveq(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorEq::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorEq::evaluate()
{
  _evaluate();
}

bool
BitVectorEq::is_invertible(const BitVector& t,
                           uint64_t pos_x,
                           bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: true
   * IC:    t = 0: (hi_x != lo_x) || (hi_x != s)
   *        t = 1: mcb(x, s)
   *
   * Inverse value:
   *   t = 0: random bit-vector != s
   *   t = 1: s
   */

  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();

  if (x.has_fixed_bits())
  {
    // fixed: IC: x == s = t
    if (x.is_fixed())
    {
      if (x.lo().bveq(s).compare(t) == 0)
      {
        BV_NODE_CACHE_INVERSE_IF(x.lo());
        return true;
      }
      return false;
    }
    // IC: t = 0: (hi_x != lo_x) || (hi_x != s)
    if (t.is_false())
    {
      if (x.hi().compare(x.lo()) || x.hi().compare(s))
      {
        BitVector res;
        BitVectorDomainGenerator gen(x, d_rng);
        do
        {
          assert(gen.has_random());
          res = gen.random();
        } while (s.compare(res) == 0);
        // Inverse value: random bit-vector != s
        BV_NODE_CACHE_INVERSE_IF(std::move(res));
        return true;
      }
      return false;
    }
    // IC: t = 1: mcb(x, s)
    if (x.match_fixed_bits(s))
    {
      // Inverse value: s
      BV_NODE_CACHE_INVERSE_IF(s);
      return true;
    }
    return false;
  }

  if (!is_essential_check)
  {
    if (t.is_false())
    {
      BitVector res;
      do
      {
        res = BitVector(x.size(), *d_rng);
      } while (s.compare(res) == 0);
      BV_NODE_CACHE_INVERSE(std::move(res));
    }
    else
    {
      BV_NODE_CACHE_INVERSE(s);
    }
  }
  return true;
}

bool
BitVectorEq::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    true
   *
   * Consistent value: random value
   */

  (void) t;
  const BitVectorDomain& x = child(pos_x)->domain();
  if (x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      BV_NODE_CACHE_CONSISTENT(x.lo());
    }
    else
    {
      BitVectorDomainGenerator gen(x, d_rng);
      // Consistent value: random value
      BV_NODE_CACHE_CONSISTENT(gen.random());
    }
  }
  else
  {
    // Consistent value: random value
    BV_NODE_CACHE_CONSISTENT(BitVector(x.size(), *d_rng));
  }
  return true;
}

const BitVector&
BitVectorEq::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(t.compare(d_inverse->bveq(s)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorEq::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorMul::BitVectorMul(RNG* rng,
                           uint64_t size,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == child0->size());
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorMul::BitVectorMul(RNG* rng,
                           const BitVectorDomain& domain,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == child0->size());
  _evaluate_and_set_domain();
}

void
BitVectorMul::_evaluate()
{
  d_assignment.ibvmul(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorMul::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorMul::evaluate()
{
  _evaluate();
}

void
BitVectorMul::compute_min_max_bounds(const BitVector& s,
                                     const BitVector& t,
                                     uint64_t pos_x,
                                     BitVector& res_min_u,
                                     BitVector& res_max_u,
                                     BitVector& res_min_s,
                                     BitVector& res_max_s)
{
  (void) t;

  assert(res_min_u.is_null());
  assert(res_max_u.is_null());
  assert(res_min_s.is_null());
  assert(res_max_s.is_null());

  uint64_t size = s.size();
  res_min_u     = BitVector::mk_zero(size);
  res_max_u     = BitVector::mk_ones(size);

  // tighten unsigned bounds wrt. to current unsigned bounds of x
  child(pos_x)->tighten_bounds(&res_min_u,
                               &res_max_u,
                               nullptr,
                               nullptr,
                               res_min_u,
                               res_max_u,
                               res_min_s,
                               res_max_s);
}

bool
BitVectorMul::is_invertible(const BitVector& t,
                            uint64_t pos_x,
                            bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: ((-s | s) & t) = t
   * IC:    IC_wo &&
   *        (s = 0 || ((odd(s) => mcb(x, t * s^-1)) &&
   *                  (!odd(s) => mcb (x << c, y << c))))
   *        with c = ctz(s) and y = (t >> c) * (s >> c)^-1
   * TODO: + bounds
   *
   * Inverse value:
   *   s = 0 (=> t = 0): random bit-vector
   *   s odd           : multiplicative inverse s^-1
   *   s even          : random value in domain
   *                     x[size - 1:size - ctz] o y[size - ctz(s) - 1:0]
   *                     with y = (t >> ctz(s)) * (s >> ctz(s))^-1
   * TODO: + bounds
   */
  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();

  // IC_wo: ((-s | s) & t) = t
  bool ic_wo = s.bvneg().ibvor(s).ibvand(t).compare(t) == 0;

  if (ic_wo)
  {
    BitVector min_lo, max_lo, min_hi, max_hi;
    compute_normalized_bounds(s, t, pos_x, min_lo, max_lo, min_hi, max_hi);
    if (min_lo.is_null() && min_hi.is_null())
    {
      return false;
    }

    if (x.has_fixed_bits())
    {
      // fixed: IC: x * s = t
      if (x.is_fixed())
      {
        const BitVector& xval = x.lo();
        if (xval.bvmul(s).compare(t) == 0
            && is_in_bounds(xval, min_lo, max_lo, min_hi, max_hi))
        {
          BV_NODE_CACHE_INVERSE_IF(xval);
          return true;
        }
        return false;
      }

      // IC: IC_wo && s != 0 &&
      //     ((odd(s) => mcb(x, t * s^-1)) && (!odd(s) => mcb (x << c, y << c)))
      //     with c = ctz(s) and y = (t >> c) * (s >> c)^-1
      if (!s.is_zero())
      {
        /*-- s odd ------------------------------*/

        if (s.lsb())
        {
          // IC: odd: mcb(x, t * s^-1)
          BitVector inv = s.bvmodinv().ibvmul(t);  // s^-1
          if (x.match_fixed_bits(inv)
              && is_in_bounds(inv, min_lo, max_lo, min_hi, max_hi))
          {
            // Inverse value: s^-1
            BV_NODE_CACHE_INVERSE_IF(std::move(inv));
            return true;
          }
          return false;
        }

        /*-- s even -----------------------------*/

        // IC: even: mcb (x << c, y << c)
        //
        // Check if relevant bits of
        //   y = (t >> ctz(s)) * (s >> ctz(s))^-1
        // match corresponding constant bits of x, i.e.,
        // mcb(x[size - ctz(s) - 1:0], y[size - ctz(s) - 1:0]).
        uint64_t size   = x.size();
        uint64_t ctz    = s.count_trailing_zeros();
        BitVector y_ext = t.bvshr(ctz)
                              .ibvmul(s.bvshr(ctz).ibvmodinv())
                              .ibvextract(size - ctz - 1, 0);
        if (x.bvextract(size - ctz - 1, 0).match_fixed_bits(y_ext))
        {
          // Result domain is x[size - 1:size - ctz] o y[size - ctz(s) - 1:0]
          BitVectorDomain d(x.bvextract(size - 1, size - ctz).bvconcat(y_ext));
          if (d.is_fixed())
          {
            if (is_in_bounds(d.lo(), min_lo, max_lo, min_hi, max_hi))
            {
              // Inverse value: random value in domain
              //                x[size - 1:size - ctz] o y[size - ctz(s) - 1:0]
              //                with y = (t >> ctz(s)) * (s >> ctz(s))^-1
              BV_NODE_CACHE_INVERSE_IF(d.lo());
              return true;
            }
            return false;
          }
          BitVectorDomainDualGenerator gen(
              d,
              d_rng,
              min_lo.is_null() ? nullptr : &min_lo,
              max_lo.is_null() ? nullptr : &max_lo,
              min_hi.is_null() ? nullptr : &min_hi,
              max_hi.is_null() ? nullptr : &max_hi);
          if (gen.has_random())
          {
            BV_NODE_CACHE_INVERSE_IF(gen.random());
            return true;
          }
          return false;
        }
        return false;
      }
      // IC: IC_wo && s = 0
      BitVectorDomainDualGenerator gen(x,
                                       d_rng,
                                       min_lo.is_null() ? nullptr : &min_lo,
                                       max_lo.is_null() ? nullptr : &max_lo,
                                       min_hi.is_null() ? nullptr : &min_hi,
                                       max_hi.is_null() ? nullptr : &max_hi);
      if (gen.has_random())
      {
        // Inverse value: s = 0: random value
        BV_NODE_CACHE_INVERSE_IF(gen.random());
        return true;
      }
      return false;
    }

    // no fixed bits
    if (s.is_zero())
    {
      // Inverse value: s = 0 (=> t = 0): random value
      BV_NODE_CACHE_INVERSE_IF(
          BitVector(x.size(), *d_rng, min_lo, max_lo, min_hi, max_hi));
      return true;
    }
    if (s.lsb())
    {
      BitVector inv = t.bvmul(s.bvmodinv());
      if (is_in_bounds(inv, min_lo, max_lo, min_hi, max_hi))
      {
        // Inverse value: s odd : s^-1 (unique solution)
        BV_NODE_CACHE_INVERSE_IF(std::move(inv));
        return true;
      }
      return false;
    }
    else
    {
      // s even: multiple solutions possible
      //         + s = 2^n: t >> n
      //                    with all bits shifted in randomly set to 0 or 1
      //         + s = 2^n * m, m is odd: c * m^-1
      //                                  with c = t >> n and
      //                                  all bits shifted in set randomly and
      //                                  m^-1 the mod inverse of m
      assert(t.count_trailing_zeros() >= s.count_trailing_zeros());
      uint64_t n    = s.count_trailing_zeros();
      uint64_t size = s.size();
      BitVector right;
      if (s.is_power_of_two())
      {
        right = t.bvextract(size - 1, n);
      }
      else
      {
        right = s.bvshr(n)
                    .ibvmodinv()
                    .ibvmul(t.bvshr(n))
                    .ibvextract(size - n - 1, 0);
      }
      BitVectorDomain d = BitVectorDomain(size - right.size()).bvconcat(right);
      BitVectorDomainDualGenerator gen(d,
                                       d_rng,
                                       min_lo.is_null() ? nullptr : &min_lo,
                                       max_lo.is_null() ? nullptr : &max_lo,
                                       min_hi.is_null() ? nullptr : &min_hi,
                                       max_hi.is_null() ? nullptr : &max_hi);
      if (gen.has_random())
      {
        // Inverse value: random value in domain
        //                x[size - 1:size - ctz] o y[size - ctz(s) - 1:0]
        //                with y = (t >> ctz(s)) * (s >> ctz(s))^-1
        //                Note: (s >> ctz(s)) = 1 if s is a power of 2
        BV_NODE_CACHE_INVERSE_IF(gen.random());
        return true;
      }
      return false;
    }
  }

  return ic_wo;
}

bool
BitVectorMul::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    (t != 0 => xhi != 0) &&
   *        (odd(t) => xhi[lsb] != 0) &&
   *        (!odd(t) => \exists y. (mcb(x, y) && ctz(t) >= ctz(y))
   *
   * Consistent value:
   *   t = 0: random value
   *   t > 0: t odd : random odd value
   *          t even: random even value > 0 with ctz(x) <= ctz(t)
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t size            = t.size();
  if (x.has_fixed_bits())
  {
    // CC: (t != 0 => xhi != 0)
    if (x.hi().is_zero())
    {
      if (t.is_zero())
      {
        // fixed: x = 0
        BV_NODE_CACHE_CONSISTENT(x.hi());
        return true;
      }
      return false;
    }

    // CC: t odd: xhi[lsb] != 0)
    if (t.lsb())
    {
      if (!x.hi().lsb())
      {
        return false;
      }
      if (x.is_fixed())
      {
        // fixed: x * s = t
        BV_NODE_CACHE_CONSISTENT(x.lo());
      }
      else
      {
        // Consistent value: t = odd: random odd value
        BitVectorDomainGenerator gen(x, d_rng, BitVector::mk_one(size), x.hi());
        BV_NODE_CACHE_CONSISTENT(gen.random());
        if (!d_consistent->lsb())
        {
          assert(!x.is_fixed_bit_false(0));
          d_consistent->set_bit(0, true);
        }
      }
      return true;
    }

    // CC: t even: \exists y. (mcb(x, y) && ctz(t) >= ctz(y))
    uint64_t ctz_t = t.count_trailing_zeros();
    BitVectorDomainGenerator gen(
        x,
        d_rng,
        t.is_zero() ? BitVector::mk_zero(size) : BitVector::mk_one(size),
        x.hi());
    assert(gen.has_random() || x.is_fixed());
    BitVector tmp = gen.has_random() ? gen.random() : x.lo();

    bool res = false;
    for (uint64_t i = 0; i < size && i <= ctz_t; ++i)
    {
      if (!x.is_fixed_bit_false(i))
      {
        res = true;
        break;
      }
    }
    if (res)
    {
      if (ctz_t < size)
      {
        uint64_t i;
        do
        {
          i = d_rng->pick<uint64_t>(0, ctz_t);
        } while (x.is_fixed_bit_false(i));
        tmp.set_bit(i, true);
      }
      // Consistent value: t = even: random even value > 0 with ctz(x) <= ctz(t)
      d_consistent.reset(new BitVector(tmp));
      return true;
    }
    return false;
  }

  // no fixed bits
  if (t.is_zero())
  {
    // Consistent value: t = 0: random value
    BV_NODE_CACHE_CONSISTENT(BitVector(x.size(), *d_rng));
  }
  else
  {
    d_consistent.reset(new BitVector(BitVector(
        x.size(), *d_rng, BitVector::mk_one(size), BitVector::mk_ones(size))));

    if (t.lsb())
    {
      // Consistent value: t = odd: random odd value
      if (!d_consistent->lsb())
      {
        d_consistent->set_bit(0, true);
      }
    }
    else
    {
      // Consistent value: t = even: random even value > 0 with ctz(x) <= ctz(t)
      assert(!x.has_fixed_bits());
      uint64_t ctz_t = t.count_trailing_zeros();
      /* choose consistent value as 2^n with prob 0.1 */
      if (d_rng->pick_with_prob(100))
      {
        d_consistent->iset(0);
        d_consistent->set_bit(d_rng->pick<uint64_t>(0, ctz_t - 1), true);
      }
      /* choose consistent value as t / 2^n with prob 0.1 */
      else if (d_rng->pick_with_prob(100))
      {
        d_consistent->iset(t);
        uint64_t r = d_rng->pick<uint64_t>(0, ctz_t);
        if (r > 0)
        {
          d_consistent->ibvshr(r);
        }
      }
      /* choose random value with ctz(t) >= ctz(res) with prob 0.8 */
      else
      {
        if (d_consistent->count_trailing_zeros() > ctz_t)
        {
          d_consistent->set_bit(d_rng->pick<uint64_t>(0, ctz_t - 1), true);
        }
      }
    }
  }
  return true;
}

const BitVector&
BitVectorMul::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(pos_x == 1 || t.compare(d_inverse->bvmul(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvmul(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorMul::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorShl::BitVectorShl(RNG* rng,
                           uint64_t size,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == child0->size());
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorShl::BitVectorShl(RNG* rng,
                           const BitVectorDomain& domain,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == child0->size());
  _evaluate_and_set_domain();
}

void
BitVectorShl::_evaluate()
{
  d_assignment.ibvshl(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorShl::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorShl::evaluate()
{
  _evaluate();
}

bool
BitVectorShl::is_invertible(const BitVector& t,
                            uint64_t pos_x,
                            bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: pos_x = 0: (t >> s) << s = t
   *        pos_x = 1: ctz(s) <= ctz(t) &&
   *                   ((t = 0) || (s << (ctz(t) - ctz(s))) = t)
   * IC:    pos_x = 0: IC_wo && mcb(x << s, t)
   *        pos_x = 1: IC_wo &&
   *                   ((t = 0) => (hi_x >= ctz(t) - ctz(s) || (s = 0))) &&
   *                   ((t != 0) => mcb(x, ctz(t) - ctz(s)))
   *
   * Inverse value:
   *   pos_x = 0: t >> s (with bits shifted in set randomly)
   *   pos_x = 1: s = 0 && t = 0: random
   *              else          : shift = ctz(t) - ctz(s)
   *                              + t = 0: shift <= res < size
   *                              + else : shift
   */

  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t ctz_t           = 0;
  uint64_t ctz_s           = 0;
  bool x_has_fixed_bits    = x.has_fixed_bits();
  bool ic;

  // IC_wo: pos_x = 0: (t >> s) << s = t
  if (pos_x == 0)
  {
    ic = t.bvshr(s).ibvshl(s).compare(t) == 0;
  }
  // IC_wo: pos_x = 1: ctz(s) <= ctz(t) &&
  else
  {
    assert(pos_x == 1);
    ctz_t = t.count_trailing_zeros();
    ctz_s = s.count_trailing_zeros();
    ic    = ctz_s <= ctz_t
         && (t.is_zero() || s.bvshl(ctz_t - ctz_s).compare(t) == 0);
  }

  // IC
  if (ic)
  {
    // fixed: x << s = t
    if (x.is_fixed())
    {
      const BitVector& xval = x.lo();
      if ((pos_x == 0 && xval.bvshl(s).compare(t) == 0)
          || (pos_x == 1 && s.bvshl(xval).compare(t) == 0))
      {
        BV_NODE_CACHE_INVERSE_IF(xval);
        return true;
      }
      return false;
    }

    // IC: pos_x = 0: IC_wo && mcb(x << s, t)
    if (pos_x == 0)
    {
      if (x_has_fixed_bits)
      {
        ic = x.bvshl(s).match_fixed_bits(t);
      }
      if (ic && !is_essential_check)
      {
        // inverse value: t >> s (with bits shifted in set randomly)
        uint64_t size = x.size();
        // shift value can be normalized to fit into 64 bit (max bit-width
        // handled is UINT64_MAX)
        uint64_t shift;
        if (size > 64)
        {
          if (s.compare(BitVector::from_ui(s.size(), UINT64_MAX)) >= 0)
          {
            shift = UINT64_MAX;
          }
          else
          {
            shift = s.bvextract(63, 0).to_uint64();
          }
        }
        else
        {
          shift = s.to_uint64();
        }
        assert(shift >= size || t.count_trailing_zeros() >= shift);
        assert(shift < size || t.count_trailing_zeros() == size);
        // Inverse value: pos_x = 0: t >> s (with bits shifted in set randomly)
        if (shift >= size)
        {
          // random value
          if (x_has_fixed_bits)
          {
            BitVectorDomainGenerator gen(x, d_rng);
            assert(gen.has_random());
            BV_NODE_CACHE_INVERSE(gen.random());
          }
          else
          {
            BV_NODE_CACHE_INVERSE(BitVector(size, *d_rng));
          }
        }
        else if (shift > 0)
        {
          BitVector left;
          if (x_has_fixed_bits)
          {
            BitVectorDomain x_ext = x.bvextract(size - 1, size - shift);
            if (x_ext.is_fixed())
            {
              left = x_ext.lo();
            }
            else
            {
              BitVectorDomainGenerator gen(x_ext, d_rng);
              assert(gen.has_random());
              left = gen.random();
            }
          }
          else
          {
            left = BitVector(shift, *d_rng);
          }
          BV_NODE_CACHE_INVERSE(
              std::move(left.ibvconcat(t.bvextract(size - 1, shift))));
        }
        else
        {
          BV_NODE_CACHE_INVERSE(t);
        }
      }
    }
    else
    {
      // IC: pos_x = 1: IC_wo &&
      //                ((t = 0) => (hi_x >= ctz(t) - ctz(s) || (s = 0))) &&
      //                ((t != 0) => mcb(x, ctz(t) - ctz(s)))
      uint64_t size = x.size();
      assert(ctz_t >= ctz_s);
      if (t.is_zero())
      {
        if (s.is_zero())
        {
          if (!is_essential_check)
          {
            // Inverse value: s = 0: random value
            if (x_has_fixed_bits)
            {
              BitVectorDomainGenerator gen(x, d_rng, x.lo(), x.hi());
              assert(gen.has_random());
              BV_NODE_CACHE_INVERSE(gen.random());
            }
            else
            {
              BV_NODE_CACHE_INVERSE(BitVector(size, *d_rng));
            }
          }
          return true;
        }
        BitVector min = BitVector::from_ui(size, ctz_t - ctz_s);
        if (x_has_fixed_bits)
        {
          if (x.hi().compare(min) >= 0)
          {
            BitVectorDomainGenerator gen(x, d_rng, min, x.hi());
            assert(gen.has_random());
            // Inverse value: t = 0: ctz(t) - ctz(s) <= res < size
            BV_NODE_CACHE_INVERSE(gen.random());
            return true;
          }
          return false;
        }
        else
        {
          BV_NODE_CACHE_INVERSE(
              BitVector(size, *d_rng, min, BitVector::mk_ones(size)));
          return true;
        }
      }
      ic = !x_has_fixed_bits
           || x.match_fixed_bits(BitVector::from_ui(x.size(), ctz_t - ctz_s));
      if (ic && !is_essential_check)
      {
        // Inverse value: t != 0: ctz(t) - ctz(s)
        uint64_t shift = ctz_t - ctz_s;
        BV_NODE_CACHE_INVERSE(BitVector::from_ui(size, shift));
      }
    }
  }
  return ic;
}

bool
BitVectorShl::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    pos_x = 0: \exists y. (y <= ctz(t) /\ mcb(x << y, t))
   *        pos_x = 1: t = 0 \/ \exists y. (y <= ctz(t) /\ mcb(x, y))
   *
   * Consistent value:
   *   pos_x = 0: t = 0: random
   *              t > 0: random value with ctz(x) <= ctz(t)
   *   pos_x = 1: t = 0: random
   *              t > 0: random value <= ctz(t)
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  bool x_has_fixed_bits    = x.has_fixed_bits();
  uint64_t ctz_t           = t.count_trailing_zeros();
  uint64_t size            = t.size();

  if (pos_x == 0)
  {
    // CC: pos_x = 0: \exists y. (y <= ctz(t) /\ mcb(x << y, t))
    if (ctz_t == size)
    {
      // Consistent value: pos_x = 0: t = 0: random value
      if (x.has_fixed_bits())
      {
        if (x.is_fixed())
        {
          BV_NODE_CACHE_CONSISTENT(x.lo());
        }
        else
        {
          BitVectorDomainGenerator gen(x, d_rng);
          BV_NODE_CACHE_CONSISTENT(gen.random());
        }
      }
      else
      {
        d_consistent.reset(new BitVector(size, *d_rng));
      }
    }
    else
    {
      // Consistent value: pos_x = 0: t > 0: random value with ctz(x) <= ctz(t)
      if (x_has_fixed_bits)
      {
        if (x.is_fixed())
        {
          uint64_t ctz_x        = x.lo().count_trailing_zeros();
          const BitVector& xval = x.lo();
          if (xval.bvshl(ctz_t - ctz_x).compare(t) == 0)
          {
            d_consistent.reset(new BitVector(xval));
            return true;
          }
          return false;
        }

        std::vector<BitVector> stack;
        for (uint64_t i = 0; i <= ctz_t; ++i)
        {
          BitVectorDomain x_slice = x.bvextract(size - 1 - i, 0);
          BitVector t_slice       = t.bvextract(size - 1, i);
          if (x_slice.match_fixed_bits(t_slice)) stack.push_back(t_slice);
        }
        if (!stack.empty())
        {
          uint64_t i          = d_rng->pick<uint64_t>(0, stack.size() - 1);
          BitVector& right    = stack[i];
          uint64_t size_right = right.size();
          if (size == size_right)
          {
            d_consistent.reset(new BitVector(right));
          }
          else
          {
            BitVectorDomainGenerator gen(x, d_rng);
            assert(gen.has_random());
            d_consistent.reset(
                new BitVector(gen.random()
                                  .ibvextract(size - 1, size_right)
                                  .ibvconcat(right)));
          }
          return true;
        }
        return false;
      }
      else
      {
        uint64_t shift = d_rng->pick<uint64_t>(0, ctz_t);
        if (shift == 0)
        {
          d_consistent.reset(new BitVector(t));
        }
        else
        {
          d_consistent.reset(
              new BitVector(BitVector(shift, *d_rng)
                                .ibvconcat(t.bvextract(size - 1, shift))));
        }
        return true;
      }
    }
  }
  else
  {
    // CC: pos_x = 1: t = 0 \/ \exists y. (y <= ctz(t) /\ mcb(x, y))
    // Consistent value: pos_x = 1: random value <= ctz(t)
    uint64_t max = ctz_t < size ? ctz_t : ((1u << size) - 1);
    if (x_has_fixed_bits)
    {
      if (x.is_fixed())
      {
        if (BitVector::from_ui(size, max).compare(x.lo()) >= 0)
        {
          BV_NODE_CACHE_CONSISTENT(x.lo());
          return true;
        }
        return false;
      }

      BitVectorDomainGenerator gen(
          x, d_rng, x.lo(), BitVector::from_ui(size, max));
      if (gen.has_random())
      {
        BV_NODE_CACHE_CONSISTENT(gen.random());
        return true;
      }
      return false;
    }
    else
    {
      d_consistent.reset(new BitVector(
          BitVector::from_ui(size, d_rng->pick<uint64_t>(0, max))));
    }
  }
  return true;
}

const BitVector&
BitVectorShl::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(pos_x == 1 || t.compare(d_inverse->bvshl(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvshl(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorShl::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorShr::BitVectorShr(RNG* rng,
                           uint64_t size,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == child0->size());
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorShr::BitVectorShr(RNG* rng,
                           const BitVectorDomain& domain,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == child0->size());
  _evaluate_and_set_domain();
}

void
BitVectorShr::_evaluate()
{
  d_assignment.ibvshr(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorShr::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorShr::evaluate()
{
  _evaluate();
}

bool
BitVectorShr::is_invertible(const BitVector& t,
                            uint64_t pos_x,
                            bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();
  return is_invertible(
      d_rng, t, s, x, pos_x, is_essential_check ? nullptr : &d_inverse);
}

bool
BitVectorShr::is_invertible(RNG* rng,
                            const BitVector& t,
                            const BitVector& s,
                            const BitVectorDomain& x,
                            uint64_t pos_x,
                            std::unique_ptr<BitVector>* inverse)
{
  /**
   * IC_wo: pos_x = 0: (t << s) >> s = t
   *        pos_x = 1: clz(s) <= clz(t) &&
   *                   ((t = 0) || (s >> (clz(t) - clz(s))) = t)
   * IC:    pos_x = 0: IC_wo && mcb(x >> s, t)
   *        pos_x = 1: IC_wo &&
   *                   ((t = 0) => (hi_x >= clz(t) - clz(s) || (s = 0))) &&
   *                   ((t != 0) => mcb(x, clz(t) - clz(s)))
   *
   * Inverse value:
   *   pos_x = 0: t << s (with bits shifted in set randomly)
   *   pos_x = 1: s = 0 && t = 0: random
   *              else          : shift = clz(t) - clz(s)
   *                              + t = 0: shift <= res < size
   *                              + else : shift
   */
  uint64_t clz_t        = 0;
  uint64_t clz_s        = 0;
  bool x_has_fixed_bits = x.has_fixed_bits();
  bool ic;

  // IC_wo
  if (pos_x == 0)
  {
    // pos_x = 0: (t << s) >> s = t
    ic = t.bvshl(s).ibvshr(s).compare(t) == 0;
  }
  else
  {
    // pos_x = 1: clz(s) <= clz(t) && ((t = 0) || (s >> (clz(t) - clz(s))) = t)
    assert(pos_x == 1);
    clz_t = t.count_leading_zeros();
    clz_s = s.count_leading_zeros();
    ic    = clz_s <= clz_t
         && (t.is_zero() || s.bvshr(clz_t - clz_s).compare(t) == 0);
  }

  // IC
  if (ic)
  {
    if (pos_x == 0)
    {
      // IC: pos_x = 0: IC_wo && mcb(x >> s, t)
      if (x_has_fixed_bits)
      {
        if (x.is_fixed())
        {
          ic = x.lo().bvshr(s).compare(t) == 0;
        }
        else
        {
          ic = x.bvshr(s).match_fixed_bits(t);
        }
      }
    }
    else
    {
      // IC: pos_x = 1: IC_wo &&
      //                ((t = 0) => (hi_x >= clz(t) - clz(s) || (s = 0))) &&
      //                ((t != 0) => mcb(x, clz(t) - clz(s)))
      uint64_t size = x.size();
      assert(clz_t >= clz_s);
      if (x.is_fixed())
      {
        ic = s.bvshr(x.lo()).compare(t) == 0;
      }
      else if (t.is_zero())
      {
        if (x_has_fixed_bits && !s.is_zero())
        {
          BitVector min = BitVector::from_ui(size, clz_t - clz_s);
          ic            = x.hi().compare(min) >= 0;
        }
      }
      else if (x_has_fixed_bits)
      {
        ic = x.match_fixed_bits(BitVector::from_ui(x.size(), clz_t - clz_s));
      }
    }
  }
  if (ic && inverse)
  {
    inverse_value(rng, t, s, x, pos_x, *inverse);
  }
  return ic;
}

bool
BitVectorShr::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    pos_x = 0: \exists y. (y <= clz(t) /\ mcb(x >> y, t))
   *        pos_x = 1: t = 0 \/ \exists y. (y <= clz(t) /\ mcb(x, y))
   *
   * Consistent value:
   *   pos_x = 0: t = 0: random
   *              t > 0: random value with clz(x) <= clz(t)
   *   pos_x = 1: t = 0: random
   *              t > 0: random value <= clz(t)
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t clz_t = t.count_leading_zeros();
  uint64_t size  = t.size();
  bool x_has_fixed_bits    = x.has_fixed_bits();

  if (pos_x == 0)
  {
    // CC: pos_x = 0: \exists y. (y <= clz(t) /\ mcb(x >> y, t))
    if (clz_t == size)
    {
      // Consistent value: pos_x = 0: t = 0: random
      if (x.has_fixed_bits())
      {
        if (x.is_fixed())
        {
          BV_NODE_CACHE_CONSISTENT(x.lo());
        }
        else
        {
          BitVectorDomainGenerator gen(x, d_rng);
          BV_NODE_CACHE_CONSISTENT(gen.random());
        }
      }
      else
      {
        d_consistent.reset(new BitVector(size, *d_rng));
      }
    }
    else
    {
      // Consistent value: pos_x = 0: t > 0: random value with clz(x) <= clz(t)
      //                   pos_x = 1: t = 0: random
      //                              t > 0: random value <= clz(t)
      if (x_has_fixed_bits)
      {
        // fixed
        if (x.is_fixed())
        {
          uint64_t clz_x        = x.lo().count_leading_zeros();
          const BitVector& xval = x.lo();
          if (xval.bvshr(clz_t - clz_x).compare(t) == 0)
          {
            d_consistent.reset(new BitVector(xval));
            return true;
          }
          return false;
        }

        std::vector<BitVector> stack;
        for (uint64_t i = 0; i <= clz_t; ++i)
        {
          BitVectorDomain x_slice = x.bvextract(size - 1, i);
          BitVector t_slice       = t.bvextract(size - 1 - i, 0);
          if (x_slice.match_fixed_bits(t_slice)) stack.push_back(t_slice);
        }
        if (!stack.empty())
        {
          uint64_t i         = d_rng->pick<uint64_t>(0, stack.size() - 1);
          BitVector& left    = stack[i];
          uint64_t size_left = left.size();
          if (size == size_left)
          {
            d_consistent.reset(new BitVector(left));
          }
          else
          {
            BitVectorDomainGenerator gen(x, d_rng);
            assert(gen.has_random());
            d_consistent.reset(new BitVector(left.ibvconcat(
                gen.random().ibvextract(size - 1 - size_left, 0))));
          }
          return true;
        }
        return false;
      }
      else
      {
        uint64_t shift = d_rng->pick<uint64_t>(0, clz_t);
        if (shift == 0)
        {
          d_consistent.reset(new BitVector(t));
        }
        else
        {
          d_consistent.reset(
              new BitVector(t.bvextract(size - shift - 1, 0)
                                .ibvconcat(BitVector(shift, *d_rng))));
        }
        return true;
      }
    }
  }
  else
  {
    // CC: pos_x = 1: t = 0 \/ \exists y. (y <= clz(t) /\ mcb(x, y))
    uint64_t max = clz_t < size ? clz_t : ((1u << size) - 1);
    if (x_has_fixed_bits)
    {
      if (x.is_fixed())
      {
        if (BitVector::from_ui(size, max).compare(x.lo()) >= 0)
        {
          BV_NODE_CACHE_CONSISTENT(x.lo());
          return true;
        }
        return false;
      }

      BitVectorDomainGenerator gen(
          x, d_rng, x.lo(), BitVector::from_ui(size, max));
      if (gen.has_random())
      {
        BV_NODE_CACHE_CONSISTENT(gen.random());
        return true;
      }
      return false;
    }
    else
    {
      d_consistent.reset(new BitVector(
          BitVector::from_ui(size, d_rng->pick<uint64_t>(0, max))));
    }
  }
  return true;
}

const BitVector&
BitVectorShr::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(pos_x == 1 || t.compare(d_inverse->bvshr(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvshr(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

void
BitVectorShr::inverse_value(RNG* rng,
                            const BitVector& t,
                            const BitVector& s,
                            const BitVectorDomain& x,
                            uint64_t pos_x,
                            std::unique_ptr<BitVector>& inverse)
{
  uint64_t size = x.size();
  if (pos_x == 0)
  {
    // pos_x = 0: t << s (with bits shifted in set randomly)
    if (x.is_fixed())
    {
      inverse.reset(new BitVector(x.lo()));
    }
    else
    {
      // shift value can be normalized to fit into 64 bit (max bit-width
      // handled is UINT64_MAX)
      uint64_t shift;
      if (size > 64)
      {
        if (s.compare(BitVector::from_ui(s.size(), UINT64_MAX)) >= 0)
        {
          shift = UINT64_MAX;
        }
        else
        {
          shift = s.bvextract(63, 0).to_uint64();
        }
      }
      else
      {
        shift = s.to_uint64();
      }
      if (shift >= size)
      {
        // random value
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x, rng);
          assert(gen.has_random());
          inverse.reset(new BitVector(gen.random()));
        }
        else
        {
          inverse.reset(new BitVector(size, *rng));
        }
      }
      else if (shift > 0)
      {
        BitVector right;
        if (x.has_fixed_bits())
        {
          BitVectorDomain x_ext = x.bvextract(shift - 1, 0);
          if (x_ext.is_fixed())
          {
            right = x_ext.lo();
          }
          else
          {
            BitVectorDomainGenerator gen(x_ext, rng);
            assert(gen.has_random());
            right = gen.random();
          }
        }
        else
        {
          right = BitVector(shift, *rng);
        }
        inverse.reset(new BitVector(
            std::move(t.bvextract(size - shift - 1, 0).ibvconcat(right))));
      }
      else
      {
        inverse.reset(new BitVector(t));
      }
    }
  }
  else
  {
    // pos_x = 1: s = 0 && t = 0: random
    //            else          : shift = clz(t) - clz(s)
    //                            + t = 0: shift <= res < size
    //                            + else : shift
    if (x.is_fixed())
    {
      inverse.reset(new BitVector(x.lo()));
    }
    else
    {
      bool t_is_zero = t.is_zero();
      if (t_is_zero && s.is_zero())
      {
        // random value
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x, rng, x.lo(), x.hi());
          assert(gen.has_random());
          inverse.reset(new BitVector(gen.random()));
        }
        else
        {
          inverse.reset(new BitVector(size, *rng));
        }
      }
      else if (t_is_zero)
      {
        uint64_t clz_t = t.count_leading_zeros();
        uint64_t clz_s = s.count_leading_zeros();
        BitVector min  = BitVector::from_ui(size, clz_t - clz_s);
        assert(x.hi().compare(min) >= 0);
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x, rng, min, x.hi());
          assert(gen.has_random());
          inverse.reset(new BitVector(gen.random()));
        }
        else
        {
          inverse.reset(
              new BitVector(size, *rng, min, BitVector::mk_ones(size)));
        }
      }
      else
      {
        uint64_t clz_t = t.count_leading_zeros();
        uint64_t clz_s = s.count_leading_zeros();
        uint64_t shift = clz_t - clz_s;
        assert(
            !x.has_fixed_bits()
            || x.match_fixed_bits(BitVector::from_ui(x.size(), clz_t - clz_s)));
        inverse.reset(new BitVector(BitVector::from_ui(size, shift)));
      }
    }
  }
}

const BitVector&
BitVectorShr::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorAshr::BitVectorAshr(RNG* rng,
                             uint64_t size,
                             BitVectorNode* child0,
                             BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == child0->size());
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorAshr::BitVectorAshr(RNG* rng,
                             const BitVectorDomain& domain,
                             BitVectorNode* child0,
                             BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == child0->size());
  _evaluate_and_set_domain();
}

void
BitVectorAshr::_evaluate()
{
  d_assignment.ibvashr(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorAshr::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorAshr::evaluate()
{
  _evaluate();
}

bool
BitVectorAshr::is_invertible(const BitVector& t,
                             uint64_t pos_x,
                             bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: pos_x = 0: (s < size(s) => (t << s) >>a s = t) &&
   *                   (s >= size(s) => (t = ones || t = 0))
   *        pos_x = 1: (s[msb] = 0 => IC_shr(s >> x = t) &&
   *                   (s[msb] = 1 => IC_shr(~s >> x = ~t)
   *
   * IC:    pos_x = 0: IC_wo && mcb(x >>a s, t)
   *        pos_x = 1: IC_wo &&
   *                     (s[msb] = 0 => IC_shr) &&
   *                     (s[msb] = 1 => IC_shr(~s >> x = ~t))
   *
   * Inverse value:
   *   pos_x = 0: IV_shr(x >> s = t) with msb = t[msb]
   *   pos_x = 1: s = 0 && t = 0: random
   *              else          : shift = cnt(t) - cnt(s)
   *                              with cnt = clz if t[msb] = 0 else clo
   *                              + t = 0: shift <= res < size
   *                              + else : shift
   */

  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();
  BitVector snot, tnot, sshr;
  bool ic;

  if (pos_x == 0)
  {
    uint64_t size = s.size();
    // IC_wo
    if (s.compare(BitVector::from_ui(size, size)) < 0)
    {
      // pos_x = 0: (s < size(s) => (t << s) >>a s = t)
      ic = t.bvshl(s).ibvashr(s).compare(t) == 0;
    }
    else
    {
      // pos_x = 0: (s >= size(s) => (t = ones || t = 0))
      ic = t.is_zero() || t.is_ones();
    }

    // IC: pos_x = 0: IC_wo && mcb(x >>a s, t)
    ic = ic && (!x.has_fixed_bits() || x.bvashr(s).match_fixed_bits(t));
    if (ic && !is_essential_check)
    {
      // Inverse value: pos_x = 0: IV_shr(x >> s = t) with msb = t[msb]
      BitVectorShr::inverse_value(d_rng, t, s, x, 0, d_inverse);
      d_inverse->set_bit(size - 1, t.msb());
    }
    return ic;
  }

  // IC_wo: pos_x = 1: (s[msb] = 0 => IC_shr(s >> x = t)
  // IC:    pos_x = 1: IC_wo && (s[msb] = 1 => IC_shr(~s >> x = ~t))
  if (s.msb())
  {
    return BitVectorShr::is_invertible(
        d_rng,
        t.bvnot(),
        s.bvnot(),
        x,
        pos_x,
        is_essential_check ? nullptr : &d_inverse);
  }
  // IC_wo: pos_x = 1: (s[msb] = 1 => IC_shr(~s >> x = ~t)
  // IC:    pos_x = 1: IC_wo && (s[msb ] = 0 => IC_shr)
  return BitVectorShr::is_invertible(
      d_rng, t, s, x, pos_x, is_essential_check ? nullptr : &d_inverse);
}

bool
BitVectorAshr::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC: pos_x = 0:
   *       ((t = 0 \/ t = ones) => \exists y. (y[msb] = t[msb] /\ mcb(x, y))) /\
   *       ((t != 0 /\ t != ones) => \exists y. (
   *          c => y <= clo(t) /\ ~c => y <= clz(t) /\ mcb(x, y))
   *       with c = ((t << y)[msb] = 1)
   *     pos_x = 1:
   *       t = 0 \/ t = ones \/
   *       \exists y. (c => y < clo(t) /\ ~c => y < clz(t) /\ mcb(x, y)
   *       with c = (t[msb] = 1)
   *
   * Consistent value:
   *   pos_x = 0: t = 0: random
   *              t > 0: random value with cnt(x) < cnt(t)
   *   pos_x = 1: t = 0: random
   *              t > 0: random value < cnt(t)
   *   with cnt = clz if t[msb] = 0 and cnt = clo if t[msb] = 1
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  bool is_signed           = t.msb();
  uint64_t cnt_t = is_signed ? t.count_leading_ones() : t.count_leading_zeros();
  uint64_t size  = t.size();

  if (pos_x == 0)
  {
    // fixed: x <<a s = t
    if (x.is_fixed())
    {
      uint64_t cnt_x = is_signed ? x.lo().count_leading_ones()
                                 : x.lo().count_leading_zeros();
      if (x.lo().bvashr(cnt_t - cnt_x).compare(t) == 0)
      {
        BV_NODE_CACHE_CONSISTENT(x.lo());
        return true;
      }
      return false;
    }
    // CC: pos_x = 0:
    //     ((t = 0 \/ t = ones) => \exists y. (y[msb] = t[msb] /\ mcb(x, y)))
    if (!is_signed && t.is_zero())
    {
      if (x.has_fixed_bits())
      {
        BitVectorDomainSignedGenerator gen(
            x, d_rng, BitVector::mk_zero(size), BitVector::mk_max_signed(size));
        if (gen.has_random())
        {
          // Consistent value: pos_x = 0: t = 0: random value
          BV_NODE_CACHE_CONSISTENT(gen.random());
          return true;
        }
        return false;
      }
    }
    if (is_signed && t.is_ones())
    {
      if (x.has_fixed_bits())
      {
        BitVectorDomainSignedGenerator gen(
            x, d_rng, BitVector::mk_min_signed(size), BitVector::mk_ones(size));
        if (gen.has_random())
        {
          // Consistent value:
          // pos_x = 0: t > 0: random value with cnt(x) < cnt(t)
          BV_NODE_CACHE_CONSISTENT(gen.random());
          return true;
        }
        return false;
      }
    }

    // Consistent value: cnt(t) = size: random value with msb set to t[msb]
    if (cnt_t == size)
    {
      if (x.has_fixed_bits())
      {
        BitVectorDomainGenerator gen(x, d_rng);
        BV_NODE_CACHE_CONSISTENT(gen.random());
      }
      else
      {
        d_consistent.reset(new BitVector(size, *d_rng));
      }
      if (is_signed && !d_consistent->msb())
      {
        d_consistent->set_bit(size - 1, true);
      }
      else if (!is_signed && d_consistent->msb())
      {
        d_consistent->set_bit(size - 1, false);
      }
      return true;
    }

    // CC: pos_x = 0:
    //     ((t != 0 /\ t != ones) => \exists y. (
    //        c => y <= clo(t) /\ ~c => y <= clz(t) /\ mcb(x, y))
    //     with c = ((t << y)[msb] = 1)
    if (x.has_fixed_bits())
    {
      std::vector<BitVector> stack;
      for (uint64_t i = 0; i < cnt_t; ++i)
      {
        BitVectorDomain x_slice = x.bvextract(size - 1, i);
        BitVector t_slice       = t.bvextract(size - 1 - i, 0);
        if (x_slice.match_fixed_bits(t_slice)) stack.push_back(t_slice);
      }
      if (!stack.empty())
      {
        uint64_t i         = d_rng->pick<uint64_t>(0, stack.size() - 1);
        BitVector& left    = stack[i];
        uint64_t size_left = left.size();
        if (size == size_left)
        {
          d_consistent.reset(new BitVector(left));
        }
        else
        {
          BitVectorDomainGenerator gen(x, d_rng);
          assert(gen.has_random());
          d_consistent.reset(new BitVector(
              left.bvconcat(gen.random().ibvextract(size - 1 - size_left, 0))));
        }
        return true;
      }
      return false;
    }

    uint64_t shift = d_rng->pick<uint64_t>(0, cnt_t - 1);
    if (shift == 0)
    {
      d_consistent.reset(new BitVector(t));
    }
    else
    {
      d_consistent.reset(
          new BitVector(t.bvextract(size - shift - 1, 0)
                            .ibvconcat(BitVector(shift, *d_rng))));
    }
    return true;
  }
  // CC: pos_x = 1:
  //     t = 0 \/ t = ones \/
  //     \exists y. (c => y < clo(t) /\ ~c => y < clz(t) /\ mcb(x, y)
  //     with c = (t[msb] = 1)
  if (x.is_fixed())
  {
    if (t.is_zero() || t.is_ones()
        || BitVector::from_ui(size, cnt_t).compare(x.lo()) > 0)
    {
      BV_NODE_CACHE_CONSISTENT(x.lo());
      return true;
    }
    return false;
  }
  // Consistent value:
  //   pos_x = 1: t = 0: random value
  //              t > 0: random value < cnt(t)
  uint64_t max = cnt_t < size ? cnt_t - 1 : ((1u << size) - 1);
  if (x.has_fixed_bits())
  {
    BitVectorDomainGenerator gen(
        x, d_rng, BitVector::mk_zero(size), BitVector::from_ui(size, max));
    if (gen.has_random())
    {
      BV_NODE_CACHE_CONSISTENT(gen.random());
      return true;
    }
    return false;
  }
  d_consistent.reset(
      new BitVector(BitVector::from_ui(size, d_rng->pick<uint64_t>(0, max))));
  return true;
}

const BitVector&
BitVectorAshr::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(pos_x == 1 || t.compare(d_inverse->bvashr(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvashr(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorAshr::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorUdiv::BitVectorUdiv(RNG* rng,
                             uint64_t size,
                             BitVectorNode* child0,
                             BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == child0->size());
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorUdiv::BitVectorUdiv(RNG* rng,
                             const BitVectorDomain& domain,
                             BitVectorNode* child0,
                             BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == child0->size());
  _evaluate_and_set_domain();
}

void
BitVectorUdiv::_evaluate()
{
  d_assignment.ibvudiv(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorUdiv::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorUdiv::evaluate()
{
  _evaluate();
}

bool
BitVectorUdiv::is_invertible(const BitVector& t,
                             uint64_t pos_x,
                             bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: pos_x = 0: (s * t) / s = t
   *        pos_x = 1: s / (s / t) = t
   * IC:    pos_x = 0: IC_wo &&
   *                   (t = 0 => lo_x < s) &&
   *                   ((t != 0 && s != 0 ) => \exists y. (
   *                       mcb(x, y) && (~c => y < s * t + 1) &&
   *                       (c => y <= ones)))
   *                   with c = umulo(s, t + 1) && uaddo(t, 1)
   *        pos_x = 1: IC_wo &&
   *                   (t != ones => hi_x > 0) &&   (covered by is_fixed check)
   *                   ((s != 0 || t != 0) => (s / hi_x <= t) && \exists y. (
   *                       mcb(x, y) &&
   *                       (t = ones => y <= s / t) &&
   *                       (t != ones => y > t + 1 && y <= s / t)))
   *
   * Inverse value:
   *   pos_x = 0: t = ones: s = 1: ones
   *              s = 0: random value
   *              s * t does not overflow: - s * t
   *                                       - v with v / s = t (0.5 prob)
   *   pos_x = 1: t = ones: s  = t: 1 or 0
   *                        s != t: 0
   *              t = 0   : 0 < s < ones: random value > s
   *                        s = 0       : random value > 0
   *              t is a divisor of s: t / s or s with s / x = t (0.5 prob)
   *              else : s with s / x = t
   */

  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();
  bool x_has_fixed_bits    = x.has_fixed_bits();
  BitVector s_mul_t, s_udiv_t;
  bool ic_wo;

  // IC_wo
  if (pos_x == 0)
  {
    // pos_x = 0: (s * t) / s = t
    s_mul_t = s.bvmul(t);
    ic_wo   = s_mul_t.bvudiv(s).compare(t) == 0;
  }
  else
  {
    // pos_x = 1: s / (s / t) = t
    assert(pos_x == 1);
    s_udiv_t = s.bvudiv(t);
    ic_wo    = s.bvudiv(s_udiv_t).compare(t) == 0;
  }

  // IC
  if (ic_wo)
  {
    // fixed: x / s = t
    if (x.is_fixed())
    {
      const BitVector& xval = x.lo();
      if ((pos_x == 0 && xval.bvudiv(s).compare(t) == 0)
          || (pos_x == 1 && s.bvudiv(xval).compare(t) == 0))
      {
        BV_NODE_CACHE_INVERSE_IF(xval);
        return true;
      }
      return false;
    }

    if (pos_x == 0)
    {
      // IC: pos_x = 0: IC_wo &&
      //                (t = 0 => x_lo < s) &&
      //                ((t != 0 && s != 0 ) => \exists y. (
      //                    mcb(x, y) && (~c => y < s * t + 1) &&
      //                    (c => y <= ones)))
      //                with c = umulo(s, t + 1) && uaddo(t, 1)
      if (x_has_fixed_bits)
      {
        if (t.is_zero())
        {
          // IC: (t = 0 => x_lo < s) &&
          if (x.lo().compare(s) >= 0)
          {
            return false;
          }
        }
        else if (!s.is_zero())
        {
          // IC: ((t != 0 && s != 0 ) => \exists y. (
          //         mcb(x, y) && (~c => y < s * t + 1) &&
          //         (c => y <= ones)))
          BitVector& min = s_mul_t;
          BitVector max  = min.bvadd(s);
          if (max.compare(min) < 0)
          {
            max = BitVector::mk_ones(s.size());
          }
          else
          {
            max.ibvdec();
          }

          BitVectorDomainGenerator gen(x, d_rng, min, max);
          if (gen.has_next())
          {
            BV_NODE_CACHE_INVERSE_IF(gen.random());
            return true;
          }
          return false;
        }
      }

      if (!is_essential_check)
      {
        uint64_t size = x.size();
        if (t.is_ones())
        {
          if (s.is_one())
          {
            // Inverse value: pos_x = 0: t = ones: s = 1: ones
            assert(!x_has_fixed_bits);
            BV_NODE_CACHE_INVERSE(BitVector::mk_ones(size));
          }
          else
          {
            // Inverse value: pos_x = 0: s = 0: random value
            assert(s.is_zero());
            if (x_has_fixed_bits)
            {
              BitVectorDomainGenerator gen(x, d_rng);
              assert(gen.has_random());
              BV_NODE_CACHE_INVERSE(gen.random());
            }
            else
            {
              BV_NODE_CACHE_INVERSE(BitVector(size, *d_rng));
            }
          }
        }
        else
        {
          // Inverse value: pos_x = 0: s * t does not overflow: - s * t
          assert(!s.is_umul_overflow(t));
          if (d_rng->flip_coin() && x.match_fixed_bits(s_mul_t))
          {
            BV_NODE_CACHE_INVERSE(std::move(s_mul_t));
          }
          else
          {
            /**
             * determine upper and lower bounds:
             * max = s * (t + 1) - 1
             *       if s * (t + 1) does not overflow, else
             *       ones
             * min = s * t
             */
            BitVector max = t.bvinc();
            if (s.is_umul_overflow(max))
            {
              max = BitVector::mk_ones(size);
            }
            else
            {
              max.ibvmul(s).ibvdec();
            }
            if (x_has_fixed_bits)
            {
              BitVectorDomainGenerator gen(x, d_rng, s_mul_t, max);
              assert(gen.has_random());
              BV_NODE_CACHE_INVERSE(gen.random());
            }
            else
            {
              BV_NODE_CACHE_INVERSE(BitVector(size, *d_rng, s_mul_t, max));
            }
          }
        }
      }
      return true;
    }

    // IC: pos_x = 1: IC_wo &&
    //                (t != ones => hi_x > 0) &&   .(covered by is_fixed check)
    //                ((s != 0 || t != 0) => (s / hi_x <= t) && \exists y. (
    //                    mcb(x, y) &&
    //                    (t = ones => y <= s / t) &&
    //                    (t != ones => y > t + 1 && y <= s / t)))
    if ((x_has_fixed_bits || !is_essential_check)
        && (!s.is_zero() || !t.is_zero()))
    {
      if (x_has_fixed_bits && s.bvudiv(x.hi()).compare(t) > 0)
      {
        return false;
      }

      uint64_t size = s.size();
      BitVector min, max;
      if (t.is_ones())
      {
        min = BitVector::mk_zero(size);
        max = s.is_ones() ? BitVector::mk_one(size) : min;
      }
      else if (s.compare(t) == 0)
      {
        min = BitVector::mk_one(size);
        max = min;
      }
      else
      {
        assert(s.compare(t) >= 0);
        min = t.bvinc();
        min.ibvudiv(s, min).ibvinc();
        max = s_udiv_t;
      }
      if (x_has_fixed_bits)
      {
        BitVectorDomainGenerator gen(x, d_rng, min, max);
        if (gen.has_random())
        {
          BV_NODE_CACHE_INVERSE_IF(gen.random());
          return true;
        }
        return false;
      }
      assert(!is_essential_check);
      BV_NODE_CACHE_INVERSE(BitVector(size, *d_rng, min, max));
    }
    else if (!is_essential_check)
    {
      // Inverse value:
      // pos_x = 1: t = ones: s = t:  1 or 0
      //                      s != t: 0
      //            t = 0   : 0 < s < ones: random value > s
      //            s = 0   : random value > 0
      //            t is a divisor of s: t / s or s with s / x = t (0.5 prob)
      //            else    : s with s / x = t
      uint64_t size = s.size();
      if (t.is_ones())
      {
        BitVector one = BitVector::mk_one(size);
        if (s.compare(t) == 0 && x.match_fixed_bits(one)
            && (!x.match_fixed_bits(BitVector::mk_zero(size))
                || d_rng->flip_coin()))
        {
          BV_NODE_CACHE_INVERSE(std::move(one));
        }
        else
        {
          BV_NODE_CACHE_INVERSE(BitVector::mk_zero(size));
        }
      }
      else
      {
        assert(t.is_zero() && s.is_zero());
        BitVector min = BitVector::mk_one(size);
        BitVector max = BitVector::mk_ones(size);
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x, d_rng, min, max);
          assert(gen.has_random());
          BV_NODE_CACHE_INVERSE(gen.random());
        }
        else
        {
          BV_NODE_CACHE_INVERSE(BitVector(size, *d_rng, min, max));
        }
      }
    }
    return true;
  }

  return ic_wo;
}

bool
BitVectorUdiv::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    pos_x = 0:
   *          (t != ones => x_hi >= t) && (t = 0 => x_lo != ones) &&
   *          ((t != 0 && t != ones && t != 1 && !mcb(x, t)) =>
   *           (!mulo(2, t) && \exists y,o.(mcb(x, y*t + o) && y >= 1 && o <= c
   *            && !mulo(y, t) && !addo(y * t, o))))
   *        with c = min(y − 1, x_hi − y * t)
   *
   *        pos_x = 1:
   *          (t = ones => (mcb(x, 0) || mcb(x, 1))) &&
   *          (t != ones => (!mulo(x_lo, t) &&
   *                     \exists y. (y > 0 && mcb(x, y) && !mulo(y, t))))
   *
   * Consistent value:
   *   pos_x = 0: t = 0   : random value < ones
   *              t = ones: random value
   *              t = one : random value > 0
   *              else    : x = y * t + offset
   *                        with y in [1, ones / t]
   *                        and offset in [0, min(y - 1, ones - y * t)]
   *
   *   pos_x = 1: t = ones: 0 or 1
   *              else    : x * t such that no overflow occurs
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  bool t_is_zero = t.is_zero();
  bool t_is_ones = t.is_ones();
  bool x_has_fixed_bits    = x.has_fixed_bits();
  uint64_t size            = x.size();

  if (pos_x == 0)
  {
    if (t_is_zero)
    {
      if (x_has_fixed_bits)
      {
        if (x.lo().is_ones())
        {
          return false;
        }
        if (x.is_fixed())
        {
          BV_NODE_CACHE_CONSISTENT(x.lo());
        }
        else
        {
          // Consistent value: pos_x = 0: t = 0 : random value < ones
          BitVectorDomainGenerator gen(x,
                                       d_rng,
                                       BitVector::mk_zero(size),
                                       BitVector::mk_ones(size).ibvdec());
          assert(gen.has_random());
          BV_NODE_CACHE_CONSISTENT(gen.random());
        }
      }
      else
      {
        // Consistent value: pos_x = 0: t = 0 : random value < ones
        d_consistent.reset(new BitVector(size,
                                         *d_rng,
                                         BitVector::mk_zero(size),
                                         BitVector::mk_ones(size).ibvdec()));
      }
      return true;
    }

    if (t_is_ones)
    {
      // Consistent value: pos_x = 0: t = ones : random value
      if (x.has_fixed_bits())
      {
        if (x.is_fixed())
        {
          BV_NODE_CACHE_CONSISTENT(x.lo());
        }
        else
        {
          BitVectorDomainGenerator gen(x, d_rng);
          assert(gen.has_random());
          BV_NODE_CACHE_CONSISTENT(gen.random());
        }
      }
      else
      {
        d_consistent.reset(new BitVector(size, *d_rng));
      }
      return true;
    }

    if (x_has_fixed_bits && x.hi().compare(t) < 0)
    {
      return false;
    }

    if (t.is_one())
    {
      // Consistent value: pos_x = 0: t = one : random value > 0
      if (x.has_fixed_bits())
      {
        if (x.is_fixed())
        {
          BV_NODE_CACHE_CONSISTENT(x.lo());
        }
        else
        {
          BitVectorDomainGenerator gen(
              x, d_rng, BitVector::mk_one(size), x.hi());
          assert(gen.has_random());
          BV_NODE_CACHE_CONSISTENT(gen.random());
        }
      }
      else
      {
        d_consistent.reset(new BitVector(
            size, *d_rng, BitVector::mk_one(size), BitVector::mk_ones(size)));
      }
      return true;
    }

    // Consistent value: pos_x = 0: x = y * t + offset
    //                              with y in [1, ones / t]
    //                              and offset in [0, min(y - 1, ones - y * t)]
    if (x_has_fixed_bits)
    {
      BitVector bvres = consistent_value_pos0_aux(t);
      if (bvres.is_null())
      {
        if (!x.match_fixed_bits(t))
        {
          return false;
        }
        d_consistent.reset(new BitVector(t));
      }
      else
      {
        BV_NODE_CACHE_CONSISTENT(std::move(bvres));
      }
      return true;
    }
    BitVector ones = BitVector::mk_ones(size);
    /* Compute x = y * t + offset with y in [1, ones / t] and
     * offset in [0, min(y - 1, ones - y * t)].  */
    BitVector y(size, *d_rng, BitVector::mk_one(size), ones.bvudiv(t));
    assert(!y.is_umul_overflow(t));
    BV_NODE_CACHE_CONSISTENT(y.bvmul(t));

    /* Make sure that adding the offset to (y * t) does not overflow.
     * The maximum value of the offset is the minimum of
     * (y - 1, ones - (y * t)).  */
    BitVector sub = ones.bvsub(*d_consistent);
    /* Compute offset for adding to y * t. */
    BitVector offset(size,
                     *d_rng,
                     BitVector::mk_zero(size),
                     sub.compare(y.ibvdec()) < 0 ? sub : y);
    assert(!d_consistent->is_uadd_overflow(offset));
    d_consistent->ibvadd(offset);
  }
  else
  {
    // fixed
    if (x.hi().is_zero())
    {
      if (t.is_ones())
      {
        BV_NODE_CACHE_CONSISTENT(x.hi());
        return true;
      }
      return false;
    }

    uint64_t size  = t.size();
    BitVector zero = BitVector::mk_zero(size);
    BitVector one  = BitVector::mk_one(size);

    if (t.is_ones())
    {
      // CC: pos_x = 1: (t = ones => (mcb(x, 0) || mcb(x, 1)))
      bool match_one  = !x_has_fixed_bits || x.match_fixed_bits(one);
      bool match_zero = !x_has_fixed_bits || x.match_fixed_bits(zero);
      if (!match_zero && !match_one)
      {
        return false;
      }
      // Consistent value: pos_x = 1: t = ones: 0 or 1
      if (!match_zero || (match_one && d_rng->flip_coin()))
      {
        BV_NODE_CACHE_CONSISTENT(std::move(one));
      }
      else
      {
        assert(match_zero);
        BV_NODE_CACHE_CONSISTENT(std::move(zero));
      }
      return true;
    }

    // CC: (t != ones => (!mulo(x_lo, t) && \exists y. (y > 0 && mcb(x, y) &&
    //                   !mulo(y, t))))
    if (x_has_fixed_bits && x.lo().is_umul_overflow(t))
    {
      return false;
    }

    // Consistent value: pos_x = 1: t != ones: x * t s.t. no overflow occurs
    if (x_has_fixed_bits)
    {
      if (x.is_fixed())
      {
        BV_NODE_CACHE_CONSISTENT(x.lo());
        return true;
      }

      bool res = true;
      BitVectorDomainGenerator gen(x, d_rng, one, x.hi());
      assert(gen.has_random());
      BitVector bvres = gen.random();
      while (bvres.is_umul_overflow(t))
      {
        bvres.ibvdec();
        BitVectorDomainGenerator ggen(x, d_rng, one, bvres);
        if (!ggen.has_random())
        {
          res = false;
          break;
        }
        bvres = ggen.random();
      }
      if (res)
      {
        BV_NODE_CACHE_CONSISTENT(std::move(bvres));
        return true;
      }
      return false;
    }
    BitVector max = BitVector::mk_ones(size);
    BitVector bvres;
    for (;;)
    {
      bvres = BitVector(size, *d_rng, one, max);
      if (!bvres.is_umul_overflow(t)) break;
      max = bvres.ibvdec();
    }
    BV_NODE_CACHE_CONSISTENT(std::move(bvres));
  }
  return true;
}

const BitVector&
BitVectorUdiv::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(pos_x == 1 || t.compare(d_inverse->bvudiv(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvudiv(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorUdiv::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

BitVector
BitVectorUdiv::consistent_value_pos0_aux(const BitVector& t)
{
  /* remaining solutions other than x = t:
   * min <= x <= ones with min = x->lo / t * t if x->lo / t > 1 and
   *                       min = 2 * t otherwise */

  const BitVectorDomain& x = child(0)->domain();
  uint64_t size            = t.size();
  BitVector one            = BitVector::mk_one(size);
  BitVector max, res;

  BitVector min = x.lo().bvudiv(t);
  if (min.compare(one) <= 0)
  {
    if (t.is_uadd_overflow(t))
    {
      /* x = t the only solution */
      return res;
    }
    min = t.bvadd(t);
  }
  else
  {
    min.ibvmul(t);
  }

  /* min / t <= s <= x->hi / t */
  BitVector ones  = BitVector::mk_ones(size);
  BitVector s_min = min.bvudiv(t);
  BitVector s_max = x.hi().bvudiv(t);
  if (s_min.compare(s_max) > 0)
  {
    s_max = ones;
  }
  for (uint32_t i = 0; i < 20; ++i)
  {
    BitVector s_tmp(size, *d_rng, s_min, s_max);
    if (s_tmp.is_umul_overflow(t))
    {
      continue;
    }
    /* for s_tmp, min = s_tmp * t and max = min + s - 1 */
    min = s_tmp.bvmul(t);
    max = s_tmp.bvadd(min);
    if (min.compare(max) > 0)
    {
      max = ones;
    }
    else
    {
      max.ibvdec();
    }
    if (x.is_fixed() && x.lo().compare(min) >= 0 && x.lo().compare(max) <= 0)
    {
      res = x.lo();
      break;
    }
    BitVectorDomainGenerator gen(x, d_rng, min, max);
    if (gen.has_random())
    {
      res = gen.random();
      break;
    }
  }
  return res;
}

/* -------------------------------------------------------------------------- */

BitVectorUlt::BitVectorUlt(RNG* rng,
                           uint64_t size,
                           BitVectorNode* child0,
                           BitVectorNode* child1,
                           bool opt_concat_sext)
    : BitVectorNode(rng, size, child0, child1),
      d_opt_concat_sext(opt_concat_sext)
{
  assert(size == 1);
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorUlt::BitVectorUlt(RNG* rng,
                           const BitVectorDomain& domain,
                           BitVectorNode* child0,
                           BitVectorNode* child1,
                           bool opt_concat_sext)
    : BitVectorNode(rng, domain, child0, child1),
      d_opt_concat_sext(opt_concat_sext)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == 1);
  _evaluate_and_set_domain();
}

void
BitVectorUlt::_evaluate()
{
  d_assignment.ibvult(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorUlt::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorUlt::evaluate()
{
  _evaluate();
}

void
BitVectorUlt::compute_min_max_bounds(const BitVector& s,
                                     const BitVector& t,
                                     uint64_t pos_x,
                                     BitVector& res_min_u,
                                     BitVector& res_max_u,
                                     BitVector& res_min_s,
                                     BitVector& res_max_s)
{
  assert(res_min_u.is_null());
  assert(res_max_u.is_null());
  assert(res_min_s.is_null());
  assert(res_max_s.is_null());

  uint64_t size = s.size();

  // compute unsigned min/max bounds wrt. s and t
  if (pos_x == 0)
  {
    if (t.is_true())
    {
      if (s.is_zero())  // conflict
      {
        return;
      }
      res_min_u = BitVector::mk_zero(size);
      res_max_u = s.bvdec();
    }
    else
    {
      res_min_u = s;
      res_max_u = BitVector::mk_ones(size);
    }
  }
  else
  {
    if (t.is_true())
    {
      if (s.is_ones())  // conflict
      {
        return;
      }
      res_min_u = s.bvinc();
      res_max_u = BitVector::mk_ones(size);
    }
    else
    {
      res_min_u = BitVector::mk_zero(size);
      res_max_u = s;
    }
  }

  // tighten unsigned bounds wrt. to current unsigned bounds of x
  child(pos_x)->tighten_bounds(&res_min_u,
                               &res_max_u,
                               nullptr,
                               nullptr,
                               res_min_u,
                               res_max_u,
                               res_min_s,
                               res_max_s);
}

bool
BitVectorUlt::is_invertible(const BitVector& t,
                            uint64_t pos_x,
                            bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  bool res                 = true;
  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();
  bool is_true             = t.is_true();

  uint64_t n = 0, bw_x = 0, bw_xx = 0;
  bool opt_sext =
      d_opt_concat_sext && child(pos_x)->kind() == NodeKind::BV_SEXT;
  const BitVectorDomain* dx = &x;
  BitVectorDomain dxn, dxx, ddx;

  /**
   * IC_wo: pos_x = 0: t = 0 || s != 0
   *        pos_x = 1: t = 0 || s != ones
   * TODO: +bounds
   *
   * IC:    pos_x = 0: t = 1 => (s != 0 && lo_x < s) && t = 0 => (hi_x >= s)
   *        pos_x = 1: t = 1 => (s != ones && hi_x > s) && t = 0 => (lo_x <= s)
   * TODO: +bounds
   */

  if (opt_sext)
  {
    n = static_cast<BitVectorSignExtend*>(child(pos_x))->get_n();
    if (n > 0)
    {
      bw_x  = x.size();
      bw_xx = bw_x - n;
      dxn   = x.bvextract(bw_x - 1, bw_xx);
      dxx   = x.bvextract(bw_xx - 1, 0);
      if (pos_x == 0 && is_true)
      {
        res = !s.is_zero();
      }
      else if (pos_x == 1 && is_true)
      {
        res = !s.is_ones();
      }

      if (res)
      {
        if (dxx.is_fixed_bit_true(bw_xx - 1)
            || (!dxx.is_fixed_bit(bw_xx - 1) && dxn.has_fixed_bits_true()))
        {
          // check if all fixed bits in dxn are 1
          res = !dxn.has_fixed_bits() || dxn.has_fixed_bits_true_only();
          // check for invertibility wrt s and fixed bits
          if (res)
          {
            dxn.fix(BitVector::mk_ones(dxn.size()));
            ddx = dxn.bvconcat(dxx);
            ddx.fix_bit(bw_xx - 1, true);
            dx = &ddx;
          }
        }
        else if (dxx.is_fixed_bit_false(bw_xx - 1)
                 || (!dxx.is_fixed_bit(bw_xx - 1)
                     && dxn.has_fixed_bits_false()))
        {
          // check if all fixed bits in dxn are 0
          res = !dxn.has_fixed_bits() || dxn.has_fixed_bits_false_only();
          // check for invertibility wrt s and fixed bits
          if (res)
          {
            dxn.fix(BitVector::mk_zero(dxn.size()));
            ddx = dxn.bvconcat(dxx);
            ddx.fix_bit(bw_xx - 1, false);
            dx = &ddx;
          }
        }
        else
        {
          // we have to check for both cases and make sure to randomly choose
          // from either (if possible) if is_essential_check is false
          dxn.fix(BitVector::mk_ones(dxn.size()));
          ddx = dxn.bvconcat(dxx);
          ddx.fix_bit(bw_xx - 1, true);
          dx  = &ddx;
          res = _is_invertible(dx, s, t, pos_x, is_essential_check);
          if (!res || d_rng->flip_coin())
          {
            dxn.fix(BitVector::mk_zero(dxn.size()));
            ddx = dxn.bvconcat(dxx);
            ddx.fix_bit(bw_xx - 1, false);
            dx = &ddx;
            // Note: _is_invertible does not reset d_inverse, thus this second
            //       call is unproblematic, even in the case were the first
            //       check was true, but this second check is false.
            bool _res = _is_invertible(dx, s, t, pos_x, is_essential_check);
            if (!res) res = _res;
          }
          return res;
        }
      }
    }
  }

  if (res)
  {
    res = _is_invertible(dx, s, t, pos_x, is_essential_check);
  }
  return res;
}

bool
BitVectorUlt::_is_invertible(const BitVectorDomain* d,
                             const BitVector& s,
                             const BitVector& t,
                             uint64_t pos_x,
                             bool is_essential_check)
{
  // IC_wo: pos_x = 0: t = 0 || s != 0
  //        pos_x = 1: t = 0 || s != ones
  BitVector min_lo, max_lo, min_hi, max_hi;
  compute_normalized_bounds(s, t, pos_x, min_lo, max_lo, min_hi, max_hi);
  if (min_lo.is_null() && min_hi.is_null())
  {
    return false;
  }

  if (d->is_fixed())
  {
    const BitVector& xval = d->lo();
    if (is_in_bounds(xval, min_lo, max_lo, min_hi, max_hi))
    {
      BV_NODE_CACHE_INVERSE_IF(xval);
      return true;
    }
    return false;
  }
  // IC:pos_x = 0: t = 1 => (s != 0 && lo_x < s) && t = 0 => (hi_x >= s)
  //    pos_x = 1: t = 1 => (s != ones && hi_x > s) && t = 0 => (lo_x <= s)
  if (d->has_fixed_bits())
  {
    BitVectorDomainDualGenerator gen(*d,
                                     d_rng,
                                     min_lo.is_null() ? nullptr : &min_lo,
                                     max_lo.is_null() ? nullptr : &max_lo,
                                     min_hi.is_null() ? nullptr : &min_hi,
                                     max_hi.is_null() ? nullptr : &max_hi);
    if (gen.has_random())
    {
      BV_NODE_CACHE_INVERSE_IF(gen.random());
      return true;
    }
    return false;
  }
  assert(!min_lo.is_null() || !min_hi.is_null());
  if (!is_essential_check)
  {
    if (!min_lo.is_null())
    {
      assert(!max_lo.is_null());
      if (!min_hi.is_null() && d_rng->flip_coin())
      {
        assert(!max_hi.is_null());
        BV_NODE_CACHE_INVERSE(
            BitVector(d->size(), *d_rng, min_hi, max_hi, false));
      }
      else
      {
        BV_NODE_CACHE_INVERSE(
            BitVector(d->size(), *d_rng, min_lo, max_lo, false));
      }
    }
    else
    {
      BV_NODE_CACHE_INVERSE(
          BitVector(d->size(), *d_rng, min_hi, max_hi, false));
    }
  }
  return true;
}

bool
BitVectorUlt::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    pos_x = 0: ~t || x_lo != ones
   *        pos_x = 1: ~t || x_hi != 0
   *
   * Consistent value:
   *   pos_x = 0: t = 1: random value < ones
   *              t = 0: random value
   *   pos_x = 1: t = 1: random_value > 0
   *              t = 0: random value
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t size            = x.size();

  if (pos_x == 0)
  {
    if (t.is_true())
    {
      if (x.has_fixed_bits())
      {
        // CC: pos_x = 0: ~t || x_lo != ones
        if (x.lo().is_ones())
        {
          return false;
        }
        // Consistent value: pos_x = 0: t = 1: random value < ones
        if (x.is_fixed())
        {
          BV_NODE_CACHE_CONSISTENT(x.lo());
        }
        else
        {
          BitVectorDomainGenerator gen(x,
                                       d_rng,
                                       BitVector::mk_zero(size),
                                       BitVector::mk_ones(size).ibvdec());
          assert(gen.has_random());
          BV_NODE_CACHE_CONSISTENT(gen.random());
        }
      }
      else
      {
        // CC_wo: true
        // Consistent value: pos_x = 0: t = 1: random value < ones
        d_consistent.reset(
            new BitVector(BitVector(size,
                                    *d_rng,
                                    BitVector::mk_zero(size),
                                    BitVector::mk_ones(size).ibvdec())));
      }
      return true;
    }
  }
  else
  {
    if (t.is_true())
    {
      if (x.has_fixed_bits())
      {
        // CC: pos_x = 1: ~t || x_hi != 0
        if (x.hi().is_zero())
        {
          return false;
        }
        // Consistent value: pos_x = 1: t = 1: random value > 0
        if (x.is_fixed())
        {
          BV_NODE_CACHE_CONSISTENT(x.lo());
        }
        else
        {
          BitVectorDomainGenerator gen(
              x, d_rng, BitVector::mk_one(size), BitVector::mk_ones(size));
          assert(gen.has_random());
          BV_NODE_CACHE_CONSISTENT(gen.random());
        }
      }
      else
      {
        // CC_wo: true
        // Consistent value: pos_x = 1: t = 1: random value > 0
        d_consistent.reset(new BitVector(BitVector(
            size, *d_rng, BitVector::mk_one(size), BitVector::mk_ones(size))));
      }
      return true;
    }
  }
  // CC: t = false: true
  // Consistent value: t = 0: random value
  assert(t.is_false());
  if (x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      BV_NODE_CACHE_CONSISTENT(x.lo());
    }
    else
    {
      BitVectorDomainGenerator gen(x, d_rng);
      assert(gen.has_random());
      BV_NODE_CACHE_CONSISTENT(gen.random());
    }
  }
  else
  {
    BV_NODE_CACHE_CONSISTENT(BitVector(size, *d_rng));
  }
  return true;
}

const BitVector&
BitVectorUlt::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(pos_x == 1 || t.compare(d_inverse->bvult(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvult(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

BitVector
BitVectorUlt::inverse_value_concat_new_random(const BitVectorDomain& d,
                                              const BitVector& min,
                                              const BitVector& max)
{
  uint64_t size = d.size();
  assert(min.size() == size);
  assert(max.size() == size);

  if (d.has_fixed_bits())
  {
    BitVectorDomainGenerator gen(d, d_rng, min, max);
    if (gen.has_random())
    {
      return gen.random();
    }
  }
  else
  {
    return BitVector(size, *d_rng, min, max);
  }
  return BitVector();
}

BitVector*
BitVectorUlt::inverse_value_concat(bool t, uint64_t pos_x, uint64_t pos_s)
{
  BitVectorNode& op_x = *child(pos_x);
  assert(op_x.kind() == NodeKind::BV_CONCAT);
  BitVectorNode& op_s = *child(pos_s);

  const BitVectorDomain& dx = op_x.domain();

  uint64_t bw_x  = op_x.size();
  uint64_t bw_x0 = op_x.child(0)->size();
  uint64_t bw_x1 = op_x.child(1)->size();
  assert(bw_x - bw_x1 == bw_x0);

  const BitVector x   = op_x.assignment();
  BitVector x0        = x.bvextract(bw_x - 1, bw_x1);
  BitVector x1        = x.bvextract(bw_x1 - 1, 0);
  const BitVector s   = op_s.assignment();
  BitVector s0        = s.bvextract(bw_x - 1, bw_x1);
  BitVector s1        = s.bvextract(bw_x1 - 1, 0);
  BitVectorDomain dx0 = dx.bvextract(bw_x - 1, bw_x1);
  BitVectorDomain dx1 = dx.bvextract(bw_x1 - 1, 0);

  BitVector res_x0, res_x1;
  BitVector* res = nullptr;

  if (pos_x == 0)
  {
    /* x0 o x1 < s0 o s1 ---------------------------------------------- */
    if (t)
    {
      assert(!s.is_zero());

      /* s0 != 0 && x0 >= s0 -> pick x0 < s0 */
      if (!s0.is_zero() && x0.compare(s0) >= 0)
      {
        res_x0 = inverse_value_concat_new_random(
            dx0, BitVector::mk_zero(bw_x0), s0.bvdec());
        if (!res_x0.is_null())
        {
          res_x0.ibvconcat(x1);
          if (res_x0.compare(s) < 0) res = new BitVector(res_x0);
        }
      }

      /* s1 != 0 && x0 == s0 && x1 >= s1 -> pick x1 < s1 */
      if (!s1.is_zero() && x0.compare(s0) == 0 && x1.compare(s1) >= 0)
      {
        res_x1 = inverse_value_concat_new_random(
            dx1, BitVector::mk_zero(bw_x1), s1.bvdec());
        if (!res_x1.is_null())
        {
          res_x1.ibvconcat(x0, res_x1);
          if (res_x1.compare(s) < 0) res = new BitVector(res_x1);
        }
      }
    }
    /* x0 o x1 >= s0 o s1 --------------------------------------------- */
    else
    {
      /* x0 < s0 -> pick x0 >= s0 */
      if (x0.compare(s0) < 0)
      {
        res_x0 =
            inverse_value_concat_new_random(dx0, s0, BitVector::mk_ones(bw_x0));
        if (!res_x0.is_null())
        {
          res_x0.ibvconcat(x1);
          if (res_x0.compare(s) >= 0) res = new BitVector(res_x0);
        }
      }

      /* x0 == s0 && x1 < s1 -> pick x1 >= s1 */
      if (x0.compare(s0) == 0 && x1.compare(s1) < 0)
      {
        res_x1 =
            inverse_value_concat_new_random(dx1, s1, BitVector::mk_ones(bw_x1));
        if (!res_x1.is_null())
        {
          res_x1.ibvconcat(x0, res_x1);
          if (res_x1.compare(s) >= 0) res = new BitVector(res_x1);
        }
      }
    }
  }
  else
  {
    /* s0 o s1 < x0 o x1 */
    if (t)
    {
      assert(!s.is_ones());

      /* x0 <= s0 -> pick x0 > s0 */
      if (!s0.is_ones() && x0.compare(s0) < 0)
      {
        res_x0 = inverse_value_concat_new_random(
            dx0, s0.bvinc(), BitVector::mk_ones(bw_x0));
        if (!res_x0.is_null())
        {
          res_x0.ibvconcat(x1);
          if (s.compare(res_x0) < 0) res = new BitVector(res_x0);
        }
      }

      /* !s1.is_ones() && x0 == s0 && x1 <= s1 -> pick x1 > s1 */
      if (x0.compare(s0) == 0 && !s1.is_ones() && x1.compare(s1) <= 0)
      {
        assert(!s1.is_ones());
        res_x1 = inverse_value_concat_new_random(
            dx1, s1.bvinc(), BitVector::mk_ones(bw_x1));
        if (!res_x1.is_null())
        {
          res_x1.ibvconcat(x0, res_x1);
          if (s.compare(res_x1) < 0) res = new BitVector(res_x1);
        }
      }
    }
    /* s0 o s1 >= x0 o x1 */
    else
    {
      /* s0 < x0 -> pick x0 <= s0 */
      if (s0.compare(x0) < 0)
      {
        res_x0 =
            inverse_value_concat_new_random(dx0, BitVector::mk_zero(bw_x0), s0);
        if (!res_x0.is_null())
        {
          res_x0.ibvconcat(x1);
          if (s.compare(res_x0) >= 0) res = new BitVector(res_x0);
        }
      }

      /* s0 == x0 && s1 < x1 -> pick x1 <= s1 */
      if (x0.compare(s0) == 0 && s1.compare(x1) < 0)
      {
        res_x1 =
            inverse_value_concat_new_random(dx1, BitVector::mk_zero(bw_x1), s1);
        if (!res_x1.is_null())
        {
          res_x1.ibvconcat(x0, res_x1);
          if (s.compare(res_x1) >= 0) res = new BitVector(res_x1);
        }
      }
    }
  }
  return res;
}

const BitVector&
BitVectorUlt::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorSlt::BitVectorSlt(RNG* rng,
                           uint64_t size,
                           BitVectorNode* child0,
                           BitVectorNode* child1,
                           bool opt_concat_sext)
    : BitVectorNode(rng, size, child0, child1),
      d_opt_concat_sext(opt_concat_sext)
{
  assert(size == 1);
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorSlt::BitVectorSlt(RNG* rng,
                           const BitVectorDomain& domain,
                           BitVectorNode* child0,
                           BitVectorNode* child1,
                           bool opt_concat_sext)
    : BitVectorNode(rng, domain, child0, child1),
      d_opt_concat_sext(opt_concat_sext)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == 1);
  _evaluate_and_set_domain();
}

void
BitVectorSlt::_evaluate()
{
  d_assignment.ibvslt(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorSlt::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorSlt::evaluate()
{
  _evaluate();
}

void
BitVectorSlt::compute_min_max_bounds(const BitVector& s,
                                     const BitVector& t,
                                     uint64_t pos_x,
                                     BitVector& res_min_u,
                                     BitVector& res_max_u,
                                     BitVector& res_min_s,
                                     BitVector& res_max_s)
{
  assert(res_min_u.is_null());
  assert(res_max_u.is_null());
  assert(res_min_s.is_null());
  assert(res_max_s.is_null());

  uint64_t size = s.size();

  // compute signed min/max bounds wrt. s and t
  if (pos_x == 0)
  {
    if (t.is_true())
    {
      if (s.is_min_signed())  // conflict
      {
        return;
      }
      res_min_s = BitVector::mk_min_signed(size);
      res_max_s = s.bvdec();
    }
    else
    {
      res_min_s = s;
      res_max_s = BitVector::mk_max_signed(size);
    }
  }
  else
  {
    if (t.is_true())
    {
      if (s.is_max_signed())  // conflict
      {
        return;
      }
      res_min_s = s.bvinc();
      res_max_s = BitVector::mk_max_signed(size);
    }
    else
    {
      res_min_s = BitVector::mk_min_signed(size);
      res_max_s = s;
    }
  }

  // tighten signed bounds wrt. to current signed bounds of x
  child(pos_x)->tighten_bounds(nullptr,
                               nullptr,
                               &res_min_s,
                               &res_max_s,
                               res_min_u,
                               res_max_u,
                               res_min_s,
                               res_max_s);
}

bool
BitVectorSlt::is_invertible(const BitVector& t,
                            uint64_t pos_x,
                            bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  bool res                 = true;
  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();
  bool is_true             = t.is_true();

  uint64_t n = 0, bw_x = 0, bw_xx = 0;
  bool opt_sext =
      d_opt_concat_sext && child(pos_x)->kind() == NodeKind::BV_SEXT;
  const BitVectorDomain* dx = &x;
  BitVectorDomain dxn, dxx, ddx;

  /**
   * IC_wo: pos_x = 0: t = 0 || s != min_signed_value
   *        pos_x = 1: t = 0 || s != max_signed_value
   * TODO: +bounds
   *
   * IC: pos_x = 0: t = 1 => (s != min_signed_value &&
   *                 ((MSB(x) = 0 && lo_x < s) ||
   *                  (MSB(x) != 0 && 1 o lo_x[size-2:0] < s))) &&
   *                t = 0 => ((MSB(x) = 1 && hi_x >= s) ||
   *                          (MSB(x) != 1 && 0 o hi_x[size-2:0] >= s))))
   *     pos_x = 1: t = 1 => (s != max_signed_value &&
   *                          ((MSB(x) = 1 && s < hi_x) ||
   *                           (MSB(x) != 1 && s < 0 o hi_x[size-2:0])))
   *                t = 0 => ((MSB(x) = 0 && s >= lo_x) ||
   *                          (MSB(x) != 0 && s >= 1 o lo_x[size-2:0])))
   * TODO: +bounds
   */

  if (opt_sext)
  {
    assert(child(pos_x)->kind() == NodeKind::BV_SEXT);
    n = static_cast<BitVectorSignExtend*>(child(pos_x))->get_n();
    if (n > 0)
    {
      bw_x  = x.size();
      bw_xx = bw_x - n;
      dxn   = x.bvextract(bw_x - 1, bw_xx);
      dxx   = x.bvextract(bw_xx - 1, 0);
      if (pos_x == 0 && is_true)
      {
        res = !s.is_min_signed();
      }
      else if (pos_x == 1 && is_true)
      {
        res = !s.is_max_signed();
      }

      if (res)
      {
        if (dxx.is_fixed_bit_true(bw_xx - 1)
            || (!dxx.is_fixed_bit(bw_xx - 1) && dxn.has_fixed_bits_true()))
        {
          // check if all fixed bits in dxn are 1
          res = !dxn.has_fixed_bits() || dxn.has_fixed_bits_true_only();
          // check for invertibility wrt s and fixed bits
          if (res)
          {
            dxn.fix(BitVector::mk_ones(dxn.size()));
            ddx = dxn.bvconcat(dxx);
            ddx.fix_bit(bw_xx - 1, true);
            dx = &ddx;
          }
        }
        else if (dxx.is_fixed_bit_false(bw_xx - 1)
                 || (!dxx.is_fixed_bit(bw_xx - 1)
                     && dxn.has_fixed_bits_false()))
        {
          // check if all fixed bits in dxn are 0
          res = !dxn.has_fixed_bits() || dxn.has_fixed_bits_false_only();
          // check for invertibility wrt s and fixed bits
          if (res)
          {
            dxn.fix(BitVector::mk_zero(dxn.size()));
            ddx = dxn.bvconcat(dxx);
            ddx.fix_bit(bw_xx - 1, false);
            dx = &ddx;
          }
        }
        else
        {
          // we have to check for both cases and make sure to randomly choose
          // from either (if possible) if is_essential_check is false
          dxn.fix(BitVector::mk_ones(dxn.size()));
          ddx = dxn.bvconcat(dxx);
          ddx.fix_bit(bw_xx - 1, true);
          dx  = &ddx;
          res = _is_invertible(dx, s, t, pos_x, is_essential_check);
          if (!res || d_rng->flip_coin())
          {
            dxn.fix(BitVector::mk_zero(dxn.size()));
            ddx = dxn.bvconcat(dxx);
            ddx.fix_bit(bw_xx - 1, false);
            dx = &ddx;
            // Note: _is_invertible does not reset d_inverse, thus this second
            //       call is unproblematic, even in the case were the first
            //       check was true, but this second check is false.
            bool _res = _is_invertible(dx, s, t, pos_x, is_essential_check);
            return !res ? _res : res;
          }
        }
      }
    }
  }

  if (res)
  {
    res = _is_invertible(dx, s, t, pos_x, is_essential_check);
  }
  return res;
}

bool
BitVectorSlt::_is_invertible(const BitVectorDomain* d,
                             const BitVector& s,
                             const BitVector& t,
                             uint64_t pos_x,
                             bool is_essential_check)
{
  // IC_wo: pos_x = 0: t = 0 || s != min_signed_value
  //        pos_x = 1: t = 0 || s != max_signed_value
  BitVector min_lo, max_lo, min_hi, max_hi;
  compute_normalized_bounds(s, t, pos_x, min_lo, max_lo, min_hi, max_hi);

  if (min_lo.is_null() && min_hi.is_null())
  {
    return false;
  }

  // IC: pos_x = 0: IC_wo &&
  //                t = 1 => (s != min_signed_value &&
  //                 ((MSB(x) = 0 && lo_x < s) ||
  //                  (MSB(x) != 0 && 1 o lo_x[size-2:0] < s))) &&
  //                t = 0 => ((MSB(x) = 1 && hi_x >= s) ||
  //                          (MSB(x) != 1 && 0 o hi_x[size-2:0] >= s))))
  //     pos_x = 1: IC_wo &&
  //                t = 1 => (s != max_signed_value &&
  //                          ((MSB(x) = 1 && s < hi_x) ||
  //                           (MSB(x) != 1 && s < 0 o hi_x[size-2:0])))
  //                t = 0 => ((MSB(x) = 0 && s >= lo_x) ||
  //                          (MSB(x) != 0 && s >= 1 o lo_x[size-2:0])))
  // TODO: +bounds
  if (d->is_fixed())
  {
    const BitVector& xval = d->lo();
    if (is_in_bounds(xval, min_lo, max_lo, min_hi, max_hi))
    {
      BV_NODE_CACHE_INVERSE_IF(d->lo());
      return true;
    }
    return false;
  }
  if (d->has_fixed_bits())
  {
    BitVectorDomainDualGenerator gen(*d,
                                     d_rng,
                                     min_lo.is_null() ? nullptr : &min_lo,
                                     max_lo.is_null() ? nullptr : &max_lo,
                                     min_hi.is_null() ? nullptr : &min_hi,
                                     max_hi.is_null() ? nullptr : &max_hi);

    if (gen.has_random())
    {
      BV_NODE_CACHE_INVERSE_IF(gen.random());
      return true;
    }
    return false;
  }
  assert(!min_lo.is_null() || !min_hi.is_null());
  if (!is_essential_check)
  {
    if (!min_lo.is_null())
    {
      assert(!max_lo.is_null());
      if (!min_hi.is_null() && d_rng->flip_coin())
      {
        assert(!max_hi.is_null());
        BV_NODE_CACHE_INVERSE(
            BitVector(d->size(), *d_rng, min_hi, max_hi, true));
      }
      else
      {
        BV_NODE_CACHE_INVERSE(
            BitVector(d->size(), *d_rng, min_lo, max_lo, true));
      }
    }
    else
    {
      BV_NODE_CACHE_INVERSE(BitVector(d->size(), *d_rng, min_hi, max_hi, true));
    }
  }
  return true;
}

BitVector
BitVectorSlt::inverse_value_concat_new_random(const BitVectorDomain& d,
                                              const BitVector& min,
                                              const BitVector& max)
{
  uint64_t size = d.size();
  assert(min.size() == size);
  assert(max.size() == size);

  if (d.has_fixed_bits())
  {
    BitVectorDomainSignedGenerator gen(d, d_rng, min, max);
    if (gen.has_random())
    {
      return gen.random();
    }
  }
  else
  {
    return BitVector(size, *d_rng, min, max, true);
  }
  return BitVector();
}

BitVector*
BitVectorSlt::inverse_value_concat(bool t, uint64_t pos_x, uint64_t pos_s)
{
  BitVectorNode& op_x = *child(pos_x);
  assert(op_x.kind() == NodeKind::BV_CONCAT);
  BitVectorNode& op_s = *child(pos_s);

  const BitVectorDomain& dx = op_x.domain();

  uint64_t bw_x  = op_x.size();
  uint64_t bw_x0 = op_x.child(0)->size();
  uint64_t bw_x1 = op_x.child(1)->size();
  assert(bw_x - bw_x1 == bw_x0);

  const BitVector x   = op_x.assignment();
  BitVector x0        = x.bvextract(bw_x - 1, bw_x1);
  BitVector x1        = x.bvextract(bw_x1 - 1, 0);
  const BitVector s   = op_s.assignment();
  BitVector s0        = s.bvextract(bw_x - 1, bw_x1);
  BitVector s1        = s.bvextract(bw_x1 - 1, 0);
  BitVectorDomain dx0 = dx.bvextract(bw_x - 1, bw_x1);
  BitVectorDomain dx1 = dx.bvextract(bw_x1 - 1, 0);

  BitVector res_x0, res_x1;
  BitVector* res = nullptr;

  if (pos_x == 0)
  {
    /* x0 o x1 < s0 o s1 ---------------------------------------------- */
    if (t)
    {
      assert(!s.is_min_signed());

      /* s0 != 0 && x0 >=s s0 -> pick x0 <s s0 */
      if (!s0.is_min_signed() && x0.signed_compare(s0) >= 0)
      {
        res_x0 = inverse_value_concat_new_random(
            dx0, BitVector::mk_min_signed(bw_x0), s0.bvdec());
        if (!res_x0.is_null())
        {
          res_x0.ibvconcat(x1);
          if (res_x0.signed_compare(s) < 0) res = new BitVector(res_x0);
        }
      }

      /* s1 != 0 && x0 == s0 && x1 >=s s1 -> pick x1 <s s1 */
      if (!s1.is_min_signed() && x0.signed_compare(s0) == 0
          && x1.signed_compare(s1) >= 0)
      {
        res_x1 = inverse_value_concat_new_random(
            dx1, BitVector::mk_min_signed(bw_x1), s1.bvdec());
        if (!res_x1.is_null())
        {
          res_x1.ibvconcat(x0, res_x1);
          if (res_x1.signed_compare(s) < 0) res = new BitVector(res_x1);
        }
      }
    }
    /* x0 o x1 >=s s0 o s1 --------------------------------------------- */
    else
    {
      /* x0 <s s0 -> pick x0 >=s s0 */
      if (x0.signed_compare(s0) < 0)
      {
        res_x0 = inverse_value_concat_new_random(
            dx0, s0, BitVector::mk_max_signed(bw_x0));
        if (!res_x0.is_null())
        {
          res_x0.ibvconcat(x1);
          if (res_x0.signed_compare(s) >= 0) res = new BitVector(res_x0);
        }
      }

      /* x0 == s0 && x1 <s s1 -> pick x1 >=s s1 */
      if (x0.signed_compare(s0) == 0 && x1.signed_compare(s1) < 0)
      {
        res_x1 = inverse_value_concat_new_random(
            dx1, s1, BitVector::mk_max_signed(bw_x1));
        if (!res_x1.is_null())
        {
          res_x1.ibvconcat(x0, res_x1);
          if (res_x1.signed_compare(s) >= 0) res = new BitVector(res_x1);
        }
      }
    }
  }
  else
  {
    /* s0 o s1 <s x0 o x1 */
    if (t)
    {
      assert(!s.is_max_signed());

      /* x0 <=s s0 -> pick x0 >s s0 */
      if (!s0.is_max_signed() && x0.signed_compare(s0) < 0)
      {
        res_x0 = inverse_value_concat_new_random(
            dx0, s0.bvinc(), BitVector::mk_max_signed(bw_x0));
        if (!res_x0.is_null())
        {
          res_x0.ibvconcat(x1);
          if (s.signed_compare(res_x0) < 0) res = new BitVector(res_x0);
        }
      }

      /* !s1.is_max_signed() && x0 == s0 && x1 <=s s1 -> pick x1 >s s1 */
      if (x0.signed_compare(s0) == 0 && !s1.is_max_signed()
          && x1.signed_compare(s1) <= 0)
      {
        assert(!s1.is_max_signed());
        res_x1 = inverse_value_concat_new_random(
            dx1, s1.bvinc(), BitVector::mk_max_signed(bw_x1));
        if (!res_x1.is_null())
        {
          res_x1.ibvconcat(x0, res_x1);
          if (s.signed_compare(res_x1) < 0) res = new BitVector(res_x1);
        }
      }
    }
    /* s0 o s1 >=s x0 o x1 */
    else
    {
      /* s0 < x0 -> pick x0 <=s s0 */
      if (s0.signed_compare(x0) < 0)
      {
        res_x0 = inverse_value_concat_new_random(
            dx0, BitVector::mk_min_signed(bw_x0), s0);
        if (!res_x0.is_null())
        {
          res_x0.ibvconcat(x1);
          if (s.signed_compare(res_x0) >= 0) res = new BitVector(res_x0);
        }
      }

      /* s0 == x0 && s1 <s x1 -> pick x1 <=s s1 */
      if (x0.signed_compare(s0) == 0 && s1.signed_compare(x1) < 0)
      {
        res_x1 = inverse_value_concat_new_random(
            dx1, BitVector::mk_min_signed(bw_x1), s1);
        if (!res_x1.is_null())
        {
          res_x1.ibvconcat(x0, res_x1);
          if (s.signed_compare(res_x1) >= 0) res = new BitVector(res_x1);
        }
      }
    }
  }
  return res;
}

bool
BitVectorSlt::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    pos_x = 0: t = false || (const(x) => x_lo != smax)
   *        pos_x = 1: t = false || (const(x) => x_hi != smin)
   *
   * Consistent value:
   *   pos_x = 0: t = 1: random value <s max_signed
   *              t = 0: random value
   *   pos_x = 1: t = 1: random_value >s min_signed
   *              t = 0: random value
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t size            = x.size();

  if (pos_x == 0)
  {
    if (t.is_true())
    {
      if (x.has_fixed_bits())
      {
        // CC: pos_x = 0: t = false || (const(x) => x_lo != smax)
        if (x.is_fixed())
        {
          if (x.lo().is_max_signed())
          {
            return false;
          }
          // Consistent value: pos_x = 0: t = 1: random value <s max_signed
          BV_NODE_CACHE_CONSISTENT(x.lo());
        }
        else
        {
          // CC_wo: true
          // Consistent value: pos_x = 0: t = 1: random value <s max_signed
          BitVectorDomainSignedGenerator gen(
              x,
              d_rng,
              BitVector::mk_min_signed(size),
              BitVector::mk_max_signed(size).ibvdec());
          assert(gen.has_random());
          BV_NODE_CACHE_CONSISTENT(gen.random());
        }
      }
      else
      {
        // CC_wo: true
        // Consistent value: pos_x = 0: t = 1: random value <s max_signed
        d_consistent.reset(
            new BitVector(BitVector(size,
                                    *d_rng,
                                    BitVector::mk_min_signed(size),
                                    BitVector::mk_max_signed(size).ibvdec(),
                                    true)));
      }
      return true;
    }
  }
  else
  {
    if (t.is_true())
    {
      if (x.has_fixed_bits())
      {
        // CC: pos_x = 1: t = false || (const(x) => x_hi != smin)
        if (x.is_fixed())
        {
          if (x.hi().is_min_signed())
          {
            return false;
          }
          // Consistent value: pos_x = 1: t = 1: random value >s min_signed
          BV_NODE_CACHE_CONSISTENT(x.lo());
        }
        else
        {
          // CC_wo: true
          // Consistent value: pos_x = 1: t = 1: random value >s min_signed
          BitVectorDomainSignedGenerator gen(
              x,
              d_rng,
              BitVector::mk_min_signed(size).ibvinc(),
              BitVector::mk_max_signed(size));
          assert(gen.has_random());
          BV_NODE_CACHE_CONSISTENT(gen.random());
        }
      }
      else
      {
        // CC_wo: true
        // Consistent value: pos_x = 1: t = 1: random value <s max_signed
        d_consistent.reset(
            new BitVector(BitVector(size,
                                    *d_rng,
                                    BitVector::mk_min_signed(size).ibvinc(),
                                    BitVector::mk_max_signed(size),
                                    true)));
      }
      return true;
    }
  }
  // CC: t = false: true
  // Consistent value: t = 0: random value
  assert(t.is_false());
  if (x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      BV_NODE_CACHE_CONSISTENT(x.lo());
    }
    else
    {
      BitVectorDomainGenerator gen(x, d_rng);
      assert(gen.has_random());
      BV_NODE_CACHE_CONSISTENT(gen.random());
    }
  }
  else
  {
    BV_NODE_CACHE_CONSISTENT(BitVector(size, *d_rng));
  }
  return true;
}

const BitVector&
BitVectorSlt::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(pos_x == 1 || t.compare(d_inverse->bvslt(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvslt(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorSlt::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  assert(d_consistent);
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorUrem::BitVectorUrem(RNG* rng,
                             uint64_t size,
                             BitVectorNode* child0,
                             BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == child0->size());
  assert(child0->size() == child1->size());
  d_inverse_domain.reset(nullptr);
  _evaluate_and_set_domain();
}

BitVectorUrem::BitVectorUrem(RNG* rng,
                             const BitVectorDomain& domain,
                             BitVectorNode* child0,
                             BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == child0->size());
  d_inverse_domain.reset(nullptr);
  _evaluate_and_set_domain();
}

void
BitVectorUrem::_evaluate()
{
  d_assignment.ibvurem(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorUrem::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorUrem::evaluate()
{
  _evaluate();
}

bool
BitVectorUrem::is_invertible(const BitVector& t,
                             uint64_t pos_x,
                             bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: pos_x = 0: ~(-s) >= t
   *        pos_x = 1: (t + t - s) & s >= t
   * IC:    pos_x = 0: IC_wo &&
   *                   ((s = 0 || t = ones) => mcb(x, t)) &&
   *                   ((s != 0 && t != ones) => \exists y. (
   *                       mcb(x, s * y + t) &&
   *                       !umulo(s, y) && !uaddo(s *y, t)))
   *        pos_x = 1: IC_wo &&
   *                   (s = t => (x_lo = 0 || hi_x > t)) &&
   *                   (s != t => \exists y. (
   *                       mcb(x, y) && y > t && (s - t) mod y = 0)
   */

  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();
  bool x_has_fixed_bits    = x.has_fixed_bits();
  bool ic;

  // IC_wo
  if (pos_x == 0)
  {
    // pos_x = 0: ~(-s) >= t
    ic = s.bvneg().ibvnot().compare(t) >= 0;
  }
  else
  {
    // (t + t - s) & s >= t
    assert(pos_x == 1);
    ic = t.bvadd(t).ibvsub(s).ibvand(s).compare(t) >= 0;
  }

  // IC
  if (ic)
  {
    // fixed: x % s = t
    if (x_has_fixed_bits && x.is_fixed())
    {
      if ((pos_x == 0 && x.lo().bvurem(s).compare(t) == 0)
          || (pos_x == 1 && s.bvurem(x.lo()).compare(t) == 0))
      {
        BV_NODE_CACHE_INVERSE_IF(x.lo());
        return true;
      }
      return false;
    }

    if (pos_x == 0 && (x_has_fixed_bits || !is_essential_check))
    {
      if (s.is_zero() || t.is_ones())
      {
        // IC: pos_x = 0: IC_wo && ((s = 0 || t = ones) => mcb(x, t))
        if (!x_has_fixed_bits || x.match_fixed_bits(t))
        {
          BV_NODE_CACHE_INVERSE_IF(t);
          return true;
        }
        return false;
      }
      // IC: pos_x = 0: IC_wo &&
      //                ((s != 0 && t != ones) => \exists y. (
      //                    mcb(x, s * y + t) &&
      //                    !umulo(s, y) && !uaddo(s *y, t)))
      assert(s.compare(t) > 0);
      // if simplest solution (0 <= res < s: res = t) does not apply,
      // x = s * n + t with n s.t. (s * n + t) does not overflow
      uint64_t size  = x.size();
      BitVector ones = BitVector::mk_ones(size);
      if (ones.bvsub(s).compare(t) < 0)
      {
        // overflow for n = 1 -> only simplest solution possible
        if (!x_has_fixed_bits || x.match_fixed_bits(t))
        {
          // overflow for n = 1 -> only simplest solution (t) possible
          BV_NODE_CACHE_INVERSE_IF(t);
          return true;
        }
        else
        {
          // simplest possible solution not applicable
          return false;
        }
      }

      // x = s * n + t, with n s.t. (s * n + t) does not overflow
      // -> n <= (~0 - t) / s (truncated)
      // -> ~0 - s * n >= t

      // s > t -> n_hi = ~0 / t (subtracting t is redundant)
      BitVector n_hi = ones.bvudiv(s);
      assert(!n_hi.is_zero());
      // ~0 - s * n_hi < t ? decrease n_hi until >= t
      BitVector mul = s.bvmul(n_hi);
      BitVector sub = ones.bvsub(mul);
      while (sub.compare(t) < 0)
      {
        n_hi.ibvdec();
        mul.ibvmul(s, n_hi);
        sub.ibvsub(ones, mul);
      }
      // hi = s * n_hi + t (upper bound for x)
      BitVector hi = mul.bvadd(t);
      // x->lo <= x <= hi
      BitVectorDomainGenerator gen(x, d_rng, x.lo(), hi);
      bool res = false;
      if (gen.has_random())
      {
        for (uint32_t cnt = 0; cnt < 10000; ++cnt)
        {
          BitVector bv  = gen.random();
          BitVector rem = bv.bvurem(s);
          if (rem.compare(t) == 0)
          {
            res = true;
            BV_NODE_CACHE_INVERSE(std::move(bv));
            break;
          }
        }
      }
      return res;
    }

    if (pos_x == 1 && (x_has_fixed_bits || !is_essential_check))
    {
      // IC: pos_x = 1: t = ones: mcb(x, 0)
      uint64_t size = x.size();
      if (t.is_ones())
      {
        BitVector zero = BitVector::mk_zero(size);
        if (x_has_fixed_bits && !x.match_fixed_bits(zero))
        {
          return false;
        }
        BV_NODE_CACHE_INVERSE_IF(std::move(zero));
        return true;
      }

      // IC: pos_x = 1: IC_wo && (s = t => (lo_x = 0 || hi_x > t))
      if (s.compare(t) == 0)
      {
        // s = t: x = 0 or random x > t
        if (!x_has_fixed_bits || x.lo().is_zero() || x.hi().compare(t) > 0)
        {
          if (!is_essential_check)
          {
            BitVector zero = BitVector::mk_zero(size);
            if (d_rng->pick_with_prob(250)
                && (!x_has_fixed_bits || x.match_fixed_bits(zero)))
            {
              BV_NODE_CACHE_INVERSE(std::move(zero));
            }
            else if (x_has_fixed_bits)
            {
              if (x.is_fixed())
              {
                BV_NODE_CACHE_INVERSE(x.lo());
              }
              else
              {
                BitVectorDomainGenerator gen(
                    x, d_rng, t.bvinc(), BitVector::mk_ones(size));
                if (!gen.has_random())
                {
                  assert(x.match_fixed_bits(zero));
                  BV_NODE_CACHE_INVERSE(std::move(zero));
                }
                else
                {
                  BV_NODE_CACHE_INVERSE(gen.random());
                }
              }
            }
            else
            {
              BV_NODE_CACHE_INVERSE(
                  BitVector(size, *d_rng, t.bvinc(), BitVector::mk_ones(size)));
            }
          }
          return true;
        }
        return false;
      }

      // IC: pos_x = 1: IC_wo && (s != t => \exists y. (
      //                            mcb(x, y) && y > t && (s - t) mod y = 0)

      /* s = x * n + t
       *
       * In general, x = s - t is always a solution with n = 1, but
       * fixed bits of x may not match s - t. In this case, we look for a
       * factor n s.t. x = (s - t) / n, where fixed bits match. */
      assert(t.compare(s) <= 0);
      BitVector n = s.bvsub(t);
      /* Is (s - t) a solution?
       *
       * -> if yes we do not immediately cache the result to enforce that
       *    we select one of several possible inverse values rather than only
       *    this solution
       */
      if (x_has_fixed_bits && !x.match_fixed_bits(n))
      {
        // if (t.is_zero() && x.match_fixed_bits(BitVector::mk_one(size)))
        if (!t.is_zero() || !x.match_fixed_bits(BitVector::mk_one(size)))
        {
          // s - t does not match const bits of x and one is not a possible
          // solution. Find factor n of (s - t) s.t. n > t and n matches the
          // const bits of x. Pick x = n.
          BitVector bv = x.get_factor(d_rng, n, t, 10000);
          assert(bv.is_null() || x.match_fixed_bits(bv));
          if (bv.is_null())
          {
            return false;
          }
          assert(s.bvurem(bv).compare(t) == 0);
          BV_NODE_CACHE_INVERSE_IF(std::move(bv));
          return true;
        }
      }
      if (!is_essential_check)
      {
        assert(s.compare(t) > 0);
        assert(t.is_zero() || t.compare(s.bvdec()) != 0);

        BitVector sub = s.bvsub(t);
        assert(sub.compare(t) > 0);
        bool x_match_sub = !x_has_fixed_bits || x.match_fixed_bits(sub);

        if (d_rng->flip_coin() && x_match_sub)
        {
          BV_NODE_CACHE_INVERSE(std::move(sub));
        }
        else
        {
          BitVector one = BitVector::mk_one(size);
          bool x_match_one =
              t.is_zero() && (!x_has_fixed_bits || x.match_fixed_bits(one));

          if (d_rng->pick_with_prob(100) && x_match_one)
          {
            BV_NODE_CACHE_INVERSE(std::move(one));
          }
          else
          {
            BitVector bv = x.get_factor(d_rng, sub, t, 10000);
            assert(bv.is_null() || x.match_fixed_bits(bv));
            if (!bv.is_null())
            {
              BV_NODE_CACHE_INVERSE(std::move(bv));
            }
            else
            {
              assert(x_match_one || x_match_sub);
              if (x_match_one && x_match_sub)
              {
                if (d_rng->flip_coin())
                {
                  BV_NODE_CACHE_INVERSE(std::move(sub));
                }
                else
                {
                  BV_NODE_CACHE_INVERSE(std::move(one));
                }
              }
              else if (x_match_one)
              {
                BV_NODE_CACHE_INVERSE(std::move(one));
              }
              else
              {
                BV_NODE_CACHE_INVERSE(std::move(sub));
              }
            }
          }
        }
      }
      return true;
    }
  }

  return ic;
}

bool
BitVectorUrem::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = child(pos_x)->domain();
  bool t_is_ones           = t.is_ones();
  bool x_has_fixed_bits    = x.has_fixed_bits();
  uint64_t size            = t.size();

  if (x_has_fixed_bits)
  {
    /* CC: pos_x = 0: (t = ones => mcb(x, ones)) &&
     *                (t != ones =>
     *                  (t > (ones - t) => mcb (x, t)) &&
     *                  (t < (ones - t) => mcb(x, t) ||
     *                   \exists y. (mcb(x, y) && y> 2*t))
     *
     *     pos_x = 1: mcb(x, 0) ||
     *                ((t = ones => mcb(x, 0)) &&
     *                 (t != ones => \exists y. (mcb(x, y) && y > t)))
     *
     * Consistent value:
     *   pos_x = 0: t = ones: ones
     *              else    : t or
     *                        x = s + t with x > t such that no overflows occur
     *   pos_x = 1: t = ones: 0
     *              else    : 0 or random value > t
     */

    if (pos_x == 0)
    {
      bool mcb = x.match_fixed_bits(t);

      // CC: pos_x = 0: (t = ones => mcb(x, ones))
      if (t_is_ones)
      {
        if (!mcb)
        {
          return false;
        }
        BV_NODE_CACHE_CONSISTENT(BitVector::mk_ones(size));
        return true;
      }

      // mcb(x, t): pick t with probability 0.1
      if (mcb && d_rng->pick_with_prob(100))
      {
        d_consistent.reset(new BitVector(t));
        return true;
      }

      // CC: pos_x = 0: (t != ones =>
      //                   (t > (ones - t) => mcb (x, t)) &&
      //                   (t < (ones - t) => mcb(x, t) ||
      //                    \exists y. (mcb(x, y) && y> 2*t))
      int32_t cmp_t = t.compare(BitVector::mk_ones(size).ibvsub(t));

      if (cmp_t > 0 && !mcb)
      {
        return false;
      }

      if (cmp_t < 0)
      {
        // x > t: pick s > t such that x = s + t does not overflow
        //        -> t < s < ones - t
        //        -> 2*t + 1 <= x <= ones
        BitVector bvres = consistent_value_pos0_aux(t);
        if (!bvres.is_null())
        {
          d_consistent.reset(new BitVector(bvres));
          return true;
        }
        else if (!mcb)
        {
          return false;
        }
      }

      assert(mcb);
      d_consistent.reset(new BitVector(t));
      return true;
    }
    else
    {
      BitVector zero = BitVector::mk_zero(size);
      bool mcb       = x.match_fixed_bits(zero);

      // CC: pos_x = 1: t = ones => mcb(x, 0)
      if (t_is_ones)
      {
        if (!mcb)
        {
          return false;
        }
        d_consistent.reset(new BitVector(zero));
        return true;
      }

      // mcb(x, 0): pick 0 with probability 0.1
      if (mcb && d_rng->pick_with_prob(100))
      {
        d_consistent.reset(new BitVector(zero));
        return true;
      }

      // CC: pos_x = 1: !mcb(x, 0) &&
      //                (t != ones => \exists y. (mcb(x, y) && y > t))
      BitVector min = t.bvinc();
      if (x.is_fixed() && x.lo().compare(min) >= 0)
      {
        BV_NODE_CACHE_CONSISTENT(x.lo());
        return true;
      }
      BitVectorDomainGenerator gen(x, d_rng, min, x.hi());
      if (gen.has_random())
      {
        BV_NODE_CACHE_CONSISTENT(gen.random());
        return true;
      }
      else if (!mcb)
      {
        return false;
      }

      assert(mcb);
      d_consistent.reset(new BitVector(zero));
      return true;
    }
  }

  // CC_wo: true
  assert(!x_has_fixed_bits);
  if (pos_x == 0)
  {
    if (t_is_ones)
    {
      // Consistent value: pos_x = 0: t = ones: ones
      BV_NODE_CACHE_CONSISTENT(BitVector::mk_ones(size));
    }
    else if (d_rng->pick_with_prob(100))
    {
      // Consistent value: pos_x = 0: t != ones: t
      d_consistent.reset(new BitVector(t));
    }
    else
    {
      // Consistent value: pos_x = 0: t != ones: x = s * t with x > t
      //                                         s.t. no overflow occurs
      BitVector max = BitVector::mk_ones(size).ibvsub(t);
      BitVector min = t.bvinc();
      if (min.compare(max) > 0)
      {
        d_consistent.reset(new BitVector(t));
      }
      else
      {
        d_consistent.reset(
            new BitVector(BitVector(size, *d_rng, min, max).ibvadd(t)));
      }
    }
  }
  else
  {
    if (t_is_ones || d_rng->pick_with_prob(100))
    {
      // Consistent value: pos_x = 1: t = ones: 0
      BV_NODE_CACHE_CONSISTENT(BitVector::mk_zero(size));
    }
    else
    {
      // Consistent value: pos_x = 1: t != ones: 0 or random value > t
      d_consistent.reset(
          new BitVector(size, *d_rng, t.bvinc(), BitVector::mk_ones(size)));
    }
  }

  return true;
}

const BitVector&
BitVectorUrem::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(pos_x == 1 || t.compare(d_inverse->bvurem(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvurem(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorUrem::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

BitVector
BitVectorUrem::consistent_value_pos0_aux(const BitVector& t)
{
  /* x > t:
   * pick s > t such that x = s + t does not overflow -> t < s < ones - t
   * -> 2*t + 1 <= x <= ones */
  const BitVectorDomain& x = child(0)->domain();
  BitVector min            = t.bvinc();
  if (!min.is_uadd_overflow(t))
  {
    min.ibvadd(t);
    if (x.is_fixed() && x.lo().compare(min) >= 0)
    {
      return x.lo();
    }
    BitVectorDomainGenerator gen(x, d_rng, min, x.hi());
    if (gen.has_random())
    {
      return gen.random();
    }
  }
  return BitVector();
}

/* -------------------------------------------------------------------------- */

BitVectorXor::BitVectorXor(RNG* rng,
                           uint64_t size,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, size, child0, child1)
{
  assert(size == child0->size());
  assert(child0->size() == child1->size());
  _evaluate_and_set_domain();
}

BitVectorXor::BitVectorXor(RNG* rng,
                           const BitVectorDomain& domain,
                           BitVectorNode* child0,
                           BitVectorNode* child1)
    : BitVectorNode(rng, domain, child0, child1)
{
  assert(child0->size() == child1->size());
  assert(domain.size() == child0->size());
  _evaluate_and_set_domain();
}

void
BitVectorXor::_evaluate()
{
  d_assignment.ibvxor(child(0)->assignment(), child(1)->assignment());
}

void
BitVectorXor::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorXor::evaluate()
{
  _evaluate();
}

bool
BitVectorXor::is_invertible(const BitVector& t,
                            uint64_t pos_x,
                            bool is_essential_check)
{
  (void) is_essential_check;

  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: true
   * IC: mcb(x, s^t)
   *
   * Inverse value: s ^ t
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s           = 1 - pos_x;
  const BitVector& s       = child(pos_s)->assignment();
  if (x.has_fixed_bits())
  {
    if (!x.match_fixed_bits(s.bvxor(t)))
    {
      return false;
    }
  }
  BV_NODE_CACHE_INVERSE_IF(s.bvxor(t));
  return true;
}

bool
BitVectorXor::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    true
   *
   * Consistent value: random value
   */

  (void) t;
  const BitVectorDomain& x = child(pos_x)->domain();
  if (x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      BV_NODE_CACHE_CONSISTENT(x.lo());
    }
    else
    {
      BitVectorDomainGenerator gen(x, d_rng);
      assert(gen.has_random());
      BV_NODE_CACHE_CONSISTENT(gen.random());
    }
  }
  else
  {
    d_consistent.reset(new BitVector(x.size(), *d_rng));
  }
  return true;
}

const BitVector&
BitVectorXor::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s     = 1 - pos_x;
  const BitVector& s = child(pos_s)->assignment();
  assert(d_inverse);
  assert(pos_x == 1 || t.compare(d_inverse->bvxor(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvxor(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorXor::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

/* -------------------------------------------------------------------------- */

BitVectorIte::BitVectorIte(RNG* rng,
                           uint64_t size,
                           BitVectorNode* child0,
                           BitVectorNode* child1,
                           BitVectorNode* child2)
    : BitVectorNode(rng, size, child0, child1, child2)
{
  assert(size == child1->size());
  assert(child0->size() == 1);
  assert(child1->size() == child2->size());
  _evaluate_and_set_domain();
}

BitVectorIte::BitVectorIte(RNG* rng,
                           const BitVectorDomain& domain,
                           BitVectorNode* child0,
                           BitVectorNode* child1,
                           BitVectorNode* child2)
    : BitVectorNode(rng, domain, child0, child1, child2)
{
  assert(child0->size() == 1);
  assert(child1->size() == child2->size());
  assert(domain.size() == child1->size());
  _evaluate_and_set_domain();
}

void
BitVectorIte::_evaluate()
{
  d_assignment.ibvite(
      child(0)->assignment(), child(1)->assignment(), child(2)->assignment());
}

void
BitVectorIte::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorIte::evaluate()
{
  _evaluate();
}

bool
BitVectorIte::is_essential(const BitVector& t, uint64_t pos_x)
{
  uint64_t pos_s0 = pos_x == 0 ? 1 : 0;
  uint64_t pos_s1 = pos_x == 2 ? 1 : 2;
  return !is_invertible(t, pos_s0, true) && !is_invertible(t, pos_s1, true);
}

bool
BitVectorIte::is_invertible(const BitVector& t,
                            uint64_t pos_x,
                            bool is_essential_check)
{
  (void) is_essential_check;

  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: pos_x = 0: s0 == t || s1 == t
   *                   with s0 the value for the '_t' branch
   *                   and s1 the value for the '_e' branch
   *        pos_x = 1: s0 == true
   *                   with s0 the value for condition '_c'
   *        pos_x = 2: s0 == false
   *                   with s0 the value for condition '_c'
   * IC:    pos_x = 0: (!is_fixed(x) && (s0 = t || s1 = t)) ||
   *                   (is_fixed_true(x) && s0 = t) ||
   *                   (is_fixed_false(x) && s1 = t)
   *                   with s0 the value for '_t' and s1 the value for '_e'
   *        pos_x = 1: (s0 = true && mcb(x, t)) ||
   *                   (s0 = false && s1 = t)
   *                   with s0 the value for '_c' and s1 the value for '_e'
   *        pos_x = 2: (s0 == false && mcb(x, t)) ||
   *                   (s1 == true && s1 = t)
   *                   with s0 the value for '_c' and s1 the value for '_t'
   *
   * Inverse values:
   *   pos_x = 0: t = 0: random value >=s s
   *              t = 1: random value <s s
   *   pos_x = 1: t = 0: random value <=s s
   *              t = 1: random value >s s
   */

  uint64_t pos_s0          = pos_x == 0 ? 1 : 0;
  uint64_t pos_s1          = pos_x == 2 ? 1 : 2;
  const BitVector& s0      = child(pos_s0)->assignment();
  const BitVector& s1      = child(pos_s1)->assignment();
  const BitVectorDomain& x = child(pos_x)->domain();
  bool x_has_fixed_bits    = x.has_fixed_bits();

  if (pos_x == 0)
  {
    int32_t cmp0 = s0.compare(t) == 0;
    int32_t cmp1 = s1.compare(t) == 0;
    if (x.is_fixed())
    {
      if ((x.is_fixed_bit_true(0) && !cmp0)
          || (!x.is_fixed_bit_true(0) && !cmp1))
      {
        return false;
      }
      BV_NODE_CACHE_INVERSE_IF(x.lo());
      return true;
    }
    if (cmp0 || cmp1)
    {
      if (!is_essential_check)
      {
        if (cmp0 && cmp1)
        {
          if (x_has_fixed_bits)
          {
            if (d_rng->flip_coin())
            {
              BitVector bv = BitVector::mk_true();
              if (x.match_fixed_bits(bv))
              {
                BV_NODE_CACHE_INVERSE(std::move(bv));
              }
              else
              {
                BV_NODE_CACHE_INVERSE(BitVector::mk_false());
              }
            }
            else
            {
              BV_NODE_CACHE_INVERSE(BitVector::mk_false());
            }
          }
          else
          {
            BV_NODE_CACHE_INVERSE(d_rng->flip_coin() ? BitVector::mk_true()
                                                     : BitVector::mk_false());
          }
        }
        else if (cmp0)
        {
          BV_NODE_CACHE_INVERSE(BitVector::mk_true());
        }
        else
        {
          assert(cmp1);
          BV_NODE_CACHE_INVERSE(BitVector::mk_false());
        }
      }
      return true;
    }
    return false;
  }

  if (pos_x == 1)
  {
    if (s0.is_true() && (!x_has_fixed_bits || x.match_fixed_bits(t)))
    {
      BV_NODE_CACHE_INVERSE_IF(t);
      return true;
    }
    if (s0.is_false() && s1.compare(t) == 0)
    {
      // return current assignment for disabled branch
      BV_NODE_CACHE_INVERSE_IF(
          x.get_copy_with_fixed_bits(child(pos_x)->assignment()));
      return true;
    }
    return false;
  }

  assert(pos_x == 2);

  if (s0.is_false() && (!x_has_fixed_bits || x.match_fixed_bits(t)))
  {
    BV_NODE_CACHE_INVERSE_IF(t);
    return true;
  }
  if (s0.is_true() && s1.compare(t) == 0)
  {
    // return current assignment for disabled branch
    BV_NODE_CACHE_INVERSE_IF(
        x.get_copy_with_fixed_bits(child(pos_x)->assignment()));
    return true;
  }
  return false;
}

bool
BitVectorIte::is_consistent(const BitVector& t, uint64_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * CC_wo: true
   * CC:    true
   *
   * Consistent value:
   *   pos_x = 0: 0 or 1
   *   pos_x > 0: disabled branch: current assignment
   *              enabled branch : t if bits in x match, else current assignment
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  const BitVector& s0      = child(0)->assignment();
  uint64_t size            = x.size();

  if (pos_x == 0)
  {
    if (x.is_fixed())
    {
      BV_NODE_CACHE_CONSISTENT(x.lo());
    }
    else
    {
      d_consistent.reset(new BitVector(d_rng->flip_coin()
                                           ? BitVector::mk_one(size)
                                           : BitVector::mk_zero(size)));
    }
  }
  else if ((pos_x == 1 && s0.is_false()) || (pos_x == 2 && s0.is_true())
           || !x.match_fixed_bits(t))
  {
    // If the current assignment does not match fixed bits in x, which can
    // happen with const bits propagated from top-level constraints, we fix the
    // assignment of those bits to match these const bits.
    d_consistent.reset(
        new BitVector(x.get_copy_with_fixed_bits(child(pos_x)->assignment())));
  }
  else
  {
    d_consistent.reset(new BitVector(t));
  }
  return true;
}

const BitVector&
BitVectorIte::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t pos_s0     = pos_x == 0 ? 1 : 0;
  uint64_t pos_s1     = pos_x == 2 ? 1 : 2;
  const BitVector& s0 = child(pos_s0)->assignment();
  const BitVector& s1 = child(pos_s1)->assignment();
  assert(d_inverse);
  assert(pos_x != 0 || t.compare(BitVector::bvite(*d_inverse, s0, s1)) == 0);
  assert(pos_x != 1 || t.compare(BitVector::bvite(s0, *d_inverse, s1)) == 0);
  assert(pos_x != 2 || t.compare(BitVector::bvite(s0, s1, *d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorIte::consistent_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(x.match_fixed_bits(*d_consistent));
#endif
  return *d_consistent;
}

uint64_t
BitVectorIte::select_path_non_const(std::vector<uint64_t>& inputs) const
{
  assert(inputs.empty());
  bool cond = child(0)->assignment().is_true();
  for (uint32_t i = 0; i < d_arity; ++i)
  {
    if (child(i)->is_value()) continue;
    if (i == 1 && !cond) continue;
    if (i == 2 && cond) continue;
    inputs.push_back(i);
  }
  if (inputs.size() == 1)
  {
    return inputs[0];
  }
  return static_cast<uint64_t>(-1);
}

std::tuple<uint64_t, bool, bool>
BitVectorIte::select_path(const BitVector& t, std::vector<uint64_t>& ess_inputs)
{
  assert(!all_value());

  std::vector<uint64_t> inputs;
  ess_inputs.clear();

  /* select non-const operand if only one is non-const */
  uint64_t pos_x = select_path_non_const(inputs);
  if (pos_x != static_cast<uint64_t>(-1))
  {
    return {pos_x, true, false};
  }

  bool checked_essential = false;
  /* select essential input if any and path selection based on essential
   * inputs is enabled. */
  if (s_path_sel_essential && d_rng->pick_with_prob(s_prob_pick_ess_input))
  {
    /* determine essential inputs, disabled branches are excluded */
    checked_essential = true;
    for (uint64_t i : inputs)
    {
      if (is_essential(t, i)) ess_inputs.push_back(i);
    }
    if (!ess_inputs.empty())
    {
      pos_x = d_rng->pick_from_set<std::vector<uint64_t>, uint64_t>(ess_inputs);
    }
  }

  /* select random input if operation has no essential inputs or if random path
   * selection enabled */
  if (pos_x == static_cast<uint64_t>(-1))
  {
    /* It can happen that inputs is empty (for example, if cond and enabled
     * branch are const). This shouldn't happen in practice, but can happen
     * in the test setting (when covering all cases), and we guard for this. */
    if (inputs.empty())
    {
      assert(child(0)->is_value());
      assert(child(0)->assignment().is_true()
             || (!child(1)->is_value() && child(2)->is_value()));
      assert(child(0)->assignment().is_false()
             || (!child(2)->is_value() && child(1)->is_value()));
      pos_x = child(0)->assignment().is_true() ? 2 : 1;
    }
    else
    {
      pos_x = d_rng->pick_from_set<std::vector<uint64_t>, uint64_t>(inputs);
    }
  }

  assert(pos_x != static_cast<uint64_t>(-1));
  return {pos_x, false, checked_essential};
}

/* -------------------------------------------------------------------------- */

BitVectorNot::BitVectorNot(RNG* rng, uint64_t size, BitVectorNode* child0)
    : BitVectorNode(rng, size, child0)
{
  assert(size == child0->size());
  _evaluate_and_set_domain();
}

BitVectorNot::BitVectorNot(RNG* rng,
                           const BitVectorDomain& domain,
                           BitVectorNode* child0)
    : BitVectorNode(rng, domain, child0)
{
  assert(domain.size() == child0->size());
  _evaluate_and_set_domain();
}

void
BitVectorNot::_evaluate()
{
  d_assignment.ibvnot(child(0)->assignment());
}

void
BitVectorNot::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorNot::evaluate()
{
  _evaluate();
}

bool
BitVectorNot::is_essential(const BitVector& t, uint64_t pos_x)
{
  return !is_invertible(t, pos_x, true);
}

bool
BitVectorNot::is_invertible(const BitVector& t,
                            uint64_t pos_x,
                            bool is_essential_check)
{
  (void) is_essential_check;

  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: true
   * IC:    mcb(x, ~t)
   *
   * Inverse value: ~t
   */

  const BitVectorDomain& x = child(pos_x)->domain();
  if (!x.has_fixed_bits() || x.match_fixed_bits(t.bvnot()))
  {
    BV_NODE_CACHE_INVERSE_IF(t.bvnot());
    return true;
  }
  return false;
}

bool
BitVectorNot::is_consistent(const BitVector& t, uint64_t pos_x)
{
  /** CC: IC */
  return is_invertible(t, pos_x);
}

const BitVector&
BitVectorNot::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(d_inverse);
  assert(t.compare(d_inverse->bvnot()) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorNot::consistent_value(const BitVector& t, uint64_t pos_x)
{
  return inverse_value(t, pos_x);
}

/* -------------------------------------------------------------------------- */

BitVectorExtract::BitVectorExtract(RNG* rng,
                                   uint64_t size,
                                   BitVectorNode* child0,
                                   uint64_t hi,
                                   uint64_t lo,
                                   bool normalize)
    : BitVectorNode(rng, size, child0), d_hi(hi), d_lo(lo)
{
  assert(hi < child0->size());
  assert(lo <= hi);
  assert(size == hi - lo + 1);
  d_x_slice_left.reset(nullptr);
  d_x_slice_right.reset(nullptr);
  if (normalize)
  {
    child0->register_extract(this);
  }
  _evaluate_and_set_domain();
}

BitVectorExtract::BitVectorExtract(RNG* rng,
                                   const BitVectorDomain& domain,
                                   BitVectorNode* child0,
                                   uint64_t hi,
                                   uint64_t lo,
                                   bool normalize)
    : BitVectorNode(rng, domain, child0), d_hi(hi), d_lo(lo)
{
  assert(hi < child0->size());
  assert(lo <= hi);
  assert(domain.size() == hi - lo + 1);
  d_x_slice_left.reset(nullptr);
  d_x_slice_right.reset(nullptr);
  if (normalize)
  {
    child0->register_extract(this);
  }
  _evaluate_and_set_domain();
}

uint64_t
BitVectorExtract::hi() const
{
  return d_hi;
}

uint64_t
BitVectorExtract::lo() const
{
  return d_lo;
}

void
BitVectorExtract::normalize(BitVectorNode* node)
{
  assert(!d_child0_original);
  assert(!node || node->size() == size());
  assert(!node || node->assignment() == d_assignment);
  d_child0_original = child(0);
  d_hi_original     = d_hi;
  d_lo_original     = d_lo;
  d_children[0]     = node;
  d_hi              = size() - 1;
  d_lo              = 0;
}

bool
BitVectorExtract::is_normalized() const
{
  return d_child0_original != nullptr;
}

void
BitVectorExtract::_evaluate()
{
  d_assignment.ibvextract(child(0)->assignment(), d_hi, d_lo);
}

void
BitVectorExtract::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorExtract::evaluate()
{
  _evaluate();
}

bool
BitVectorExtract::is_essential(const BitVector& t, uint64_t pos_x)
{
  return !is_invertible(t, pos_x, true);
}

bool
BitVectorExtract::is_invertible(const BitVector& t,
                                uint64_t pos_x,
                                bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /**
   * IC_wo: true
   * IC:    mcb(x[hi:lo], t)
   *
   * Inverse value: x[msb: hi+1] o t o x[lo-1:0]
   *
   * We choose with probability s_prob_keep if we keep the current assignment
   * of the don't care bits, i.e., all bits that are not determined by t, or if
   * we set them randomly. If the current assignment does not match fixed bits
   * in x, though, which can happen with const bits propagated from top-level
   * constraints, we fix the assignment of those bits to match these const bits.
   */

  const BitVectorDomain& x = child(pos_x)->domain();

  if (!x.has_fixed_bits() || x.bvextract(d_hi, d_lo).match_fixed_bits(t))
  {
    if (!is_essential_check)
    {
      const BitVector& x_val = child(pos_x)->assignment();
      uint64_t size          = x.size();
      bool keep              = d_rng->pick_with_prob(s_prob_keep);
      bool random            = !keep && d_rng->flip_coin();
      BitVector left, propagated, right;

      if (d_hi < size - 1)
      {
        if (keep)
        {
          left =
              x.get_copy_with_fixed_bits(x_val).ibvextract(size - 1, d_hi + 1);
        }
        else
        {
          if (x.has_fixed_bits())
          {
            if (d_x_slice_left == nullptr)
            {
              d_x_slice_left.reset(
                  new BitVectorDomain(x.bvextract(size - 1, d_hi + 1)));
            }
            if (d_x_slice_left->is_fixed())
            {
              left = d_x_slice_left->lo();
            }
            else
            {
              bool iszero = !random && d_x_slice_left->lo().is_zero();
              bool isones = !random && d_x_slice_left->lo().is_ones();
              if (!random && (iszero || isones))
              {
                if (iszero && isones)
                {
                  left = d_rng->flip_coin() ? d_x_slice_left->lo()
                                            : d_x_slice_left->hi();
                }
                else if (iszero)
                {
                  left = d_x_slice_left->lo();
                }
                else
                {
                  left = d_x_slice_left->hi();
                }
              }
              else
              {
                BitVectorDomainGenerator gen(*d_x_slice_left, d_rng);
                assert(gen.has_random());
                left = gen.random();
              }
            }
          }
          else
          {
            uint64_t lsize = size - 1 - d_hi;
            if (random)
            {
              left = BitVector(lsize, *d_rng);
            }
            else
            {
              left = d_rng->flip_coin() ? BitVector::mk_zero(lsize)
                                        : BitVector::mk_ones(lsize);
            }
          }
        }
      }

      if (d_lo > 0)
      {
        if (keep)
        {
          right = x.get_copy_with_fixed_bits(x_val).bvextract(d_lo - 1, 0);
        }
        else
        {
          if (x.has_fixed_bits())
          {
            if (d_x_slice_right == nullptr)
            {
              d_x_slice_right.reset(
                  new BitVectorDomain(x.bvextract(d_lo - 1, 0)));
            }
            if (d_x_slice_right->is_fixed())
            {
              right = d_x_slice_right->lo();
            }
            else
            {
              bool iszero = !random && d_x_slice_right->lo().is_zero();
              bool isones = !random && d_x_slice_right->lo().is_ones();
              if (!random && (iszero || isones))
              {
                if (iszero && isones)
                {
                  right = d_rng->flip_coin() ? d_x_slice_right->lo()
                                             : d_x_slice_right->hi();
                }
                else if (iszero)
                {
                  right = d_x_slice_right->lo();
                }
                else
                {
                  right = d_x_slice_right->hi();
                }
              }
              else
              {
                BitVectorDomainGenerator gen(*d_x_slice_right, d_rng);
                assert(gen.has_random());
                right = gen.random();
              }
            }
          }
          else
          {
            if (random)
            {
              right = BitVector(d_lo, *d_rng);
            }
            else
            {
              right = d_rng->flip_coin() ? BitVector::mk_zero(d_lo)
                                         : BitVector::mk_ones(d_lo);
            }
          }
        }
      }

      if (left.is_null())
      {
        if (right.is_null())
        {
          BV_NODE_CACHE_INVERSE(t);
        }
        else
        {
          BV_NODE_CACHE_INVERSE(t.bvconcat(right));
        }
      }
      else if (right.is_null())
      {
        BV_NODE_CACHE_INVERSE(left.bvconcat(t));
      }
      else
      {
        BV_NODE_CACHE_INVERSE(left.bvconcat(t).ibvconcat(right));
      }
    }
    return true;
  }
  return false;
}

bool
BitVectorExtract::is_consistent(const BitVector& t, uint64_t pos_x)
{
  /** CC: IC */
  return is_invertible(t, pos_x);
}

const BitVector&
BitVectorExtract::inverse_value(const BitVector& t, uint64_t pos_x)
{
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
  assert(d_inverse);
  assert(t.compare(d_inverse->bvextract(d_hi, d_lo)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
#endif
  return *d_inverse;
}

const BitVector&
BitVectorExtract::consistent_value(const BitVector& t, uint64_t pos_x)
{
  return inverse_value(t, pos_x);
}

std::string
BitVectorExtract::str() const
{
  return "[" + std::to_string(d_id) + "] (" + std::to_string(d_normalized_id)
         + ") " + std::to_string(kind()) + ": "
         + (is_normalized() ? "(normalized) " : "") + "["
         + std::to_string(d_hi) + ":" + std::to_string(d_lo)
         + "]: " + d_domain.str() + " (" + d_assignment.str() + ")";
}

/* -------------------------------------------------------------------------- */

BitVectorSignExtend::BitVectorSignExtend(RNG* rng,
                                         uint64_t size,
                                         BitVectorNode* child0,
                                         uint64_t n)
    : BitVectorNode(rng, size, child0), d_n(n)
{
  assert(size == child0->size() + n);
  _evaluate_and_set_domain();
}

BitVectorSignExtend::BitVectorSignExtend(RNG* rng,
                                         const BitVectorDomain& domain,
                                         BitVectorNode* child0,
                                         uint64_t n)
    : BitVectorNode(rng, domain, child0), d_n(n)
{
  assert(domain.size() == child0->size() + n);
  _evaluate_and_set_domain();
}

void
BitVectorSignExtend::_evaluate()
{
  d_assignment.ibvsext(child(0)->assignment(), d_n);
}

void
BitVectorSignExtend::_evaluate_and_set_domain()
{
  _evaluate();
  if (d_all_value)
  {
    if (!d_is_value)
    {
      d_domain.fix(d_assignment);
      d_is_value = true;
    }
  }
  // we cannot assert that the assignment matches const bits, see header
}

void
BitVectorSignExtend::evaluate()
{
  _evaluate();
}

void
BitVectorSignExtend::normalize_bounds(BitVector* min_u,
                                      BitVector* max_u,
                                      BitVector* min_s,
                                      BitVector* max_s,
                                      BitVector& res_min_lo,
                                      BitVector& res_max_lo,
                                      BitVector& res_min_hi,
                                      BitVector& res_max_hi)
{
  // Sign extension is a bit of a special case in that its bounds are either
  // from 0::x->domain().lo()[msb-1:0] to 0::x->domain().hi()[msb-1:0] or
  // from 1::x->domain().lo()[msb-1:0] to 1::x->domain().hi()[msb-1:0].
  // These two bounds are disjunct.

  res_min_lo = BitVector();
  res_max_lo = BitVector();
  res_min_hi = BitVector();
  res_max_hi = BitVector();

  // First, compute the normalized bounds of the current signed and unsigned
  // bounds on x.
  BitVectorNode::normalize_bounds(min_u,
                                  max_u,
                                  min_s,
                                  max_s,
                                  res_min_lo,
                                  res_max_lo,
                                  res_min_hi,
                                  res_max_hi);

  if (res_min_lo.is_null() && res_min_hi.is_null())
  {
    return;  // conflict
  }

  if (d_n > 0)
  {
    // Now, determine the disjunct bounds imposed from the extension.
    const BitVectorDomain& dx = child(0)->domain();
    BitVectorDomain dxn       = d_domain.bvextract(this->size() - 1, d_n - 1);
    uint64_t dx_size          = dx.size();
    bool has_fixed_bits       = dxn.has_fixed_bits();
    BitVector min_0, max_0, min_1, max_1;

    if (!has_fixed_bits || dxn.has_fixed_bits_false())
    {
      min_0 = BitVector::mk_zero(d_n + 1);
      max_0 = BitVector::mk_zero(d_n + 1);
      if (dx_size > 1)
      {
        min_0.ibvconcat(dx.lo().bvextract(dx_size - 2, 0));
        max_0.ibvconcat(dx.hi().bvextract(dx_size - 2, 0));
      }
    }
    if (!has_fixed_bits || dxn.has_fixed_bits_true())
    {
      min_1 = BitVector::mk_ones(d_n + 1);
      max_1 = BitVector::mk_ones(d_n + 1);
      if (dx_size > 1)
      {
        min_1.ibvconcat(d_domain.lo().bvextract(dx_size - 2, 0));
        max_1.ibvconcat(d_domain.hi().bvextract(dx_size - 2, 0));
      }
    }
    if (!res_min_lo.is_null())
    {
      assert(!res_max_lo.is_null());
      // Identify conflicts.
      if (!max_0.is_null() && max_0.compare(res_min_lo) < 0)
      {
        res_min_lo = BitVector();
        res_max_lo = BitVector();
      }
      else if (!min_0.is_null() && min_0.compare(res_max_lo) > 0)
      {
        res_min_lo = BitVector();
        res_max_lo = BitVector();
      }
      // Tighten bounds.
      if (!res_min_lo.is_null())
      {
        if (!min_0.is_null() && min_0.compare(res_min_lo) > 0)
        {
          res_min_lo = min_0;
        }
        if (!max_0.is_null() && max_0.compare(res_max_lo) < 0)
        {
          res_max_lo = max_0;
        }
      }
    }
    if (!res_min_hi.is_null())
    {
      assert(!res_max_hi.is_null());
      // Identify conflicts.
      if (!max_1.is_null() && max_1.compare(res_min_hi) < 0)
      {
        res_min_hi = BitVector();
        res_max_hi = BitVector();
      }
      else if (!min_1.is_null() && min_1.compare(res_max_hi) > 0)
      {
        res_min_hi = BitVector();
        res_max_hi = BitVector();
      }
      if (res_min_lo.is_null() && res_min_hi.is_null())
      {
        assert(res_max_lo.is_null());
        assert(res_max_hi.is_null());
        return;  // conflict
      }
      // Tighten bounds.
      if (!res_min_hi.is_null())
      {
        if (!min_1.is_null() && min_1.compare(res_min_hi) > 0)
        {
          res_min_hi = min_1;
        }
        if (!max_1.is_null() && max_1.compare(res_max_hi) < 0)
        {
          res_max_hi = max_1;
        }
      }
    }
  }
}

bool
BitVectorSignExtend::is_essential(const BitVector& t, uint64_t pos_x)
{
  return !is_invertible(t, pos_x, true);
}

bool
BitVectorSignExtend::is_invertible(const BitVector& t,
                                   uint64_t pos_x,
                                   bool is_essential_check)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  (void) pos_x;

  const BitVectorDomain& x = child(pos_x)->domain();
  uint64_t size            = t.size();
  BitVector t_x            = t.bvextract(size - 1 - d_n, 0);
  BitVector t_ext          = t.bvextract(size - 1, size - 1 - d_n);

  /**
   * IC_wo: t_ext == ones || t_ext == zero
   *         and t_x   = t[t_size - 1 - n : 0]
   *         and t_ext = t[t_size - 1, t_size - 1 - n]
   *         (i.e., it includes MSB of t_x)
   * IC:     IC_wo && mcb(x, t_x)
   *
   * Inverse value: t_x
   */
  bool ic_wo = t_ext.is_zero() || t_ext.is_ones();

  if (ic_wo && x.has_fixed_bits())
  {
    ic_wo = x.match_fixed_bits(t_x);
  }
  if (ic_wo)
  {
    BV_NODE_CACHE_INVERSE_IF(t_x);
  }

  return ic_wo;
}

bool
BitVectorSignExtend::is_consistent(const BitVector& t, uint64_t pos_x)
{
  /** CC: IC */
  return is_invertible(t, pos_x);
}

const BitVector&
BitVectorSignExtend::inverse_value(const BitVector& t, uint64_t pos_x)
{
  assert(d_inverse != nullptr);
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = child(pos_x)->domain();
#endif
  assert(t.compare(d_inverse->bvsext(d_n)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorSignExtend::consistent_value(const BitVector& t, uint64_t pos_x)
{
  return inverse_value(t, pos_x);
}

std::string
BitVectorSignExtend::str() const
{
  return "[" + std::to_string(d_id) + "] (" + std::to_string(d_normalized_id)
         + ") " + std::to_string(kind()) + ": " + d_domain.str() + " ("
         + d_assignment.str() + ")";
}

/* -------------------------------------------------------------------------- */

#undef BV_NODE_CACHE_INVERSE_IF
#undef BV_NODE_CACHE_CONSISTENT

}  // namespace ls
}  // namespace bzla
