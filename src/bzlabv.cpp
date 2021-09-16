/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

extern "C" {
#include "bzlabv.h"

#include "utils/bzlamem.h"
#include "utils/bzlautil.h"
}

#include "bitvector.h"
#include "bzlabvstruct.h"
#include "utils/bzlarngstruct.h"

BzlaBitVector *
bzla_bv_new(BzlaMemMgr *mm, uint32_t bw)
{
  assert(mm);
  assert(bw > 0);

  BzlaBitVector *res;

  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bw));
  return res;
}

BzlaBitVector *
bzla_bv_new_random(BzlaMemMgr *mm, BzlaRNG *rng, uint32_t bw)
{
  BzlaBitVector *res;

  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bw, *rng->d_rng.get()));
  return res;
}

BzlaBitVector *
bzla_bv_new_random_range(BzlaMemMgr *mm,
                         BzlaRNG *rng,
                         uint32_t bw,
                         const BzlaBitVector *from,
                         const BzlaBitVector *to)
{
  assert(mm);
  assert(rng);
  assert(from);
  assert(to);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(
      bw, *rng->d_rng.get(), *from->d_bv.get(), *to->d_bv.get()));
  return res;
}

BzlaBitVector *
bzla_bv_new_random_signed_range(BzlaMemMgr *mm,
                                BzlaRNG *rng,
                                uint32_t bw,
                                const BzlaBitVector *from,
                                const BzlaBitVector *to)
{
  assert(mm);
  assert(rng);
  assert(from);
  assert(to);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(
      bw, *rng->d_rng.get(), *from->d_bv.get(), *to->d_bv.get(), true));
  return res;
}

BzlaBitVector *
bzla_bv_new_random_bit_range(
    BzlaMemMgr *mm, BzlaRNG *rng, uint32_t bw, uint32_t up, uint32_t lo)
{
  assert(mm);
  assert(rng);
  assert(up >= lo);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bw, *rng->d_rng.get(), up, lo));
  return res;
}

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_bv_char_to_bv(BzlaMemMgr *mm, const char *assignment)
{
  assert(mm);
  assert(assignment);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  std::string a(assignment);
  res->d_bv.reset(new bzla::BitVector(a.size(), a));
  return res;
}

BzlaBitVector *
bzla_bv_uint64_to_bv(BzlaMemMgr *mm, uint64_t value, uint32_t bw)
{
  assert(mm);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bw, value));
  return res;
}

BzlaBitVector *
bzla_bv_int64_to_bv(BzlaMemMgr *mm, int64_t value, uint32_t bw)
{
  assert(mm);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bw, value, true));
  return res;
}

BzlaBitVector *
bzla_bv_const(BzlaMemMgr *mm, const char *str, uint32_t bw)
{
  assert(bzla_util_check_bin_to_bv(mm, str, bw));

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bw, str));
  return res;
}

BzlaBitVector *
bzla_bv_constd(BzlaMemMgr *mm, const char *str, uint32_t bw)
{
  assert(bzla_util_check_dec_to_bv(mm, str, bw));

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bw, str, 10));
  return res;
}

BzlaBitVector *
bzla_bv_consth(BzlaMemMgr *mm, const char *str, uint32_t bw)
{
  assert(bzla_util_check_hex_to_bv(mm, str, bw));

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bw, str, 16));
  return res;
}

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_bv_copy(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(*bv->d_bv.get()));
  return res;
}

/*------------------------------------------------------------------------*/

bool
bzla_bv_str_fits_in_size(uint32_t bw, const char *str, uint32_t base)
{
  assert(str);
  assert(base == 2 || base == 10 || base == 16);
  return bzla::BitVector::fits_in_size(bw, str, base);
}

bool
bzla_bv_uint64_fits_in_size(uint32_t bw, uint64_t value)
{
  return bzla::BitVector::fits_in_size(bw, value);
}

bool
bzla_bv_int64_fits_in_size(uint32_t bw, int64_t value)
{
  return bzla::BitVector::fits_in_size(bw, value, true);
}

size_t
bzla_bv_size(const BzlaBitVector *bv)
{
  assert(bv);
  (void) bv;
  return sizeof(BzlaBitVector);
}

void
bzla_bv_free(BzlaMemMgr *mm, BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);
  bv->d_bv.reset(nullptr);
  bzla_mem_free(mm, bv, sizeof(BzlaBitVector));
}

int32_t
bzla_bv_compare(const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(a);
  assert(b);
  return a->d_bv->compare(*b->d_bv.get());
}

int32_t
bzla_bv_signed_compare(const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(a);
  assert(b);
  return a->d_bv->signed_compare(*b->d_bv.get());
}

uint32_t
bzla_bv_hash(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->hash();
}

/*------------------------------------------------------------------------*/

void
bzla_bv_print_without_new_line(const BzlaBitVector *bv)
{
  assert(bv);

  for (int64_t i = bv->d_bv->size() - 1; i >= 0; --i)
  {
    printf("%d", bzla_bv_get_bit(bv, i));
  }
}

void
bzla_bv_print(const BzlaBitVector *bv)
{
  bzla_bv_print_without_new_line(bv);
  printf("\n");
}

/*------------------------------------------------------------------------*/

char *
bzla_bv_to_char(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  std::string s = bv->d_bv->to_string();
  return bzla_mem_strdup(mm, s.c_str());
}

char *
bzla_bv_to_hex_char(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  std::string s = bv->d_bv->to_string(16);
  return bzla_mem_strdup(mm, s.c_str());
}

char *
bzla_bv_to_dec_char(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  std::string s = bv->d_bv->to_string(10);
  return bzla_mem_strdup(mm, s.c_str());
}

/*------------------------------------------------------------------------*/

uint64_t
bzla_bv_to_uint64(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->to_uint64();
}

/*------------------------------------------------------------------------*/

uint32_t
bzla_bv_get_width(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->size();
}

uint32_t
bzla_bv_get_bit(const BzlaBitVector *bv, uint32_t pos)
{
  assert(bv);
  return bv->d_bv->get_bit(pos);
}

void
bzla_bv_set_bit(BzlaBitVector *bv, uint32_t pos, uint32_t bit)
{
  assert(bv);
  assert(bit == 0 || bit == 1);
  bv->d_bv->set_bit(pos, bit);
}

void
bzla_bv_flip_bit(BzlaBitVector *bv, uint32_t pos)
{
  assert(bv);
  bv->d_bv->flip_bit(pos);
}

/*------------------------------------------------------------------------*/

bool
bzla_bv_is_true(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->is_true();
}

bool
bzla_bv_is_false(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->is_false();
}

bool
bzla_bv_is_zero(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->is_zero();
}

bool
bzla_bv_is_ones(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->is_ones();
}

bool
bzla_bv_is_one(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->is_one();
}

bool
bzla_bv_is_min_signed(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->is_min_signed();
}

bool
bzla_bv_is_max_signed(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->is_max_signed();
}

int64_t
bzla_bv_power_of_two(const BzlaBitVector *bv)
{
  assert(bv);

  int64_t i, j;
  uint32_t bit;
  bool iszero;

  for (i = 0, j = 0, iszero = true; i < bv->d_bv->size(); i++)
  {
    bit = bzla_bv_get_bit(bv, i);
    if (!bit) continue;
    if (bit && !iszero) return -1;
    assert(bit && iszero);
    j      = i;
    iszero = false;
  }
  return j;
}

uint32_t
bzla_bv_get_num_trailing_zeros(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->count_trailing_zeros();
}

uint32_t
bzla_bv_get_num_leading_zeros(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->count_leading_zeros();
}

uint32_t
bzla_bv_get_num_leading_ones(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->d_bv->count_leading_ones();
}

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_bv_one(BzlaMemMgr *mm, uint32_t bw)
{
  assert(mm);
  assert(bw);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bzla::BitVector::mk_one(bw)));
  return res;
}

BzlaBitVector *
bzla_bv_ones(BzlaMemMgr *mm, uint32_t bw)
{
  assert(mm);
  assert(bw);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bzla::BitVector::mk_ones(bw)));
  return res;
}

BzlaBitVector *
bzla_bv_min_signed(BzlaMemMgr *mm, uint32_t bw)
{
  assert(mm);
  assert(bw);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bzla::BitVector::mk_min_signed(bw)));
  return res;
}

BzlaBitVector *
bzla_bv_max_signed(BzlaMemMgr *mm, uint32_t bw)
{
  assert(mm);
  assert(bw);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bzla::BitVector::mk_max_signed(bw)));
  return res;
}

BzlaBitVector *
bzla_bv_neg(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bv->d_bv->bvneg()));
  return res;
}

BzlaBitVector *
bzla_bv_not(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bv->d_bv->bvnot()));
  return res;
}

BzlaBitVector *
bzla_bv_inc(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bv->d_bv->bvinc()));
  return res;
}

BzlaBitVector *
bzla_bv_dec(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bv->d_bv->bvdec()));
  return res;
}

BzlaBitVector *
bzla_bv_redand(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bv->d_bv->bvredand()));
  return res;
}

BzlaBitVector *
bzla_bv_redor(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bv->d_bv->bvredor()));
  return res;
}

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_bv_add(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvadd(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_sub(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvsub(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_and(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvand(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_implies(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvimplies(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_or(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvor(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_nand(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvnand(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_nor(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvnor(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_xnor(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvxnor(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_xor(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvxor(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_eq(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bveq(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_ne(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvne(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_ult(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvult(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_ulte(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvule(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_ugt(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvugt(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_ugte(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvuge(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_slt(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvslt(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_slte(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvsle(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_sgt(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvsgt(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_sgte(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvsge(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_sll_uint64(BzlaMemMgr *mm, const BzlaBitVector *a, uint64_t shift)
{
  assert(mm);
  assert(a);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvshl(shift)));
  return res;
}

BzlaBitVector *
bzla_bv_sll(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvshl(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_sra(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvashr(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_srl_uint64(BzlaMemMgr *mm, const BzlaBitVector *a, uint64_t shift)
{
  assert(mm);
  assert(a);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvshr(shift)));
  return res;
}

BzlaBitVector *
bzla_bv_srl(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvshr(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_mul(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvmul(*b->d_bv.get())));
  return res;
}

void
bzla_bv_udiv_urem(BzlaMemMgr *mm,
                  const BzlaBitVector *a,
                  const BzlaBitVector *b,
                  BzlaBitVector **q,
                  BzlaBitVector **r)
{
  assert(mm);
  assert(a);
  assert(b);

  bzla::BitVector quot, rem;
  a->d_bv->bvudivurem(*b->d_bv.get(), &quot, &rem);
  BZLA_CNEW(mm, *q);
  BZLA_CNEW(mm, *r);
  (*q)->d_bv.reset(new bzla::BitVector(quot));
  (*r)->d_bv.reset(new bzla::BitVector(rem));
}

BzlaBitVector *
bzla_bv_udiv(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvudiv(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_urem(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvurem(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_sdiv(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvsdiv(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_srem(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvsrem(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_concat(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(a->d_bv->bvconcat(*b->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_slice(BzlaMemMgr *mm,
              const BzlaBitVector *bv,
              uint32_t upper,
              uint32_t lower)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bv->d_bv->bvextract(upper, lower)));
  return res;
}

BzlaBitVector *
bzla_bv_sext(BzlaMemMgr *mm, const BzlaBitVector *bv, uint32_t len)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bv->d_bv->bvsext(len)));
  return res;
}

BzlaBitVector *
bzla_bv_uext(BzlaMemMgr *mm, const BzlaBitVector *bv, uint32_t len)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bv->d_bv->bvzext(len)));
  return res;
}

BzlaBitVector *
bzla_bv_ite(BzlaMemMgr *mm,
            const BzlaBitVector *c,
            const BzlaBitVector *t,
            const BzlaBitVector *e)
{
  assert(c);
  assert(t);
  assert(e);

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(
      bzla::BitVector::bvite(*c->d_bv.get(), *t->d_bv.get(), *e->d_bv.get())));
  return res;
}

BzlaBitVector *
bzla_bv_flipped_bit(BzlaMemMgr *mm, const BzlaBitVector *bv, uint32_t pos)
{
  assert(bv);

  BzlaBitVector *res = bzla_bv_copy(mm, bv);
  bzla_bv_flip_bit(res, pos);
  return res;
}

BzlaBitVector *
bzla_bv_flipped_bit_range(BzlaMemMgr *mm,
                          const BzlaBitVector *bv,
                          uint32_t upper,
                          uint32_t lower)
{
  assert(mm);
  assert(lower <= upper);

  BzlaBitVector *res = bzla_bv_copy(mm, bv);
  for (uint32_t i = lower; i <= upper; i++)
  {
    bzla_bv_set_bit(res, i, bzla_bv_get_bit(res, i) ? 0 : 1);
  }
  return res;
}

/*------------------------------------------------------------------------*/

bool
bzla_bv_is_uaddo(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  return a->d_bv->is_uadd_overflow(*b->d_bv.get());
}

bool
bzla_bv_is_umulo(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  return a->d_bv->is_umul_overflow(*b->d_bv.get());
}

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_bv_mod_inverse(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);
  assert(bzla_bv_get_bit(bv, 0)); /* bv must be odd */

  BzlaBitVector *res;
  BZLA_CNEW(mm, res);
  res->d_bv.reset(new bzla::BitVector(bv->d_bv->bvmodinv()));
  return res;
}

/*------------------------------------------------------------------------*/

BzlaSpecialConstBitVector
bzla_bv_is_special_const(const BzlaBitVector *bv)
{
  assert(bv);

  if (bzla_bv_is_zero(bv)) return BZLA_SPECIAL_CONST_BV_ZERO;
  if (bzla_bv_is_one(bv))
  {
    return bv->d_bv->size() == 1 ? BZLA_SPECIAL_CONST_BV_ONE_ONES
                                 : BZLA_SPECIAL_CONST_BV_ONE;
  }
  if (bzla_bv_is_ones(bv))
  {
    assert(bv->d_bv->size() > 1);
    return BZLA_SPECIAL_CONST_BV_ONES;
  }
  if (bzla_bv_is_min_signed(bv))
  {
    return BZLA_SPECIAL_CONST_BV_MIN_SIGNED;
  }
  if (bzla_bv_is_max_signed(bv))
  {
    return BZLA_SPECIAL_CONST_BV_MAX_SIGNED;
  }
  return BZLA_SPECIAL_CONST_BV_NONE;
}

/*------------------------------------------------------------------------*/

BzlaBitVectorTuple *
bzla_bv_new_tuple(BzlaMemMgr *mm, uint32_t arity)
{
  assert(mm);

  BzlaBitVectorTuple *res = 0;

  BZLA_CNEW(mm, res);
  if (arity) BZLA_CNEWN(mm, res->bv, arity);
  res->arity = arity;
  return res;
}

void
bzla_bv_add_to_tuple(BzlaMemMgr *mm,
                     BzlaBitVectorTuple *t,
                     const BzlaBitVector *bv,
                     uint32_t pos)
{
  assert(mm);
  assert(t);
  assert(bv);
  assert(pos < t->arity);
  assert(!t->bv[pos]);
  t->bv[pos] = bzla_bv_copy(mm, bv);
}

void
bzla_bv_free_tuple(BzlaMemMgr *mm, BzlaBitVectorTuple *t)
{
  assert(mm);
  assert(t);

  uint32_t i;

  if (t->arity)
  {
    for (i = 0; i < t->arity; i++) bzla_bv_free(mm, t->bv[i]);
    bzla_mem_free(mm, t->bv, sizeof(BzlaBitVectorTuple *) * t->arity);
  }
  bzla_mem_free(mm, t, sizeof(BzlaBitVectorTuple));
}

int32_t
bzla_bv_compare_tuple(const BzlaBitVectorTuple *t0,
                      const BzlaBitVectorTuple *t1)
{
  assert(t0);
  assert(t1);

  uint32_t i;
  if (t0->arity != t1->arity) return -1;

  for (i = 0; i < t0->arity; i++)
  {
    assert(t0->bv[i]);
    assert(t1->bv[i]);
    if (t0->bv[i]->d_bv->size() != t1->bv[i]->d_bv->size()
        || bzla_bv_compare(t0->bv[i], t1->bv[i]) != 0)
      return 1;
  }
  return 0;
}

uint32_t
bzla_bv_hash_tuple(const BzlaBitVectorTuple *t)
{
  assert(t);

  uint32_t hash = 0;
  for (uint32_t i = 0, j = 0; i < t->arity; i++)
  {
    assert(t->bv[i]);
    hash += bzla_bv_hash(t->bv[i]) * bzla::BitVector::s_hash_primes[j++];
    if (j == bzla::BitVector::s_n_primes) j = 0;
  }
  return hash;
}

BzlaBitVectorTuple *
bzla_bv_copy_tuple(BzlaMemMgr *mm, BzlaBitVectorTuple *t)
{
  assert(mm);
  assert(t);

  BzlaBitVectorTuple *res = 0;
  uint32_t i;

  res = bzla_bv_new_tuple(mm, t->arity);

  for (i = 0; i < t->arity; i++)
  {
    assert(t->bv[i]);
    res->bv[i] = bzla_bv_copy(mm, t->bv[i]);
  }
  return res;
}

size_t
bzla_bv_size_tuple(BzlaBitVectorTuple *t)
{
  assert(t);

  uint32_t i;
  size_t res = 0;

  res = sizeof(BzlaBitVectorTuple) + t->arity * sizeof(BzlaBitVector *);
  for (i = 0; i < t->arity; i++) res += bzla_bv_size(t->bv[i]);
  return res;
}

/*------------------------------------------------------------------------*/
