/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include <gmpxx.h>

#include <sstream>
#include <unordered_map>
#include <vector>

#include "bv/bitvector.h"
#include "bzlabvstruct.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "solver/fp/symfpu_wrapper.h"
#include "solver/fp/word_blaster_old.h"

extern "C" {
#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlafp.h"
#include "bzlanode.h"
#include "bzlarm.h"
#include "bzlasort.h"
#include "utils/bzlaabort.h"
#include "utils/bzlamem.h"
#include "utils/bzlautil.h"
}

#include "node/node_manager.h"
#include "symfpu/core/add.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/remainder.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/core/unpackedFloat.h"

static std::unordered_map<BzlaRoundingMode, bzla::RoundingMode> bzlarm2rm = {
    {BZLA_RM_RNA, bzla::RoundingMode::RNA},
    {BZLA_RM_RNE, bzla::RoundingMode::RNE},
    {BZLA_RM_RTN, bzla::RoundingMode::RTN},
    {BZLA_RM_RTP, bzla::RoundingMode::RTP},
    {BZLA_RM_RTZ, bzla::RoundingMode::RTZ},
};

struct BzlaFloatingPoint
{
  std::unique_ptr<bzla::FloatingPoint> d_fp;
};

void
bzla_fp_free(Bzla *bzla, BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  fp->d_fp.reset(nullptr);
  BZLA_DELETE(bzla->mm, fp);
}

BzlaFloatingPoint *
bzla_fp_copy(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;

  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::FloatingPoint(*fp->d_fp));
  return res;
}

uint32_t
bzla_fp_get_exp_width(const BzlaFloatingPoint *fp)
{
  return fp->d_fp->size()->exponentWidth();
}

uint32_t
bzla_fp_get_sig_width(const BzlaFloatingPoint *fp)
{
  return fp->d_fp->size()->significandWidth();
}

uint32_t
bzla_fp_get_bv_width(const BzlaFloatingPoint *fp)
{
  return fp->d_fp->size()->exponentWidth()
         + fp->d_fp->size()->significandWidth();
}

BzlaBitVector *
bzla_fp_as_bv(Bzla *bzla, BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  bzla::BitVector bv = fp->d_fp->as_bv();
  BzlaBitVector *bbv = bzla_bv_new(bzla->mm, bv.size());
  bbv->d_bv.reset(new bzla::BitVector(bv));
  return bbv;
}

void
bzla_fp_ieee_bv_as_bvs(Bzla *bzla,
                       const BzlaBitVector *bv,
                       BzlaSortId fp_sort,
                       BzlaBitVector **sign,
                       BzlaBitVector **exp,
                       BzlaBitVector **sig)
{
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  bzla::BitVector bsign, bexp, bsig;
  bzla::NodeManager &nm = bzla::NodeManager::get();
  bzla::FloatingPoint::ieee_bv_as_bvs(
      nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, fp_sort),
                    bzla_sort_fp_get_sig_width(bzla, fp_sort)),
      *bv->d_bv,
      bsign,
      bexp,
      bsig);
  *sign = bzla_bv_new(bzla->mm, bsign.size());
  (*sign)->d_bv.reset(new bzla::BitVector(bsign));
  *exp = bzla_bv_new(bzla->mm, bexp.size());
  (*exp)->d_bv.reset(new bzla::BitVector(bexp));
  *sig = bzla_bv_new(bzla->mm, bsig.size());
  (*sig)->d_bv.reset(new bzla::BitVector(bsig));
}

BzlaFloatingPoint *
bzla_fp_get_fp(BzlaNode *node)
{
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_fp_const(node));
  return static_cast<BzlaFloatingPoint *>(((BzlaFPConstNode *) node)->fp);
}

void *
bzla_fp_get_unpacked_float(BzlaNode *node)
{
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_fp_const(node));
  return bzla_fp_get_fp(node)->d_fp->unpacked();
}

uint32_t
bzla_fp_hash(const BzlaFloatingPoint *fp)
{
  return fp->d_fp->hash();
}

int32_t
bzla_fp_compare(const BzlaFloatingPoint *a, const BzlaFloatingPoint *b)
{
  assert(a);
  assert(b);

  return a->d_fp->compare(*b->d_fp);
}

bool
bzla_fp_is_zero(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  return fp->d_fp->fpiszero();
}

bool
bzla_fp_is_normal(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  return fp->d_fp->fpisnormal();
}

bool
bzla_fp_is_subnormal(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  return fp->d_fp->fpissubnormal();
}

bool
bzla_fp_is_nan(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  return fp->d_fp->fpisnan();
}

bool
bzla_fp_is_inf(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  return fp->d_fp->fpisinf();
}

bool
bzla_fp_is_neg(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  return fp->d_fp->fpisneg();
}

bool
bzla_fp_is_pos(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  return fp->d_fp->fpispos();
}

bool
bzla_fp_eq(Bzla *bzla,
           const BzlaFloatingPoint *fp0,
           const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->d_fp->size()->exponentWidth()
         == fp1->d_fp->size()->exponentWidth());
  assert(fp0->d_fp->size()->significandWidth()
         == fp1->d_fp->size()->significandWidth());

  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  return fp0->d_fp->fpeq(*fp1->d_fp);
}

bool
bzla_fp_lt(Bzla *bzla,
           const BzlaFloatingPoint *fp0,
           const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->d_fp->size()->exponentWidth()
         == fp1->d_fp->size()->exponentWidth());
  assert(fp0->d_fp->size()->significandWidth()
         == fp1->d_fp->size()->significandWidth());

  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  return fp0->d_fp->fplt(*fp1->d_fp);
}

bool
bzla_fp_lte(Bzla *bzla,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->d_fp->size()->exponentWidth()
         == fp1->d_fp->size()->exponentWidth());
  assert(fp0->d_fp->size()->significandWidth()
         == fp1->d_fp->size()->significandWidth());

  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  return fp0->d_fp->fple(*fp1->d_fp);
}

BzlaFloatingPoint *
bzla_fp_zero(Bzla *bzla, BzlaSortId sort, bool sign)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  bzla::NodeManager &nm = bzla::NodeManager::get();
  bzla::Type type = nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, sort),
                                  bzla_sort_fp_get_sig_width(bzla, sort));
  res->d_fp.reset(
      new bzla::FloatingPoint(bzla::FloatingPoint::fpzero(type, sign)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_inf(Bzla *bzla, BzlaSortId sort, bool sign)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  bzla::NodeManager &nm = bzla::NodeManager::get();
  bzla::Type type = nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, sort),
                                  bzla_sort_fp_get_sig_width(bzla, sort));
  res->d_fp.reset(
      new bzla::FloatingPoint(bzla::FloatingPoint::fpinf(type, sign)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_nan(Bzla *bzla, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  bzla::NodeManager &nm = bzla::NodeManager::get();
  bzla::Type type = nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, sort),
                                  bzla_sort_fp_get_sig_width(bzla, sort));
  res->d_fp.reset(new bzla::FloatingPoint(bzla::FloatingPoint::fpnan(type)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_fp(Bzla *bzla,
           BzlaBitVector *sign,
           BzlaBitVector *exp,
           BzlaBitVector *sig)
{
  assert(bzla);
  assert(sign);
  assert(exp);
  assert(sig);

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::FloatingPoint(
      bzla::FloatingPoint::fpfp(*sign->d_bv, *exp->d_bv, *sig->d_bv)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_from_bv(Bzla *bzla, BzlaSortId sort, const BzlaBitVector *bv_const)
{
  assert(bzla);
  assert(sort);
  assert(bv_const);
  assert(bzla_sort_is_fp(bzla, sort));
  assert(bzla_sort_fp_get_exp_width(bzla, sort)
             + bzla_sort_fp_get_sig_width(bzla, sort)
         == bzla_bv_get_width(bv_const));
  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  bzla::NodeManager &nm = bzla::NodeManager::get();
  bzla::Type type = nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, sort),
                                  bzla_sort_fp_get_sig_width(bzla, sort));
  res->d_fp.reset(new bzla::FloatingPoint(type, *bv_const->d_bv));
  return res;
}

BzlaFloatingPoint *
bzla_fp_abs(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::FloatingPoint(fp->d_fp->fpabs()));
  return res;
}

BzlaFloatingPoint *
bzla_fp_neg(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::FloatingPoint(fp->d_fp->fpneg()));
  return res;
}

BzlaFloatingPoint *
bzla_fp_sqrt(Bzla *bzla, const BzlaRoundingMode rm, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::FloatingPoint(fp->d_fp->fpsqrt(bzlarm2rm.at(rm))));
  return res;
}

BzlaFloatingPoint *
bzla_fp_rti(Bzla *bzla, const BzlaRoundingMode rm, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::FloatingPoint(fp->d_fp->fprti(bzlarm2rm.at(rm))));
  return res;
}

BzlaFloatingPoint *
bzla_fp_rem(Bzla *bzla,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->d_fp->size()->exponentWidth()
         == fp1->d_fp->size()->exponentWidth());
  assert(fp0->d_fp->size()->significandWidth()
         == fp1->d_fp->size()->significandWidth());

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::FloatingPoint(fp0->d_fp->fprem(*fp1->d_fp)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_add(Bzla *bzla,
            const BzlaRoundingMode rm,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->d_fp->size()->exponentWidth()
         == fp1->d_fp->size()->exponentWidth());
  assert(fp0->d_fp->size()->significandWidth()
         == fp1->d_fp->size()->significandWidth());

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::FloatingPoint(fp0->d_fp->fpadd(bzlarm2rm.at(rm), *fp1->d_fp)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_mul(Bzla *bzla,
            const BzlaRoundingMode rm,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->d_fp->size()->exponentWidth()
         == fp1->d_fp->size()->exponentWidth());
  assert(fp0->d_fp->size()->significandWidth()
         == fp1->d_fp->size()->significandWidth());

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::FloatingPoint(fp0->d_fp->fpmul(bzlarm2rm.at(rm), *fp1->d_fp)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_div(Bzla *bzla,
            const BzlaRoundingMode rm,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->d_fp->size()->exponentWidth()
         == fp1->d_fp->size()->exponentWidth());
  assert(fp0->d_fp->size()->significandWidth()
         == fp1->d_fp->size()->significandWidth());

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::FloatingPoint(fp0->d_fp->fpdiv(bzlarm2rm.at(rm), *fp1->d_fp)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_fma(Bzla *bzla,
            const BzlaRoundingMode rm,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1,
            const BzlaFloatingPoint *fp2)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp2);
  assert(fp0->d_fp->size()->exponentWidth()
         == fp1->d_fp->size()->exponentWidth());
  assert(fp0->d_fp->size()->significandWidth()
         == fp1->d_fp->size()->significandWidth());
  assert(fp0->d_fp->size()->exponentWidth()
         == fp2->d_fp->size()->exponentWidth());
  assert(fp0->d_fp->size()->significandWidth()
         == fp2->d_fp->size()->significandWidth());

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::FloatingPoint(
      fp0->d_fp->fpfma(bzlarm2rm.at(rm), *fp1->d_fp, *fp2->d_fp)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_convert(Bzla *bzla,
                BzlaSortId sort,
                const BzlaRoundingMode rm,
                const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(sort);
  assert(fp);

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  bzla::NodeManager &nm = bzla::NodeManager::get();
  bzla::Type type = nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, sort),
                                  bzla_sort_fp_get_sig_width(bzla, sort));
  res->d_fp.reset(new bzla::FloatingPoint(type, bzlarm2rm.at(rm), *fp->d_fp));
  return res;
}

BzlaFloatingPoint *
bzla_fp_convert_from_ubv(Bzla *bzla,
                         BzlaSortId sort,
                         const BzlaRoundingMode rm,
                         const BzlaBitVector *bv)
{
  assert(bzla);
  assert(sort);
  assert(bv);

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  bzla::NodeManager &nm = bzla::NodeManager::get();
  bzla::Type type = nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, sort),
                                  bzla_sort_fp_get_sig_width(bzla, sort));
  res->d_fp.reset(
      new bzla::FloatingPoint(type, bzlarm2rm.at(rm), *bv->d_bv, false));
  return res;
}

BzlaFloatingPoint *
bzla_fp_convert_from_sbv(Bzla *bzla,
                         BzlaSortId sort,
                         const BzlaRoundingMode rm,
                         const BzlaBitVector *bv)
{
  assert(bzla);
  assert(sort);
  assert(bv);

  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  bzla::NodeManager &nm = bzla::NodeManager::get();
  bzla::Type type = nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, sort),
                                  bzla_sort_fp_get_sig_width(bzla, sort));
  res->d_fp.reset(
      new bzla::FloatingPoint(type, bzlarm2rm.at(rm), *bv->d_bv, true));
  return res;
}

BzlaFloatingPoint *
bzla_fp_convert_from_real(Bzla *bzla,
                          BzlaSortId sort,
                          const BzlaRoundingMode rm,
                          const char *real)
{
  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  bzla::NodeManager &nm = bzla::NodeManager::get();
  bzla::Type type = nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, sort),
                                  bzla_sort_fp_get_sig_width(bzla, sort));
  res->d_fp.reset(new bzla::FloatingPoint(
      bzla::FloatingPoint::from_real(type, bzlarm2rm.at(rm), real)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_convert_from_rational(Bzla *bzla,
                              BzlaSortId sort,
                              const BzlaRoundingMode rm,
                              const char *num,
                              const char *den)
{
  BzlaFloatingPoint *res;
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  bzla::NodeManager &nm = bzla::NodeManager::get();
  bzla::Type type = nm.mk_fp_type(bzla_sort_fp_get_exp_width(bzla, sort),
                                  bzla_sort_fp_get_sig_width(bzla, sort));
  res->d_fp.reset(new bzla::FloatingPoint(
      bzla::FloatingPoint::from_rational(type, bzlarm2rm.at(rm), num, den)));
  return res;
}

void
bzla_fp_word_blaster_get_introduced_ufs(Bzla *bzla, BzlaNodePtrStack *ufs)
{
  assert(bzla);
  if (!bzla->word_blaster) return;
  bzla::fp::WordBlasterOld *word_blaster =
      static_cast<bzla::fp::WordBlasterOld *>(bzla->word_blaster);

  std::vector<BzlaNode *> introduced_ufs;
  word_blaster->get_introduced_ufs(introduced_ufs);
  for (BzlaNode *uf : introduced_ufs)
  {
    BZLA_PUSH_STACK(*ufs, uf);
  }
}

/* -------------------------------------------------------------------------- */

void *
bzla_fp_word_blaster_new(Bzla *bzla)
{
  return new bzla::fp::WordBlasterOld(bzla);
}

void
bzla_fp_word_blaster_delete(Bzla *bzla)
{
  assert(bzla);
  if (!bzla->word_blaster) return;
  bzla::fp::WordBlasterOld *wb =
      static_cast<bzla::fp::WordBlasterOld *>(bzla->word_blaster);
  bzla::fp::WordBlasterOld::set_s_bzla(wb->get_bzla());
  delete wb;
  bzla->word_blaster = nullptr;
}

void
bzla_fp_word_blaster_add_additional_assertions(Bzla *bzla)
{
  assert(bzla);
  if (!bzla->word_blaster) return;
  bzla::fp::WordBlasterOld *word_blaster =
      static_cast<bzla::fp::WordBlasterOld *>(bzla->word_blaster);
  word_blaster->add_additional_assertions();
}

BzlaNode *
bzla_fp_word_blast(Bzla *bzla, BzlaNode *node)
{
  assert(bzla);
  assert(bzla->word_blaster);
  assert(node);
  bzla::fp::WordBlasterOld::set_s_bzla(bzla);
  BzlaNode *res = static_cast<bzla::fp::WordBlasterOld *>(bzla->word_blaster)
                      ->get_word_blasted_node(node);
  return bzla_simplify_exp(bzla, res);
}

/* -------------------------------------------------------------------------- */
