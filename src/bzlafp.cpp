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

#include "bzlabvstruct.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "solver/fp/symfpu_wrapper.h"

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

template <bool is_signed>
class BzlaFPSymBV;
class BzlaFPWordBlaster;

namespace bzla::fp {
class FloatingPointSortInfo;
}

static std::unordered_map<BzlaRoundingMode, bzla::fp::RoundingMode> bzlarm2rm =
    {
        {BZLA_RM_RNA, bzla::fp::RoundingMode::RNA},
        {BZLA_RM_RNE, bzla::fp::RoundingMode::RNE},
        {BZLA_RM_RTN, bzla::fp::RoundingMode::RTN},
        {BZLA_RM_RTP, bzla::fp::RoundingMode::RTP},
        {BZLA_RM_RTZ, bzla::fp::RoundingMode::RTZ},
};

/* ========================================================================== */
/* Floating-Point constants.                                                  */
/* ========================================================================== */

struct BzlaFloatingPoint
{
  std::unique_ptr<bzla::fp::FloatingPoint> d_fp;
};

/* ========================================================================== */
/* Word blaster.                                                              */
/* ========================================================================== */

struct BzlaSortHashFunction
{
  size_t operator()(BzlaSortId sort) const { return sort; }
};

struct BzlaSortPairHashFunction
{
  size_t operator()(const std::pair<BzlaSortId, BzlaSortId> &p) const
  {
    return p.first * 333444569u + p.second * 76891121u;
  }
};

struct BzlaNodeHashFunction
{
  size_t operator()(BzlaNode *exp) const { return bzla_node_hash_by_id(exp); }
};

class BzlaFPWordBlaster
{
 public:
  BzlaFPWordBlaster(Bzla *bzla) : d_bzla(bzla) {}
  ~BzlaFPWordBlaster();

  BzlaNode *word_blast(BzlaNode *node);
  BzlaNode *get_word_blasted_node(BzlaNode *node);
  void get_introduced_ufs(std::vector<BzlaNode *> &ufs);
  void add_additional_assertions();

  BzlaFPWordBlaster *clone(Bzla *cbzla, BzlaNodeMap *exp_map);

  Bzla *get_bzla() { return d_bzla; }

  static void set_s_bzla(Bzla *bzla)
  {
    bzla::fp::FloatingPoint::s_bzla         = bzla;
    bzla::fp::FloatingPointSortInfo::s_bzla = bzla;
    bzla::fp::BzlaFPBV<true>::s_bzla        = bzla;
    bzla::fp::BzlaFPBV<false>::s_bzla       = bzla;
    bzla::fp::BzlaFPSymRM::s_bzla           = bzla;
    bzla::fp::BzlaFPSymProp::s_bzla         = bzla;
    bzla::fp::BzlaFPSymBV<true>::s_bzla     = bzla;
    bzla::fp::BzlaFPSymBV<false>::s_bzla    = bzla;
  }

 private:
  BzlaNode *min_max_uf(BzlaNode *node);
  BzlaNode *sbv_ubv_uf(BzlaNode *node);

  using BzlaSymUnpackedFloat =
      ::symfpu::unpackedFloat<bzla::fp::BzlaFPSymTraits>;
  using BzlaFPUnpackedFloatMap = std::
      unordered_map<BzlaNode *, BzlaSymUnpackedFloat, BzlaNodeHashFunction>;
  using BzlaFPSymRMMap = std::
      unordered_map<BzlaNode *, bzla::fp::BzlaFPSymRM, BzlaNodeHashFunction>;
  using BzlaFPSymPropMap = std::
      unordered_map<BzlaNode *, bzla::fp::BzlaFPSymProp, BzlaNodeHashFunction>;
  using BzlaFPPackedFloatMap = std::unordered_map<BzlaNode *,
                                                  bzla::fp::BzlaFPSymBV<false>,
                                                  BzlaNodeHashFunction>;
  using BzlaFPSymSBVMap      = std::unordered_map<BzlaNode *,
                                             bzla::fp::BzlaFPSymBV<true>,
                                             BzlaNodeHashFunction>;
  using BzlaFPSymUBVMap      = std::unordered_map<BzlaNode *,
                                             bzla::fp::BzlaFPSymBV<false>,
                                             BzlaNodeHashFunction>;

  BzlaFPSymRMMap d_rm_map;
  BzlaFPSymPropMap d_prop_map;
  BzlaFPSymUBVMap d_ubv_map;
  BzlaFPSymSBVMap d_sbv_map;
  BzlaFPUnpackedFloatMap d_unpacked_float_map;
  BzlaFPPackedFloatMap d_packed_float_map;

  std::unordered_map<BzlaSortId, BzlaNode *, BzlaSortHashFunction>
      d_min_max_uf_map;

  std::unordered_map<std::pair<BzlaSortId, BzlaSortId>,
                     BzlaNode *,
                     BzlaSortPairHashFunction>
      d_sbv_ubv_uf_map;

  std::vector<BzlaNode *> d_additional_assertions;
  Bzla *d_bzla;
};

/* -------------------------------------------------------------------------- */

static bzla::fp::UnpackedFloat *
fp_get_unpacked_float(BzlaNode *node)
{
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_fp_const(node));
  return static_cast<bzla::fp::UnpackedFloat *>(
      bzla_fp_get_fp(node)->d_fp->unpacked());
}

static std::string
create_component_symbol(BzlaNode *node, const char *s)
{
  assert(node);
  assert(s);
  std::stringstream ss;
  ss << "_fp_var_" << bzla_node_get_id(node) << s << "_component_";
  return ss.str();
}

BzlaFPWordBlaster::~BzlaFPWordBlaster()
{
  for (const auto &p : d_min_max_uf_map)
  {
    bzla_sort_release(d_bzla, p.first);
    bzla_node_release(d_bzla, p.second);
  }
  for (const auto &p : d_sbv_ubv_uf_map)
  {
    bzla_sort_release(d_bzla, p.first.first);
    bzla_sort_release(d_bzla, p.first.second);
    bzla_node_release(d_bzla, p.second);
  }
  for (const auto &p : d_unpacked_float_map)
  {
    bzla_node_release(d_bzla, p.first);
  }
  for (const auto &p : d_rm_map)
  {
    bzla_node_release(d_bzla, p.first);
  }
  for (const auto &p : d_prop_map)
  {
    bzla_node_release(d_bzla, p.first);
  }
  for (const auto &p : d_ubv_map)
  {
    bzla_node_release(d_bzla, p.first);
  }
  for (const auto &p : d_sbv_map)
  {
    bzla_node_release(d_bzla, p.first);
  }
  for (BzlaNode *node : d_additional_assertions)
  {
    bzla_node_release(d_bzla, node);
  }
}

BzlaNode *
BzlaFPWordBlaster::word_blast(BzlaNode *node)
{
  assert(d_bzla);
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(d_bzla == bzla_node_real_addr(node)->bzla);
  assert((bzla_node_is_bv(d_bzla, node) && node->arity
          && (bzla_node_is_fp(d_bzla, node->e[0])
              || bzla_node_is_rm(d_bzla, node->e[0])))
         || bzla_node_is_fp(d_bzla, node) || bzla_node_is_rm(d_bzla, node));

  BzlaNode *res = nullptr;

  BzlaNode *cur;
  std::vector<BzlaNode *> to_visit;
  std::unordered_map<BzlaNode *, uint32_t, BzlaNodeHashFunction> visited;

  to_visit.push_back(node);

  while (!to_visit.empty())
  {
    cur = bzla_node_real_addr(to_visit.back());
    assert(!bzla_node_real_addr(cur)->parameterized);
    to_visit.pop_back();

    if (d_prop_map.find(cur) != d_prop_map.end()
        || d_rm_map.find(cur) != d_rm_map.end()
        || d_sbv_map.find(cur) != d_sbv_map.end()
        || d_ubv_map.find(cur) != d_ubv_map.end()
        || d_unpacked_float_map.find(cur) != d_unpacked_float_map.end())
    {
      continue;
    }

    if (visited.find(cur) == visited.end())
    {
      visited.emplace(cur, 0);
      to_visit.push_back(cur);

      /* We treat applies and quantifiers as variables. */
      if (!bzla_node_is_apply(cur) && !bzla_node_is_forall(cur))
      {
        for (uint32_t i = 0; i < cur->arity; ++i)
        {
          to_visit.push_back(cur->e[i]);
        }
      }
    }
    else if (visited.at(cur) == 0)
    {
      if (bzla_node_is_cond(cur) && bzla_node_is_rm(d_bzla, cur->e[1]))
      {
        assert(d_rm_map.find(cur->e[1]) != d_rm_map.end());
        assert(d_rm_map.find(cur->e[2]) != d_rm_map.end());
        d_rm_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::ite<bzla::fp::BzlaFPSymProp, bzla::fp::BzlaFPSymRM>::iteOp(
                bzla::fp::BzlaFPSymProp(cur->e[0]),
                d_rm_map.at(cur->e[1]),
                d_rm_map.at(cur->e[2])));
      }
      else if (bzla_node_is_cond(cur) && bzla_node_is_fp(d_bzla, cur->e[1]))
      {
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[2])
               != d_unpacked_float_map.end());

        // Consruct ITEs over unpacked float components
        auto uf1 = d_unpacked_float_map.at(cur->e[1]);
        auto uf2 = d_unpacked_float_map.at(cur->e[2]);

        BzlaNode *nan = bzla_exp_cond(
            d_bzla, cur->e[0], uf1.getNaN().getNode(), uf2.getNaN().getNode());
        BzlaNode *inf = bzla_exp_cond(
            d_bzla, cur->e[0], uf1.getInf().getNode(), uf2.getInf().getNode());
        BzlaNode *zero = bzla_exp_cond(d_bzla,
                                       cur->e[0],
                                       uf1.getZero().getNode(),
                                       uf2.getZero().getNode());
        BzlaNode *sign = bzla_exp_cond(d_bzla,
                                       cur->e[0],
                                       uf1.getSign().getNode(),
                                       uf2.getSign().getNode());
        BzlaNode *exp  = bzla_exp_cond(d_bzla,
                                      cur->e[0],
                                      uf1.getExponent().getNode(),
                                      uf2.getExponent().getNode());
        BzlaNode *sig  = bzla_exp_cond(d_bzla,
                                      cur->e[0],
                                      uf1.getSignificand().getNode(),
                                      uf2.getSignificand().getNode());

        BzlaSymUnpackedFloat ite(nan, inf, zero, sign, exp, sig);
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur), ite);
        bzla_node_release(d_bzla, nan);
        bzla_node_release(d_bzla, inf);
        bzla_node_release(d_bzla, zero);
        bzla_node_release(d_bzla, sign);
        bzla_node_release(d_bzla, exp);
        bzla_node_release(d_bzla, sig);
      }
      else if (bzla_node_is_rm_const(cur))
      {
        d_rm_map.emplace(bzla_node_copy(d_bzla, cur),
                         bzla::fp::BzlaFPSymRM(cur));
      }
      else if (bzla_node_is_rm_var(cur)
               || (bzla_node_is_apply(cur) && bzla_node_is_rm(d_bzla, cur)))
      {
        bzla::fp::BzlaFPSymRM var(cur);
        d_rm_map.emplace(bzla_node_copy(d_bzla, cur), var);
        d_additional_assertions.push_back(
            bzla_node_copy(d_bzla, var.valid().getNode()));
      }
      else if (bzla_node_is_fp_const(cur))
      {
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            BzlaSymUnpackedFloat(*fp_get_unpacked_float(cur)));
      }
      else if (bzla_node_is_fp_var(cur)
               || (bzla_node_is_apply(cur) && bzla_node_is_fp(d_bzla, cur)))
      {
        BzlaSortId sort   = bzla_node_get_sort_id(cur);
        BzlaSortId sort_1 = bzla_sort_bv(d_bzla, 1);
        BzlaSortId sort_exp =
            bzla_sort_bv(d_bzla, BzlaSymUnpackedFloat::exponentWidth(sort));
        BzlaSortId sort_sig =
            bzla_sort_bv(d_bzla, BzlaSymUnpackedFloat::significandWidth(sort));

        BzlaNode *inf = bzla_exp_var(
            d_bzla, sort_1, create_component_symbol(cur, "inf").c_str());
        BzlaNode *nan = bzla_exp_var(
            d_bzla, sort_1, create_component_symbol(cur, "nan").c_str());
        BzlaNode *sign = bzla_exp_var(
            d_bzla, sort_1, create_component_symbol(cur, "sign").c_str());
        BzlaNode *zero = bzla_exp_var(
            d_bzla, sort_1, create_component_symbol(cur, "zero").c_str());
        BzlaNode *exp = bzla_exp_var(
            d_bzla, sort_exp, create_component_symbol(cur, "exp").c_str());
        BzlaNode *sig = bzla_exp_var(
            d_bzla, sort_sig, create_component_symbol(cur, "sig").c_str());

        BzlaSymUnpackedFloat uf(nan, inf, zero, sign, exp, sig);
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur), uf);
        d_additional_assertions.push_back(
            bzla_node_copy(d_bzla, uf.valid(sort).getNode()));

        bzla_node_release(d_bzla, sig);
        bzla_node_release(d_bzla, exp);
        bzla_node_release(d_bzla, zero);
        bzla_node_release(d_bzla, sign);
        bzla_node_release(d_bzla, nan);
        bzla_node_release(d_bzla, inf);
        bzla_sort_release(d_bzla, sort_sig);
        bzla_sort_release(d_bzla, sort_exp);
        bzla_sort_release(d_bzla, sort_1);
      }
      else if (bzla_node_is_fp_eq(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::smtlibEqual<bzla::fp::BzlaFPSymTraits>(
                               bzla::fp::FloatingPointSortInfo(
                                   bzla_node_get_sort_id(cur->e[0])),
                               d_unpacked_float_map.at(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_rm_eq(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_rm_map.find(cur->e[1]) != d_rm_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           d_rm_map.at(cur->e[0]) == d_rm_map.at(cur->e[1]));
      }
      else if (bzla_node_is_fp_abs(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::absolute<bzla::fp::BzlaFPSymTraits>(
                bzla_node_get_sort_id(cur),
                d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_neg(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::negate<bzla::fp::BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_normal(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isNormal<bzla::fp::BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_subnormal(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isSubnormal<bzla::fp::BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_zero(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isZero<bzla::fp::BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_inf(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isInfinite<bzla::fp::BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_nan(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isNaN<bzla::fp::BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_neg(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isNegative<bzla::fp::BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_pos(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isPositive<bzla::fp::BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_lte(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::lessThanOrEqual<bzla::fp::BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_lt(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::lessThan<bzla::fp::BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_min(cur) || bzla_node_is_fp_max(cur))
      {
        assert(cur->arity == 2);
        BzlaNode *uf = min_max_uf(cur);
        BzlaNode *args[2];
        for (uint32_t i = 0; i < cur->arity; ++i)
        {
          assert(d_unpacked_float_map.find(cur->e[i])
                 != d_unpacked_float_map.end());
          if (d_packed_float_map.find(cur->e[i]) == d_packed_float_map.end())
          {
            d_packed_float_map.emplace(
                cur->e[i],
                symfpu::pack(bzla_node_get_sort_id(cur->e[i]),
                             d_unpacked_float_map.at(cur->e[i])));
          }
          args[i] = d_packed_float_map.at(cur->e[i]).getNode();
        }
        BzlaNode *apply_args = bzla_exp_args(d_bzla, args, cur->arity);
        BzlaNode *apply      = bzla_exp_apply(d_bzla, uf, apply_args);
        if (bzla_node_is_fp_min(cur))
        {
          d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                       symfpu::min<bzla::fp::BzlaFPSymTraits>(
                                           bzla_node_get_sort_id(cur),
                                           d_unpacked_float_map.at(cur->e[0]),
                                           d_unpacked_float_map.at(cur->e[1]),
                                           apply));
        }
        else
        {
          d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                       symfpu::max<bzla::fp::BzlaFPSymTraits>(
                                           bzla_node_get_sort_id(cur),
                                           d_unpacked_float_map.at(cur->e[0]),
                                           d_unpacked_float_map.at(cur->e[1]),
                                           apply));
        }
        bzla_node_release(d_bzla, apply);
        bzla_node_release(d_bzla, apply_args);
      }
      else if (bzla_node_is_fp_rem(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::remainder<bzla::fp::BzlaFPSymTraits>(
                bzla_node_get_sort_id(cur),
                d_unpacked_float_map.at(cur->e[0]),
                d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_sqrt(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::sqrt<bzla::fp::BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_rti(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::roundToIntegral<bzla::fp::BzlaFPSymTraits>(
                bzla_node_get_sort_id(cur),
                d_rm_map.at(cur->e[0]),
                d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_add(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[2])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::add<bzla::fp::BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         d_unpacked_float_map.at(cur->e[1]),
                                         d_unpacked_float_map.at(cur->e[2]),
                                         bzla::fp::BzlaFPSymProp(true)));
      }
      else if (bzla_node_is_fp_mul(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[2])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::multiply<bzla::fp::BzlaFPSymTraits>(
                bzla_node_get_sort_id(cur),
                d_rm_map.at(cur->e[0]),
                d_unpacked_float_map.at(cur->e[1]),
                d_unpacked_float_map.at(cur->e[2])));
      }
      else if (bzla_node_is_fp_div(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[2])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::divide<bzla::fp::BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         d_unpacked_float_map.at(cur->e[1]),
                                         d_unpacked_float_map.at(cur->e[2])));
      }
      else if (bzla_node_is_fp_fma(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[2])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[3])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::fma<bzla::fp::BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         d_unpacked_float_map.at(cur->e[1]),
                                         d_unpacked_float_map.at(cur->e[2]),
                                         d_unpacked_float_map.at(cur->e[3])));
      }
      else if (bzla_node_is_fp_to_sbv(cur) || bzla_node_is_fp_to_ubv(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        uint32_t bw          = bzla_node_bv_get_width(d_bzla, cur);
        BzlaNode *uf         = sbv_ubv_uf(cur);
        BzlaNode *args[2]    = {cur->e[0], cur->e[1]};
        BzlaNode *apply_args = bzla_exp_args(d_bzla, args, cur->arity);
        BzlaNode *apply      = bzla_exp_apply(d_bzla, uf, apply_args);
        if (bzla_node_is_fp_to_sbv(cur))
        {
          d_sbv_map.emplace(
              bzla_node_copy(d_bzla, cur),
              symfpu::convertFloatToSBV<bzla::fp::BzlaFPSymTraits>(
                  bzla_node_get_sort_id(cur->e[1]),
                  d_rm_map.at(cur->e[0]),
                  d_unpacked_float_map.at(cur->e[1]),
                  bw,
                  bzla::fp::BzlaFPSymBV<true>(apply)));
        }
        else
        {
          d_ubv_map.emplace(
              bzla_node_copy(d_bzla, cur),
              symfpu::convertFloatToUBV<bzla::fp::BzlaFPSymTraits>(
                  bzla_node_get_sort_id(cur->e[1]),
                  d_rm_map.at(cur->e[0]),
                  d_unpacked_float_map.at(cur->e[1]),
                  bw,
                  bzla::fp::BzlaFPSymBV<false>(apply)));
        }
        bzla_node_release(d_bzla, apply);
        bzla_node_release(d_bzla, apply_args);
      }
      else if (bzla_node_is_fp_to_fp_from_bv(cur))
      {
        assert(bzla_node_is_bv(d_bzla, cur->e[0]));
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::unpack<bzla::fp::BzlaFPSymTraits>(
                bzla_node_get_sort_id(cur),
                bzla::fp::BzlaFPSymBV<false>(cur->e[0])));
      }
      else if (bzla_node_is_fp_to_fp_from_fp(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::convertFloatToFloat<bzla::fp::BzlaFPSymTraits>(
                bzla_node_get_sort_id(cur->e[1]),
                bzla_node_get_sort_id(cur),
                d_rm_map.at(cur->e[0]),
                d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_to_fp_from_sbv(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(bzla_node_is_bv(d_bzla, cur->e[1]));
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::convertSBVToFloat<bzla::fp::BzlaFPSymTraits>(
                bzla_node_get_sort_id(cur),
                d_rm_map.at(cur->e[0]),
                bzla::fp::BzlaFPSymBV<true>(cur->e[1])));
      }
      else if (bzla_node_is_fp_to_fp_from_ubv(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(bzla_node_is_bv(d_bzla, cur->e[1]));
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::convertUBVToFloat<bzla::fp::BzlaFPSymTraits>(
                bzla_node_get_sort_id(cur),
                d_rm_map.at(cur->e[0]),
                bzla::fp::BzlaFPSymBV<false>(cur->e[1])));
      }
      visited.at(cur) = 1;
    }
    else
    {
      assert(visited.at(cur) == 1);
      continue;
    }
  }

  if (d_prop_map.find(node) != d_prop_map.end())
  {
    assert(bzla_sort_is_bool(d_bzla, bzla_node_get_sort_id(node)));
    res = d_prop_map.at(node).getNode();
  }
  else if (d_rm_map.find(node) != d_rm_map.end())
  {
    assert(bzla_node_is_rm(d_bzla, node));
    res = d_rm_map.at(node).getNode();
  }
  else if (d_sbv_map.find(node) != d_sbv_map.end())
  {
    assert(bzla_node_is_fp_to_sbv(node));
    res = d_sbv_map.at(node).getNode();
  }
  else if (d_ubv_map.find(node) != d_ubv_map.end())
  {
    assert(bzla_node_is_fp_to_ubv(node));
    res = d_ubv_map.at(node).getNode();
  }
  else
  {
    assert(d_unpacked_float_map.find(node) != d_unpacked_float_map.end());
    d_packed_float_map.emplace(node,
                               symfpu::pack(bzla_node_get_sort_id(node),
                                            d_unpacked_float_map.at(node)));
    res = d_packed_float_map.at(node).getNode();
  }
  assert(res);
  return res;
}

BzlaNode *
BzlaFPWordBlaster::get_word_blasted_node(BzlaNode *node)
{
  assert(d_bzla);
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(d_bzla == node->bzla);

  if (d_packed_float_map.find(node) != d_packed_float_map.end())
  {
    return d_packed_float_map.at(node).getNode();
  }

  if (bzla_sort_is_bool(d_bzla, bzla_node_get_sort_id(node))
      && d_prop_map.find(node) != d_prop_map.end())
  {
    return d_prop_map.at(node).getNode();
  }

  if (bzla_node_is_rm(d_bzla, node) && d_rm_map.find(node) != d_rm_map.end())
  {
    return d_rm_map.at(node).getNode();
  }

  if (d_unpacked_float_map.find(node) != d_unpacked_float_map.end())
  {
    d_packed_float_map.emplace(node,
                               symfpu::pack(bzla_node_get_sort_id(node),
                                            d_unpacked_float_map.at(node)));
    return d_packed_float_map.at(node).getNode();
  }

  return word_blast(node);
}

void
BzlaFPWordBlaster::get_introduced_ufs(std::vector<BzlaNode *> &ufs)
{
  for (const auto &p : d_min_max_uf_map)
  {
    ufs.push_back(p.second);
  }
  for (const auto &p : d_sbv_ubv_uf_map)
  {
    ufs.push_back(p.second);
  }
}

void
BzlaFPWordBlaster::add_additional_assertions()
{
  for (BzlaNode *node : d_additional_assertions)
  {
    bzla_assert_exp(d_bzla, node);
    bzla_node_release(d_bzla, node);
  }
  d_additional_assertions.clear();
}

BzlaFPWordBlaster *
BzlaFPWordBlaster::clone(Bzla *cbzla, BzlaNodeMap *exp_map)
{
  BzlaNode *exp, *cexp;
  BzlaFPWordBlaster *res = new BzlaFPWordBlaster(cbzla);

  for (const auto &p : d_min_max_uf_map)
  {
    BzlaSortId s = p.first;
    exp          = p.second;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_min_max_uf_map.find(s) == res->d_min_max_uf_map.end());
    res->d_min_max_uf_map.emplace(s, cexp);
  }
  for (const auto &p : d_sbv_ubv_uf_map)
  {
    exp = p.second;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_sbv_ubv_uf_map.find(p.first) == res->d_sbv_ubv_uf_map.end());
    res->d_sbv_ubv_uf_map.emplace(p.first, cexp);
  }
  for (const auto &p : d_rm_map)
  {
    exp = p.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_rm_map.find(cexp) == res->d_rm_map.end());

    BzlaNode *sexp  = d_rm_map.at(exp).getNode();
    BzlaNode *scexp = bzla_nodemap_mapped(exp_map, sexp);
    assert(scexp);
    res->d_rm_map.emplace(cexp, bzla::fp::BzlaFPSymRM(scexp));
  }
  for (const auto &p : d_prop_map)
  {
    exp = p.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_prop_map.find(cexp) == res->d_prop_map.end());

    BzlaNode *sexp  = d_prop_map.at(exp).getNode();
    BzlaNode *scexp = bzla_nodemap_mapped(exp_map, sexp);
    assert(scexp);
    res->d_prop_map.emplace(cexp, bzla::fp::BzlaFPSymProp(scexp));
  }
  for (const auto &p : d_sbv_map)
  {
    exp = p.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_sbv_map.find(cexp) == res->d_sbv_map.end());

    BzlaNode *sexp  = d_sbv_map.at(exp).getNode();
    BzlaNode *scexp = bzla_nodemap_mapped(exp_map, sexp);
    assert(scexp);
    res->d_sbv_map.emplace(cexp, bzla::fp::BzlaFPSymBV<true>(scexp));
  }
  for (const auto &p : d_ubv_map)
  {
    exp = p.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_ubv_map.find(cexp) == res->d_ubv_map.end());

    BzlaNode *sexp  = d_ubv_map.at(exp).getNode();
    BzlaNode *scexp = bzla_nodemap_mapped(exp_map, sexp);
    assert(scexp);
    res->d_ubv_map.emplace(cexp, bzla::fp::BzlaFPSymBV<false>(scexp));
  }
  for (const auto &p : d_unpacked_float_map)
  {
    exp = p.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_unpacked_float_map.find(cexp)
           == res->d_unpacked_float_map.end());

    BzlaNode *nan = p.second.getNaN().getNode();
    assert(nan);
    BzlaNode *cnan = bzla_nodemap_mapped(exp_map, nan);
    assert(cnan);

    BzlaNode *inf = p.second.getInf().getNode();
    assert(inf);
    BzlaNode *cinf = bzla_nodemap_mapped(exp_map, inf);
    assert(cinf);

    BzlaNode *zero = p.second.getZero().getNode();
    assert(zero);
    BzlaNode *czero = bzla_nodemap_mapped(exp_map, zero);
    assert(czero);

    BzlaNode *sign = p.second.getSign().getNode();
    assert(sign);
    BzlaNode *csign = bzla_nodemap_mapped(exp_map, sign);
    assert(csign);

    BzlaNode *expo = p.second.getExponent().getNode();
    assert(expo);
    BzlaNode *cexpo = bzla_nodemap_mapped(exp_map, expo);
    assert(cexpo);

    BzlaNode *sig = p.second.getSignificand().getNode();
    assert(sig);
    BzlaNode *csig = bzla_nodemap_mapped(exp_map, sig);
    assert(csig);

    res->d_unpacked_float_map.emplace(
        cexp,
        BzlaSymUnpackedFloat(bzla::fp::BzlaFPSymProp(cnan),
                             bzla::fp::BzlaFPSymProp(cinf),
                             bzla::fp::BzlaFPSymProp(czero),
                             bzla::fp::BzlaFPSymProp(csign),
                             bzla::fp::BzlaFPSymBV<true>(cexpo),
                             bzla::fp::BzlaFPSymBV<false>(csig)));
  }
  for (BzlaNode *node : d_additional_assertions)
  {
    BzlaNode *real_node = bzla_node_real_addr(node);
    cexp                = bzla_nodemap_mapped(exp_map, real_node);
    assert(cexp);
    res->d_additional_assertions.push_back(bzla_node_cond_invert(node, cexp));
  }
  return res;
}

BzlaNode *
BzlaFPWordBlaster::min_max_uf(BzlaNode *node)
{
  assert(bzla_node_is_regular(node));

  BzlaSortId sort_fp = bzla_node_get_sort_id(node);

  if (d_min_max_uf_map.find(sort_fp) != d_min_max_uf_map.end())
    return d_min_max_uf_map.at(sort_fp);

  uint32_t arity      = node->arity;
  uint32_t bw         = bzla_sort_fp_get_bv_width(d_bzla, sort_fp);
  BzlaSortId sort_bv1 = bzla_sort_bv(d_bzla, 1);
  BzlaSortId sort_bv  = bzla_sort_bv(d_bzla, bw);
  BzlaSortId sorts[2];
  for (uint32_t i = 0; i < arity; ++i) sorts[i] = sort_bv;
  BzlaSortId sort_domain = bzla_sort_tuple(d_bzla, sorts, arity);
  BzlaSortId sort_fun    = bzla_sort_fun(d_bzla, sort_domain, sort_bv1);
  std::stringstream ss;
  ss << (bzla_node_is_fp_min(node) ? "_fp_min_uf_" : "_fp_max_uf_")
     << bzla_node_get_id(node) << "_";
  d_min_max_uf_map.emplace(bzla_sort_copy(d_bzla, sort_fp),
                           bzla_exp_uf(d_bzla, sort_fun, ss.str().c_str()));
  bzla_sort_release(d_bzla, sort_fun);
  bzla_sort_release(d_bzla, sort_domain);
  bzla_sort_release(d_bzla, sort_bv);
  bzla_sort_release(d_bzla, sort_bv1);
  return d_min_max_uf_map.at(sort_fp);
}

BzlaNode *
BzlaFPWordBlaster::sbv_ubv_uf(BzlaNode *node)
{
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_rm(d_bzla, node->e[0]));
  assert(bzla_node_is_fp(d_bzla, node->e[1]));

  BzlaSortId sort_bv = bzla_node_get_sort_id(node);
  BzlaSortId sort_fp = bzla_node_get_sort_id(node->e[1]);
  std::pair<BzlaSortId, BzlaSortId> p(sort_fp, sort_bv);

  if (d_sbv_ubv_uf_map.find(p) != d_sbv_ubv_uf_map.end())
    return d_sbv_ubv_uf_map.at(p);

  BzlaSortId sorts[2]    = {bzla_node_get_sort_id(node->e[0]), sort_fp};
  BzlaSortId sort_domain = bzla_sort_tuple(d_bzla, sorts, 2);
  BzlaSortId sort_fun    = bzla_sort_fun(d_bzla, sort_domain, sort_bv);

  std::stringstream ss;
  ss << (bzla_node_is_fp_to_sbv(node) ? "_fp_sbv_uf_" : "_fp_ubv_uf_")
     << bzla_node_get_id(node) << "_";
  (void) bzla_sort_copy(d_bzla, sort_fp);
  (void) bzla_sort_copy(d_bzla, sort_bv);
  d_sbv_ubv_uf_map.emplace(p, bzla_exp_uf(d_bzla, sort_fun, ss.str().c_str()));
  bzla_sort_release(d_bzla, sort_fun);
  bzla_sort_release(d_bzla, sort_domain);
  return d_sbv_ubv_uf_map.at(p);
}

/* ========================================================================== */

void
bzla_fp_free(Bzla *bzla, BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);
  BzlaFPWordBlaster::set_s_bzla(bzla);
  fp->d_fp.reset(nullptr);
  BZLA_DELETE(bzla->mm, fp);
}

BzlaFloatingPoint *
bzla_fp_copy(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;

  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(*fp->d_fp));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp->d_fp->as_bv();
}

void
bzla_fp_ieee_bv_as_bvs(Bzla *bzla,
                       const BzlaBitVector *bv,
                       BzlaSortId fp_sort,
                       BzlaBitVector **sign,
                       BzlaBitVector **exp,
                       BzlaBitVector **sig)
{
  uint32_t bw     = bzla_bv_get_width(bv);
  uint32_t bw_exp = bzla_sort_fp_get_exp_width(bzla, fp_sort);
  uint32_t bw_sig = bzla_sort_fp_get_sig_width(bzla, fp_sort);
  *sign           = bzla_bv_slice(bzla->mm, bv, bw - 1, bw - 1);
  *exp            = bzla_bv_slice(bzla->mm, bv, bw - 2, bw - 1 - bw_exp);
  *sig            = bzla_bv_slice(bzla->mm, bv, bw_sig - 2, 0);
}

void
bzla_fp_as_bvs(Bzla *bzla,
               BzlaFloatingPoint *fp,
               BzlaBitVector **sign,
               BzlaBitVector **exp,
               BzlaBitVector **sig)
{
  assert(bzla);
  assert(fp);
  assert(sign);
  assert(exp);
  assert(sig);

  BzlaFPWordBlaster::set_s_bzla(bzla);
  fp->d_fp->as_bvs(sign, exp, sig);
}

BzlaFloatingPoint *
bzla_fp_get_fp(BzlaNode *node)
{
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_fp_const(node));
  return static_cast<BzlaFloatingPoint *>(((BzlaFPConstNode *) node)->fp);
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp->d_fp->is_zero();
}

bool
bzla_fp_is_normal(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp->d_fp->is_normal();
}

bool
bzla_fp_is_subnormal(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp->d_fp->is_subnormal();
}

bool
bzla_fp_is_nan(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp->d_fp->is_nan();
}

bool
bzla_fp_is_inf(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp->d_fp->is_inf();
}

bool
bzla_fp_is_neg(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp->d_fp->is_neg();
}

bool
bzla_fp_is_pos(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp->d_fp->is_pos();
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

  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp0->d_fp->is_eq(*fp1->d_fp);
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

  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp0->d_fp->is_lt(*fp1->d_fp);
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

  BzlaFPWordBlaster::set_s_bzla(bzla);
  return fp0->d_fp->is_le(*fp1->d_fp);
}

BzlaFloatingPoint *
bzla_fp_zero(Bzla *bzla, BzlaSortId sort, bool sign)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaFloatingPoint *res;
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::fp::FloatingPoint(bzla::fp::FloatingPoint::fpzero(sort, sign)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_inf(Bzla *bzla, BzlaSortId sort, bool sign)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaFloatingPoint *res;
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::fp::FloatingPoint(bzla::fp::FloatingPoint::fpinf(sort, sign)));
  return res;
}

BzlaFloatingPoint *
bzla_fp_nan(Bzla *bzla, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaFloatingPoint *res;
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::fp::FloatingPoint(bzla::fp::FloatingPoint::fpnan(sort)));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(
      bzla::fp::FloatingPoint::fpfp(sign, exp, sig)));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(sort, bv_const));
  return res;
}

BzlaFloatingPoint *
bzla_fp_abs(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(fp->d_fp->fpabs()));
  return res;
}

BzlaFloatingPoint *
bzla_fp_neg(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(fp->d_fp->fpneg()));
  return res;
}

BzlaFloatingPoint *
bzla_fp_sqrt(Bzla *bzla, const BzlaRoundingMode rm, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::fp::FloatingPoint(fp->d_fp->fpsqrt(bzlarm2rm.at(rm))));
  return res;
}

BzlaFloatingPoint *
bzla_fp_rti(Bzla *bzla, const BzlaRoundingMode rm, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::fp::FloatingPoint(fp->d_fp->fprti(bzlarm2rm.at(rm))));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(fp0->d_fp->fprem(*fp1->d_fp)));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(
      fp0->d_fp->fpadd(bzlarm2rm.at(rm), *fp1->d_fp)));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(
      fp0->d_fp->fpmul(bzlarm2rm.at(rm), *fp1->d_fp)));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(
      fp0->d_fp->fpdiv(bzlarm2rm.at(rm), *fp1->d_fp)));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::fp::FloatingPoint(sort, bzlarm2rm.at(rm), *fp->d_fp));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::fp::FloatingPoint(sort, bzlarm2rm.at(rm), bv, false));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::fp::FloatingPoint(sort, bzlarm2rm.at(rm), bv, true));
  return res;
}

BzlaFloatingPoint *
bzla_fp_convert_from_real(Bzla *bzla,
                          BzlaSortId sort,
                          const BzlaRoundingMode rm,
                          const char *real)
{
  BzlaFloatingPoint *res;
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(new bzla::fp::FloatingPoint(
      bzla::fp::FloatingPoint::from_real(sort, bzlarm2rm.at(rm), real)));
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
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->d_fp.reset(
      new bzla::fp::FloatingPoint(bzla::fp::FloatingPoint::from_rational(
          sort, bzlarm2rm.at(rm), num, den)));
  return res;
}

void
bzla_fp_word_blaster_get_introduced_ufs(Bzla *bzla, BzlaNodePtrStack *ufs)
{
  assert(bzla);
  if (!bzla->word_blaster) return;
  BzlaFPWordBlaster *word_blaster =
      static_cast<BzlaFPWordBlaster *>(bzla->word_blaster);

  std::vector<BzlaNode *> introduced_ufs;
  word_blaster->get_introduced_ufs(introduced_ufs);
  for (BzlaNode *uf : introduced_ufs)
  {
    BZLA_PUSH_STACK(*ufs, uf);
  }
}

/* ========================================================================== */

void *
bzla_fp_word_blaster_new(Bzla *bzla)
{
  return new BzlaFPWordBlaster(bzla);
}

void *
bzla_fp_word_blaster_clone(Bzla *bzla, Bzla *clone, BzlaNodeMap *exp_map)
{
  assert(bzla);
  assert(bzla->word_blaster);
  assert(clone);
  assert(exp_map);
  BzlaFPWordBlaster::set_s_bzla(clone);
  return static_cast<BzlaFPWordBlaster *>(bzla->word_blaster)
      ->clone(clone, exp_map);
}

void
bzla_fp_word_blaster_delete(Bzla *bzla)
{
  assert(bzla);
  if (!bzla->word_blaster) return;
  BzlaFPWordBlaster *wb = static_cast<BzlaFPWordBlaster *>(bzla->word_blaster);
  BzlaFPWordBlaster::set_s_bzla(wb->get_bzla());
  delete wb;
  bzla->word_blaster = nullptr;
}

void
bzla_fp_word_blaster_add_additional_assertions(Bzla *bzla)
{
  assert(bzla);
  if (!bzla->word_blaster) return;
  BzlaFPWordBlaster *word_blaster =
      static_cast<BzlaFPWordBlaster *>(bzla->word_blaster);
  word_blaster->add_additional_assertions();
}

BzlaNode *
bzla_fp_word_blast(Bzla *bzla, BzlaNode *node)
{
  assert(bzla);
  assert(bzla->word_blaster);
  assert(node);
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BzlaNode *res = static_cast<BzlaFPWordBlaster *>(bzla->word_blaster)
                      ->get_word_blasted_node(node);
  return bzla_simplify_exp(bzla, res);
}

/* -------------------------------------------------------------------------- */
