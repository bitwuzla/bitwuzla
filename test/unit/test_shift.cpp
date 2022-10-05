/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include <bitset>

#include "test.h"

extern "C" {
#include "bzlabv.h"
#include "utils/bzlautil.h"
}

class TestShift : public TestCommon
{
 protected:
  void test_shift(uint32_t bw,
                  const char *shift,
                  BitwuzlaKind kind_shift,
                  BitwuzlaKind kind)
  {
    assert(bw > 1);
    assert(bw == strlen(shift));

    int32_t res;
    uint32_t ushift;
    const BitwuzlaSort *sort;
    const BitwuzlaTerm *res_shift0, *shift0;
    const BitwuzlaTerm *res_shift1;
    const BitwuzlaTerm *e0, *ne0;
    const BitwuzlaTerm *two;

    Bitwuzla *bitwuzla = bitwuzla_new();
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_RW_LEVEL, 0);
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);

    sort   = bitwuzla_mk_bv_sort(bitwuzla, bw);
    e0     = bitwuzla_mk_const(bitwuzla, sort, "e0");
    ushift = std::stol(shift, nullptr, 2);

    shift0 = bitwuzla_mk_bv_value(bitwuzla, sort, shift, BITWUZLA_BV_BASE_BIN);
    res_shift0 = bitwuzla_mk_term2(bitwuzla, kind_shift, e0, shift0);

    res_shift1 = e0;
    two        = bitwuzla_mk_bv_value_uint64(bitwuzla, sort, 2u);
    for (uint32_t i = 0; i < ushift; ++i)
    {
      res_shift1 = bitwuzla_mk_term2(bitwuzla, kind, res_shift1, two);
    }
    if (kind_shift == BITWUZLA_KIND_BV_ASHR)
    {
      /* if msb = 1, shift in 1 bits instead of 0 bits */
      if (ushift > 0)
      {
        const BitwuzlaTerm *msb = bitwuzla_mk_term1_indexed2(
            bitwuzla, BITWUZLA_KIND_BV_EXTRACT, e0, bw - 1, bw - 1);
        if (ushift < bw)
        {
          const BitwuzlaTerm *slice =
              bitwuzla_mk_term1_indexed2(bitwuzla,
                                         BITWUZLA_KIND_BV_EXTRACT,
                                         res_shift1,
                                         bw - ushift - 1,
                                         0);
          const BitwuzlaSort *sort_sra_ones =
              bitwuzla_mk_bv_sort(bitwuzla, ushift);
          const BitwuzlaTerm *ones =
              bitwuzla_mk_bv_ones(bitwuzla, sort_sra_ones);
          const BitwuzlaTerm *concat =
              bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_CONCAT, ones, slice);
          res_shift1 = bitwuzla_mk_term3(
              bitwuzla, BITWUZLA_KIND_ITE, msb, concat, res_shift1);
        }
        else
        {
          res_shift1 = bitwuzla_mk_term3(bitwuzla,
                                         BITWUZLA_KIND_ITE,
                                         msb,
                                         bitwuzla_mk_bv_ones(bitwuzla, sort),
                                         res_shift1);
        }
      }
    }

    ne0 = bitwuzla_mk_term2(
        bitwuzla, BITWUZLA_KIND_DISTINCT, res_shift0, res_shift1);
    bitwuzla_assert(bitwuzla, ne0);

    res = bitwuzla_check_sat(bitwuzla);
    if (res == BITWUZLA_SAT)
    {
      const BitwuzlaTerm *val_e0 = bitwuzla_get_value(bitwuzla, e0);
      const BitwuzlaTerm *val_res_shift0 =
          bitwuzla_get_value(bitwuzla, res_shift0);
      const BitwuzlaTerm *val_shift0 = bitwuzla_get_value(bitwuzla, shift0);
      const BitwuzlaTerm *val_res_shift1 =
          bitwuzla_get_value(bitwuzla, res_shift1);

      bitwuzla_term_dump(val_e0, "btor", stdout);
      bitwuzla_term_dump(val_res_shift0, "btor", stdout);
      bitwuzla_term_dump(val_shift0, "btor", stdout);
      bitwuzla_term_dump(val_res_shift1, "btor", stdout);
    }
    assert(res == BITWUZLA_UNSAT);

    bitwuzla_delete(bitwuzla);
  }
};

TEST_F(TestShift, sll_2)
{
  for (uint32_t i = 0; i < (1u << 2); ++i)
  {
    test_shift(2,
               std::bitset<2>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_SHL,
               BITWUZLA_KIND_BV_MUL);
  }
}

TEST_F(TestShift, sll_3)
{
  for (uint32_t i = 0; i < (1u << 3); ++i)
  {
    test_shift(3,
               std::bitset<3>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_SHL,
               BITWUZLA_KIND_BV_MUL);
  }
}

TEST_F(TestShift, sll_4)
{
  for (uint32_t i = 0; i < (1u << 4); ++i)
  {
    test_shift(4,
               std::bitset<4>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_SHL,
               BITWUZLA_KIND_BV_MUL);
  }
}

TEST_F(TestShift, sll_5)
{
  for (uint32_t i = 0; i < (1u << 5); ++i)
  {
    test_shift(5,
               std::bitset<5>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_SHL,
               BITWUZLA_KIND_BV_MUL);
  }
}

TEST_F(TestShift, sll_8)
{
  for (uint32_t i = 0; i < (1u << 8); ++i)
  {
    test_shift(8,
               std::bitset<8>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_SHL,
               BITWUZLA_KIND_BV_MUL);
  }
}

TEST_F(TestShift, srl_2)
{
  for (uint32_t i = 0; i < (1u << 2); ++i)
  {
    test_shift(2,
               std::bitset<2>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_SHR,
               BITWUZLA_KIND_BV_UDIV);
  }
}

TEST_F(TestShift, srl_3)
{
  for (uint32_t i = 0; i < (1u << 3); ++i)
  {
    test_shift(3,
               std::bitset<3>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_SHR,
               BITWUZLA_KIND_BV_UDIV);
  }
}

TEST_F(TestShift, srl_4)
{
  for (uint32_t i = 0; i < (1u << 4); ++i)
  {
    test_shift(4,
               std::bitset<4>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_SHR,
               BITWUZLA_KIND_BV_UDIV);
  }
}

TEST_F(TestShift, srl_5)
{
  for (uint32_t i = 0; i < (1u << 5); ++i)
  {
    test_shift(5,
               std::bitset<5>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_SHR,
               BITWUZLA_KIND_BV_UDIV);
  }
}

TEST_F(TestShift, srl_8)
{
  for (uint32_t i = 0; i < (1u << 8); ++i)
  {
    test_shift(8,
               std::bitset<8>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_SHR,
               BITWUZLA_KIND_BV_UDIV);
  }
}

TEST_F(TestShift, sra_2)
{
  for (uint32_t i = 0; i < (1u << 2); ++i)
  {
    test_shift(2,
               std::bitset<2>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_ASHR,
               BITWUZLA_KIND_BV_UDIV);
  }
}

TEST_F(TestShift, sra_3)
{
  for (uint32_t i = 0; i < (1u << 3); ++i)
  {
    test_shift(3,
               std::bitset<3>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_ASHR,
               BITWUZLA_KIND_BV_UDIV);
  }
}

TEST_F(TestShift, sra_4)
{
  for (uint32_t i = 0; i < (1u << 4); ++i)
  {
    test_shift(4,
               std::bitset<4>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_ASHR,
               BITWUZLA_KIND_BV_UDIV);
  }
}

TEST_F(TestShift, sra_5)
{
  for (uint32_t i = 0; i < (1u << 5); ++i)
  {
    test_shift(5,
               std::bitset<5>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_ASHR,
               BITWUZLA_KIND_BV_UDIV);
  }
}

TEST_F(TestShift, sra_8)
{
  for (uint32_t i = 0; i < (1u << 8); ++i)
  {
    test_shift(8,
               std::bitset<8>(i).to_string().c_str(),
               BITWUZLA_KIND_BV_ASHR,
               BITWUZLA_KIND_BV_UDIV);
  }
}
