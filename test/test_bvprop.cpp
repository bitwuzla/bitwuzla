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
#include "bzlaaigvec.h"
#include "bzlabvprop.h"
#include "utils/bzlamem.h"
#include "utils/bzlautil.h"
}

#define TEST_BVPROP_THREE_BITS 0

#define TEST_BVPROP_RELEASE_D_XZ   \
  do                               \
  {                                \
    bzla_bvdomain_free(d_mm, d_x); \
    bzla_bvdomain_free(d_mm, d_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_RES_XZ   \
  do                                 \
  {                                  \
    bzla_bvdomain_free(d_mm, res_x); \
    bzla_bvdomain_free(d_mm, res_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_D_XYZ  \
  do                               \
  {                                \
    bzla_bvdomain_free(d_mm, d_x); \
    bzla_bvdomain_free(d_mm, d_y); \
    bzla_bvdomain_free(d_mm, d_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_RES_XYZ  \
  do                                 \
  {                                  \
    bzla_bvdomain_free(d_mm, res_x); \
    bzla_bvdomain_free(d_mm, res_y); \
    bzla_bvdomain_free(d_mm, res_z); \
  } while (0)

class TestBvProp : public TestBvDomainCommon
{
 protected:
  enum BvPropOp
  {
    TEST_BVPROP_ADD,
    TEST_BVPROP_AND,
    TEST_BVPROP_CONCAT,
    TEST_BVPROP_EQ,
    TEST_BVPROP_COND,
    TEST_BVPROP_MUL,
    TEST_BVPROP_OR,
    TEST_BVPROP_SLICE,
    TEST_BVPROP_SLL,
    TEST_BVPROP_SRL,
    TEST_BVPROP_UDIV,
    TEST_BVPROP_ULT,
    TEST_BVPROP_UREM,
    TEST_BVPROP_XOR
  };

  void SetUp() override
  {
    TestBvDomainCommon::SetUp();
    d_bzla  = bzla_new();
    d_avmgr = bzla_aigvec_mgr_new(d_bzla);
  }

  void TearDown() override
  {
    bzla_aigvec_mgr_delete(d_avmgr);
    bzla_delete(d_bzla);
    TestBvDomainCommon::TearDown();
  }

  BzlaAIGVec *aigvec_from_domain(BzlaBvDomain *d)
  {
    char *str_d = from_domain(d_mm, d);
    size_t len  = strlen(str_d);

    BzlaAIGVec *res = bzla_aigvec_var(d_avmgr, len);

    for (size_t i = 0; i < len; i++)
    {
      if (str_d[i] == '0')
      {
        bzla_aig_release(d_avmgr->amgr, res->aigs[i]);
        res->aigs[i] = BZLA_AIG_FALSE;
      }
      else if (str_d[i] == '1')
      {
        bzla_aig_release(d_avmgr->amgr, res->aigs[i]);
        res->aigs[i] = BZLA_AIG_TRUE;
      }
    }
    bzla_mem_freestr(d_mm, str_d);
    return res;
  }

  void print_aigvec(BzlaAIGVec *av)
  {
    for (size_t i = 0; i < av->width; i++)
    {
      if (av->aigs[i] == BZLA_AIG_FALSE)
      {
        printf("0");
      }
      else if (av->aigs[i] == BZLA_AIG_TRUE)
      {
        printf("1");
      }
      else
      {
        printf("x");
      }
    }
  }

  BzlaAIGVec *aigvec_or(BzlaAIGVec *a, BzlaAIGVec *b)
  {
    BzlaAIGVec *not_a, *not_b, *_and, *result;
    not_a  = bzla_aigvec_not(d_avmgr, a);
    not_b  = bzla_aigvec_not(d_avmgr, b);
    _and   = bzla_aigvec_and(d_avmgr, not_a, not_b);
    result = bzla_aigvec_not(d_avmgr, _and);
    bzla_aigvec_release_delete(d_avmgr, not_a);
    bzla_aigvec_release_delete(d_avmgr, not_b);
    bzla_aigvec_release_delete(d_avmgr, _and);
    return result;
  }

  BzlaAIGVec *aigvec_xor(BzlaAIGVec *a, BzlaAIGVec *b)
  {
    BzlaAIGVec *_or, *_and, *not_and, *result;
    _or     = aigvec_or(a, b);
    _and    = bzla_aigvec_and(d_avmgr, a, b);
    not_and = bzla_aigvec_not(d_avmgr, _and);
    result  = bzla_aigvec_and(d_avmgr, _or, not_and);
    bzla_aigvec_release_delete(d_avmgr, _or);
    bzla_aigvec_release_delete(d_avmgr, _and);
    bzla_aigvec_release_delete(d_avmgr, not_and);
    return result;
  }

  char *slice_str_const(char *str_const, uint32_t from, uint32_t to)
  {
    char *res;
    uint32_t len = to - from + 1;

    BZLA_CNEWN(d_mm, res, len + 1);
    strncpy(res, str_const + from, len);
    return res;
  }

#if 0
  bool is_false_eq (const char *a, const char *b)
  {
    assert (strlen (a) == strlen (b));
    size_t len = strlen (a);
    for (size_t i = 0; i < len; i++)
    {
      if (a[i] == 'x' || b[i] == 'x')
      {
        continue;
      }
      if (a[i] != b[i])
      {
        return true;
      }
    }
    return false;
  }

  bool is_true_eq (const char *a, const char *b)
  {
    assert (strlen (a) == strlen (b));
    size_t len = strlen (a);
    for (size_t i = 0; i < len; i++)
    {
      if (a[i] == 'x' && b[i] == 'x')
      {
        return false;
      }
      if (a[i] != 'x' && b[i] != 'x')
      {
        if (a[i] != b[i])
        {
          return false;
        }
      }
    }
    return true;
  }
#endif

  void check_not(BzlaBvDomain *d_x, BzlaBvDomain *d_z)
  {
    assert(bzla_bvdomain_is_valid(d_mm, d_x));
    assert(bzla_bvdomain_is_valid(d_mm, d_z));

    char *str_x = from_domain(d_mm, d_x);
    char *str_z = from_domain(d_mm, d_z);
    ASSERT_EQ(strlen(str_x), strlen(str_z));

    size_t len = strlen(str_x);
    for (size_t i = 0; i < len; i++)
    {
      ASSERT_TRUE(str_x[i] != 'x' || str_z[i] == 'x');
      ASSERT_TRUE(str_x[i] != '0' || str_z[i] == '1');
      ASSERT_TRUE(str_x[i] != '1' || str_z[i] == '0');
      ASSERT_TRUE(str_z[i] != '0' || str_x[i] == '1');
      ASSERT_TRUE(str_z[i] != '1' || str_x[i] == '0');
    }
    bzla_mem_freestr(d_mm, str_x);
    bzla_mem_freestr(d_mm, str_z);
  }

  void check_sll_const(BzlaBvDomain *d_x, BzlaBvDomain *d_z, uint32_t n)
  {
    assert(bzla_bvdomain_is_valid(d_mm, d_x));
    assert(bzla_bvdomain_is_valid(d_mm, d_z));

    char *str_x = from_domain(d_mm, d_x);
    char *str_z = from_domain(d_mm, d_z);
    ASSERT_EQ(strlen(str_x), strlen(str_z));

    for (size_t i = 0, len = strlen(str_x); i < len; i++)
    {
      ASSERT_TRUE(i >= n || str_z[len - 1 - i] == '0');
      ASSERT_TRUE(i < n || str_z[len - 1 - i] == str_x[len - 1 - i + n]);
    }
    bzla_mem_freestr(d_mm, str_x);
    bzla_mem_freestr(d_mm, str_z);
  }

  void check_srl_const(BzlaBvDomain *d_x, BzlaBvDomain *d_z, uint32_t n)
  {
    assert(bzla_bvdomain_is_valid(d_mm, d_x));
    assert(bzla_bvdomain_is_valid(d_mm, d_z));

    char *str_x = from_domain(d_mm, d_x);
    char *str_z = from_domain(d_mm, d_z);
    ASSERT_EQ(strlen(str_x), strlen(str_z));

    for (size_t i = 0, len = strlen(str_x); i < len; i++)
    {
      ASSERT_TRUE(i >= n || str_z[i] == '0');
      ASSERT_TRUE(i < n || str_z[i] == str_x[i - n]);
    }
    bzla_mem_freestr(d_mm, str_x);
    bzla_mem_freestr(d_mm, str_z);
  }

  void check_concat(BzlaBvDomain *d_x, BzlaBvDomain *d_y, BzlaBvDomain *d_z)
  {
    bool res;
    BzlaBvDomain *res_x, *res_y, *res_z;

    res = bzla_bvprop_concat(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
    ASSERT_TRUE(res || !is_valid(d_mm, res_x, res_y, res_z, 0));
    check_sat(d_x,
              d_y,
              d_z,
              0,
              res_x,
              res_y,
              res_z,
              0,
              2,
              false,
              BITWUZLA_KIND_BV_CONCAT,
              0,
              0,
              res);
    ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_x)
                || !bzla_bv_compare(d_x->lo, res_x->lo));
    ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_y)
                || !bzla_bv_compare(d_y->lo, res_y->lo));
    ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_z)
                || !bzla_bv_compare(d_z->lo, res_z->lo));
    check_concat_result(res_x, res_y, res_z);
    ASSERT_TRUE(bzla_bvdomain_is_valid(d_mm, res_x));
    ASSERT_TRUE(bzla_bvdomain_is_valid(d_mm, res_y));
    ASSERT_TRUE(bzla_bvdomain_is_valid(d_mm, res_z));
    ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_x)
                || bzla_bvdomain_is_fixed(d_mm, res_x));
    ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_y)
                || bzla_bvdomain_is_fixed(d_mm, res_y));
    ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_z)
                || (bzla_bvdomain_is_fixed(d_mm, res_x)
                    && bzla_bvdomain_is_fixed(d_mm, res_y)
                    && bzla_bvdomain_is_fixed(d_mm, res_z)));
    TEST_BVPROP_RELEASE_RES_XYZ;
  }

  void check_sext(BzlaBvDomain *d_x, BzlaBvDomain *d_z)
  {
    if (bzla_bvdomain_is_valid(d_mm, d_x) && bzla_bvdomain_is_valid(d_mm, d_z))
    {
      size_t i, len_x, len_z, n;
      char *str_x = from_domain(d_mm, d_x);
      char *str_z = from_domain(d_mm, d_z);

      len_x = strlen(str_x);
      len_z = strlen(str_z);
      n     = len_z - len_x;

      for (i = 0; i < n; i++)
      {
        ASSERT_EQ(str_z[i], str_x[0]);
      }
      for (i = 0; i < len_x; i++)
      {
        ASSERT_EQ(str_z[i + n], str_x[i]);
      }

      bzla_mem_freestr(d_mm, str_x);
      bzla_mem_freestr(d_mm, str_z);
    }
  }

  void check_cond(BzlaBvDomain *d_x,
                  BzlaBvDomain *d_y,
                  BzlaBvDomain *d_z,
                  BzlaBvDomain *d_c)
  {
    assert(bzla_bvdomain_get_width(d_c) == 1);
    assert(bzla_bvdomain_is_valid(d_mm, d_x));
    assert(bzla_bvdomain_is_valid(d_mm, d_y));
    assert(bzla_bvdomain_is_valid(d_mm, d_z));
    assert(bzla_bvdomain_is_valid(d_mm, d_c));

    char *str_x = from_domain(d_mm, d_x);
    char *str_y = from_domain(d_mm, d_y);
    char *str_z = from_domain(d_mm, d_z);
    char *str_c = from_domain(d_mm, d_c);

    if (str_c[0] == '0')
    {
      ASSERT_EQ(strcmp(str_z, str_y), 0);
    }
    else if (str_c[0] == '1')
    {
      ASSERT_EQ(strcmp(str_z, str_x), 0);
    }
    else
    {
      size_t len = strlen(str_x);
      ASSERT_EQ(len, strlen(str_y));
      ASSERT_EQ(len, strlen(str_z));

      if (strcmp(str_z, str_x) && strcmp(str_z, str_y))
      {
        for (size_t i = 0; i < len; i++)
        {
          ASSERT_TRUE(
              (str_z[i] == str_x[i] || str_z[i] == 'x' || str_x[i] == 'x')
              && (str_z[i] == str_y[i] || str_z[i] == 'x' || str_y[i] == 'x'));
        }
      }
    }

    bzla_mem_freestr(d_mm, str_x);
    bzla_mem_freestr(d_mm, str_y);
    bzla_mem_freestr(d_mm, str_z);
    bzla_mem_freestr(d_mm, str_c);
  }

  void check_synth(BzlaBvDomain *d_x,
                   BzlaBvDomain *d_y,
                   BzlaBvDomain *d_z,
                   BzlaBvDomain *d_c,
                   BzlaBvDomain *res_z,
                   BvPropOp op,
                   uint32_t upper,
                   uint32_t lower,
                   bool expect_fail = false)
  {
    BzlaAIGVec *av_x = 0, *av_y = 0, *av_c = 0, *av_res = 0;
    char *str_res_z;

    if (bzla_bvdomain_has_fixed_bits(d_mm, d_z))
    {
      return;
    }

    str_res_z = from_domain(d_mm, res_z);
    if (d_x)
    {
      av_x = aigvec_from_domain(d_x);
    }
    if (d_y)
    {
      av_y = aigvec_from_domain(d_y);
    }
    if (d_c)
    {
      av_c = aigvec_from_domain(d_c);
    }

    switch (op)
    {
      case TEST_BVPROP_SLICE:
        av_res = bzla_aigvec_slice(d_avmgr, av_x, upper, lower);
        break;

      case TEST_BVPROP_AND:
        av_res = bzla_aigvec_and(d_avmgr, av_x, av_y);
        break;

      case TEST_BVPROP_OR: av_res = aigvec_or(av_x, av_y); break;

      case TEST_BVPROP_XOR: av_res = aigvec_xor(av_x, av_y); break;

      case TEST_BVPROP_EQ: av_res = bzla_aigvec_eq(d_avmgr, av_x, av_y); break;

      case TEST_BVPROP_ADD:
        av_res = bzla_aigvec_add(d_avmgr, av_x, av_y);
        break;

      case TEST_BVPROP_MUL:
        av_res = bzla_aigvec_mul(d_avmgr, av_x, av_y);
        break;

      case TEST_BVPROP_ULT:
        av_res = bzla_aigvec_ult(d_avmgr, av_x, av_y);
        break;

      case TEST_BVPROP_SLL:
        av_res = bzla_aigvec_sll(d_avmgr, av_x, av_y);
        break;

      case TEST_BVPROP_SRL:
        av_res = bzla_aigvec_srl(d_avmgr, av_x, av_y);
        break;

      case TEST_BVPROP_UDIV:
        av_res = bzla_aigvec_udiv(d_avmgr, av_x, av_y);
        break;

      case TEST_BVPROP_UREM:
        av_res = bzla_aigvec_urem(d_avmgr, av_x, av_y);
        break;

      case TEST_BVPROP_CONCAT:
        av_res = bzla_aigvec_concat(d_avmgr, av_x, av_y);
        break;

      default:
        assert(op == TEST_BVPROP_COND);
        av_res = bzla_aigvec_cond(d_avmgr, av_c, av_x, av_y);
    }

    if (av_x)
    {
      bzla_aigvec_release_delete(d_avmgr, av_x);
    }
    if (av_y)
    {
      bzla_aigvec_release_delete(d_avmgr, av_y);
    }
    if (av_c)
    {
      bzla_aigvec_release_delete(d_avmgr, av_c);
    }

    bool result = true;
    for (size_t i = 0; i < av_res->width; i++)
    {
      if (bzla_aig_is_const(av_res->aigs[i]) && str_res_z[i] == 'x')
      {
        result = false;
        break;
      }
    }

    if (expect_fail)
    {
      if (result)
      {
        printf("\n");
        if (d_x)
        {
          printf("x: ");
          print_domain(d_x, true);
        }
        if (d_y)
        {
          printf("y: ");
          print_domain(d_y, true);
        }
        if (d_z)
        {
          printf("z: ");
          print_domain(d_z, true);
        }
        if (d_c)
        {
          printf("c: ");
          print_domain(d_c, true);
        }
        printf("prop result: ");
        print_domain(res_z, true);
        printf("AIG result : ");
        print_aigvec(av_res);
        printf("\n");
      }

      ASSERT_FALSE(result);
      goto DONE;
    }

    if (!result)
    {
      printf("\n");
      if (d_x)
      {
        printf("x: ");
        print_domain(d_x, true);
      }
      if (d_y)
      {
        printf("y: ");
        print_domain(d_y, true);
      }
      if (d_z)
      {
        printf("z: ");
        print_domain(d_z, true);
      }
      if (d_c)
      {
        printf("c: ");
        print_domain(d_c, true);
      }
      printf("prop result: ");
      print_domain(res_z, true);
      printf("AIG result : ");
      print_aigvec(av_res);
      printf("\n");
    }
    ASSERT_TRUE(result);

  DONE:
    bzla_aigvec_release_delete(d_avmgr, av_res);
    bzla_mem_freestr(d_mm, str_res_z);
  }

  /**
   * Assert that fixed bits in the given result domain do not match in any
   * satisfying assignment for var, i.e.,
   *   (var | d->lo) != var || (var & d->hi) != var.
   * This is a helper for the check_sat test below.
   */
  void fix_result_bits_for_check_sat(Bitwuzla *bitwuzla,
                                     const BitwuzlaTerm *var,
                                     BzlaBvDomain *d)
  {
    assert(bitwuzla);
    assert(var);
    assert(d);
    assert(bzla_bvdomain_is_valid(d_mm, d));

    const BitwuzlaTerm *d_hi, *d_lo, *a, *o, *_or, *ne1, *ne2;
    const BitwuzlaSort *sort;
    char *s_hi, *s_lo;

    sort = bitwuzla_mk_bv_sort(bitwuzla, bzla_bvdomain_get_width(d));
    s_hi = bzla_bv_to_char(d_mm, d->hi);
    s_lo = bzla_bv_to_char(d_mm, d->lo);

    d_hi = bitwuzla_mk_bv_value(bitwuzla, sort, s_hi, BITWUZLA_BV_BASE_BIN);
    d_lo = bitwuzla_mk_bv_value(bitwuzla, sort, s_lo, BITWUZLA_BV_BASE_BIN);

    a = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_AND, var, d_hi);
    o = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_OR, var, d_lo);

    ne1 = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_DISTINCT, a, var);
    ne2 = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_DISTINCT, o, var);

    _or = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_OR, ne1, ne2);

    bitwuzla_assert(bitwuzla, _or);

    bzla_mem_freestr(d_mm, s_hi);
    bzla_mem_freestr(d_mm, s_lo);
  }

  /**
   * Fix bits in var corresponding to the fixed bits in the given input domain.
   * This is a helper for the check_sat test below.
   */
  void fix_domain_bits_for_check_sat(Bitwuzla *bitwuzla,
                                     const BitwuzlaTerm *var,
                                     BzlaBvDomain *d)
  {
    assert(bitwuzla);
    assert(var);
    assert(d);
    assert(bzla_bvdomain_is_valid(d_mm, d));

    const BitwuzlaTerm *d_hi, *d_lo, *a, *o, *_and, *eq1, *eq2;
    const BitwuzlaSort *sort;
    char *s_hi, *s_lo;

    sort = bitwuzla_mk_bv_sort(bitwuzla, bzla_bvdomain_get_width(d));
    s_hi = bzla_bv_to_char(d_mm, d->hi);
    s_lo = bzla_bv_to_char(d_mm, d->lo);

    d_hi = bitwuzla_mk_bv_value(bitwuzla, sort, s_hi, BITWUZLA_BV_BASE_BIN);
    d_lo = bitwuzla_mk_bv_value(bitwuzla, sort, s_lo, BITWUZLA_BV_BASE_BIN);

    a = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_AND, var, d_hi);
    o = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_OR, var, d_lo);

    eq1 = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_EQUAL, a, var);
    eq2 = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_EQUAL, o, var);

    _and = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_AND, eq1, eq2);

    bitwuzla_assert(bitwuzla, _and);

    bzla_mem_freestr(d_mm, s_hi);
    bzla_mem_freestr(d_mm, s_lo);
  }

  void print_domains_for_check_sat(BzlaBvDomain *d_x,
                                   BzlaBvDomain *d_y,
                                   BzlaBvDomain *d_z,
                                   BzlaBvDomain *d_c,
                                   BzlaBvDomain *res_x,
                                   BzlaBvDomain *res_y,
                                   BzlaBvDomain *res_z,
                                   BzlaBvDomain *res_c)
  {
    assert(d_x);
    assert(d_z);
    assert(res_x);
    assert(res_z);

    printf("\n");
    printf("x: ");
    print_domain(d_x, true);
    if (d_y)
    {
      printf("y: ");
      print_domain(d_y, true);
    }
    if (d_c)
    {
      printf("c: ");
      print_domain(d_c, true);
    }
    printf("z: ");
    print_domain(d_z, true);
    printf("x': ");
    print_domain(res_x, true);
    if (res_y)
    {
      printf("y': ");
      print_domain(res_y, true);
    }
    if (res_c)
    {
      printf("c': ");
      print_domain(res_c, true);
    }
    printf("z': ");
    print_domain(res_z, true);
  }

  void check_sat(BzlaBvDomain *d_x,
                 BzlaBvDomain *d_y,
                 BzlaBvDomain *d_z,
                 BzlaBvDomain *d_c,
                 BzlaBvDomain *res_x,
                 BzlaBvDomain *res_y,
                 BzlaBvDomain *res_z,
                 BzlaBvDomain *res_c,
                 uint32_t arity,
                 bool is_overflow,
                 BitwuzlaKind kind,
                 uint32_t hi,
                 uint32_t lo,
                 bool valid)
  {
    assert(d_x);
    assert(d_z);
    assert(res_x);
    assert(res_z);
    assert(!d_c || arity == 3);
    assert(!d_y || d_c || arity == 2 || kind == BITWUZLA_KIND_BV_SIGN_EXTEND);
    assert(kind != BITWUZLA_KIND_BV_SIGN_EXTEND || hi);
    assert(!is_overflow || kind == BITWUZLA_KIND_BV_ADD
           || kind == BITWUZLA_KIND_BV_MUL);

    BitwuzlaResult sat_res;
    uint32_t bwx, bwy, bwz;
    const BitwuzlaTerm *x, *y, *z, *c, *fun, *ofun, *_not, *eq;
    const BitwuzlaSort *swx, *swy, *swz, *s1;

    swy = 0;

    Bitwuzla *bitwuzla = bitwuzla_new();
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_INCREMENTAL, 1);
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_RW_LEVEL, 0);
    bwx = bzla_bvdomain_get_width(d_x);
    swx = bitwuzla_mk_bv_sort(bitwuzla, bwx);
    bwz = bzla_bvdomain_get_width(d_z);
    swz = bitwuzla_mk_bv_sort(bitwuzla, bwz);
    s1  = bitwuzla_mk_bv_sort(bitwuzla, 1);
    x   = bitwuzla_mk_const(bitwuzla, swx, "x");
    z   = bitwuzla_mk_const(bitwuzla, swz, "z");
    y   = 0;
    c   = 0;

    if (d_y)
    {
      bwy = bzla_bvdomain_get_width(d_y);
      swy = bitwuzla_mk_bv_sort(bitwuzla, bwy);
      y   = bitwuzla_mk_const(bitwuzla, swy, "y");
    }

    if (d_c)
    {
      ASSERT_NE(y, nullptr);
      c   = bitwuzla_mk_const(bitwuzla, s1, "c");
      fun = bitwuzla_mk_term3(bitwuzla, BITWUZLA_KIND_ITE, c, x, y);
    }
    else if (kind == BITWUZLA_KIND_BV_SIGN_EXTEND)
    {
      fun = bitwuzla_mk_term1_indexed1(bitwuzla, kind, x, hi);
    }
    else if (kind == BITWUZLA_KIND_BV_EXTRACT)
    {
      fun = bitwuzla_mk_term1_indexed2(bitwuzla, kind, x, hi, lo);
    }
    else if (arity == 1)
    {
      fun = bitwuzla_mk_term1(bitwuzla, kind, x);
    }
    else
    {
      assert(arity == 2);
      ASSERT_NE(y, nullptr);
      fun = bitwuzla_mk_term2(bitwuzla, kind, x, y);
      if (is_overflow)
      {
        if (kind == BITWUZLA_KIND_BV_ADD)
        {
          ofun =
              bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_UADD_OVERFLOW, x, y);
        }
        else
        {
          assert(kind == BITWUZLA_KIND_BV_MUL);
          ofun =
              bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_UMUL_OVERFLOW, x, y);
        }
        _not = bitwuzla_mk_term1(bitwuzla, BITWUZLA_KIND_BV_NOT, ofun);
        bitwuzla_assert(bitwuzla, _not);
      }
    }
    eq = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_EQUAL, fun, z);
    bitwuzla_assert(bitwuzla, eq);

    fix_domain_bits_for_check_sat(bitwuzla, x, d_x);
    if (d_y) fix_domain_bits_for_check_sat(bitwuzla, y, d_y);
    fix_domain_bits_for_check_sat(bitwuzla, z, d_z);
    if (d_c) fix_domain_bits_for_check_sat(bitwuzla, c, d_c);

    if (valid)
    {
      /* check fixed bits in result domains */

      bitwuzla_push(bitwuzla, 1);
      fix_result_bits_for_check_sat(bitwuzla, x, res_x);
      sat_res = bitwuzla_check_sat(bitwuzla);
      if (sat_res != BITWUZLA_UNSAT)
      {
        print_domains_for_check_sat(
            d_x, d_y, d_z, d_c, res_x, res_y, res_z, res_c);
      }
      ASSERT_TRUE(sat_res == BITWUZLA_UNSAT);
      bitwuzla_pop(bitwuzla, 1);

      if (res_y)
      {
        bitwuzla_push(bitwuzla, 1);
        fix_result_bits_for_check_sat(bitwuzla, y, res_y);
        sat_res = bitwuzla_check_sat(bitwuzla);
        if (sat_res != BITWUZLA_UNSAT)
        {
          print_domains_for_check_sat(
              d_x, d_y, d_z, d_c, res_x, res_y, res_z, res_c);
        }
        ASSERT_TRUE(sat_res == BITWUZLA_UNSAT);
        bitwuzla_pop(bitwuzla, 1);
      }
      bitwuzla_push(bitwuzla, 1);
      fix_result_bits_for_check_sat(bitwuzla, z, res_z);
      sat_res = bitwuzla_check_sat(bitwuzla);
      if (sat_res != BITWUZLA_UNSAT)
      {
        print_domains_for_check_sat(
            d_x, d_y, d_z, d_c, res_x, res_y, res_z, res_c);
      }
      ASSERT_TRUE(sat_res == BITWUZLA_UNSAT);
      bitwuzla_pop(bitwuzla, 1);
      if (res_c)
      {
        bitwuzla_push(bitwuzla, 1);
        fix_result_bits_for_check_sat(bitwuzla, c, res_c);
        sat_res = bitwuzla_check_sat(bitwuzla);
        if (sat_res != BITWUZLA_UNSAT)
        {
          print_domains_for_check_sat(
              d_x, d_y, d_z, d_c, res_x, res_y, res_z, res_c);
        }
        ASSERT_TRUE(sat_res == BITWUZLA_UNSAT);
        bitwuzla_pop(bitwuzla, 1);
      }
    }
    else
    {
      /* fixed bits in input domains should already be UNSAT */
      sat_res = bitwuzla_check_sat(bitwuzla);
      if (sat_res != BITWUZLA_UNSAT)
      {
        print_domains_for_check_sat(
            d_x, d_y, d_z, d_c, res_x, res_y, res_z, res_c);
      }
      ASSERT_TRUE(sat_res == BITWUZLA_UNSAT);
    }

    bitwuzla_delete(bitwuzla);
  }

  void test_shift_const(uint32_t bw, bool is_srl)
  {
    bool res;
    uint32_t i, j, n, num_consts;
    char **consts;
    BzlaBitVector *bv_n;
    BzlaBvDomain *d_x, *d_y, *d_z, *res_x, *res_z;

    num_consts = generate_consts(bw, &consts);

    for (i = 0; i < num_consts; i++)
    {
      d_z = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      for (j = 0; j < num_consts; j++)
      {
        d_x = bzla_bvdomain_new_from_char(d_mm, consts[j]);

        for (n = 0; n < bw + 1; n++)
        {
          bv_n = bzla_bv_uint64_to_bv(d_mm, n, bw);
          d_y  = bzla_bvdomain_new(d_mm, bv_n, bv_n);
          if (is_srl)
          {
            res = bzla_bvprop_srl_const(d_mm, d_x, d_z, bv_n, &res_x, &res_z);
            check_sat(d_x,
                      d_y,
                      d_z,
                      0,
                      res_x,
                      0,
                      res_z,
                      0,
                      2,
                      false,
                      BITWUZLA_KIND_BV_SHR,
                      0,
                      0,
                      res);
            if (res)
            {
              check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_SRL, 0, 0);
            }
          }
          else
          {
            res = bzla_bvprop_sll_const(d_mm, d_x, d_z, bv_n, &res_x, &res_z);
            check_sat(d_x,
                      d_y,
                      d_z,
                      0,
                      res_x,
                      0,
                      res_z,
                      0,
                      2,
                      false,
                      BITWUZLA_KIND_BV_SHL,
                      0,
                      0,
                      res);
            if (res)
            {
              check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_SLL, 0, 0);
            }
          }
          ASSERT_TRUE(res || !is_valid(d_mm, res_x, 0, res_z, 0));

          ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_x)
                      || !bzla_bvdomain_is_valid(d_mm, res_x)
                      || !bzla_bv_compare(d_x->lo, res_x->lo));
          ASSERT_TRUE(!res || !bzla_bvdomain_is_fixed(d_mm, d_z)
                      || !bzla_bvdomain_is_valid(d_mm, res_z)
                      || !bzla_bv_compare(d_z->lo, res_z->lo));
          if (res)
          {
            if (is_srl)
            {
              check_srl_const(res_x, res_z, n);
            }
            else
            {
              check_sll_const(res_x, res_z, n);
            }
          }

          TEST_BVPROP_RELEASE_RES_XZ;
          bzla_bv_free(d_mm, bv_n);
          bzla_bvdomain_free(d_mm, d_y);
        }
        bzla_bvdomain_free(d_mm, d_x);
      }
      bzla_bvdomain_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_sll_const(uint32_t bw) { test_shift_const(bw, false); }

  void test_srl_const(uint32_t bw) { test_shift_const(bw, true); }

  void test_shift(uint32_t bw, bool is_srl)
  {
    bool res;
    uint32_t i, j, k, num_consts;
    char **consts;
    BzlaBvDomain *d_x, *d_y, *d_z, *res_x, *res_y, *res_z;

    num_consts = generate_consts(bw, &consts);

    for (i = 0; i < num_consts; i++)
    {
      d_z = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      for (j = 0; j < num_consts; j++)
      {
        d_x = bzla_bvdomain_new_from_char(d_mm, consts[j]);

        for (k = 0; k < num_consts; k++)
        {
          d_y = bzla_bvdomain_new_from_char(d_mm, consts[k]);
          if (is_srl)
          {
            res = bzla_bvprop_srl(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
            check_sat(d_x,
                      d_y,
                      d_z,
                      0,
                      res_x,
                      res_y,
                      res_z,
                      0,
                      2,
                      false,
                      BITWUZLA_KIND_BV_SHR,
                      0,
                      0,
                      res);
            if (res)
            {
              check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_SRL, 0, 0);
            }
          }
          else
          {
            res = bzla_bvprop_sll(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
            check_sat(d_x,
                      d_y,
                      d_z,
                      0,
                      res_x,
                      res_y,
                      res_z,
                      0,
                      2,
                      false,
                      BITWUZLA_KIND_BV_SHL,
                      0,
                      0,
                      res);
            if (res)
            {
              check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_SLL, 0, 0);
            }
          }

          ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_x)
                      || !bzla_bvdomain_is_valid(d_mm, res_x)
                      || !bzla_bv_compare(d_x->lo, res_x->lo));
          ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_y)
                      || !bzla_bvdomain_is_valid(d_mm, res_y)
                      || !bzla_bv_compare(d_y->lo, res_y->lo));
          ASSERT_TRUE(!res || !bzla_bvdomain_is_fixed(d_mm, d_z)
                      || !bzla_bvdomain_is_valid(d_mm, res_z)
                      || !bzla_bv_compare(d_z->lo, res_z->lo));
          TEST_BVPROP_RELEASE_RES_XYZ;
          bzla_bvdomain_free(d_mm, d_y);
        }
        bzla_bvdomain_free(d_mm, d_x);
      }
      bzla_bvdomain_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_sll(uint32_t bw) { test_shift(bw, false); }

  void test_srl(uint32_t bw) { test_shift(bw, true); }

  void test_and_or_xor(BvPropOp op, uint32_t bw)
  {
    bool res;
    uint32_t num_consts;
    char **consts, *str_z, *str_x, *str_y, *str_res_z, *str_res_x, *str_res_y;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_x, *d_y, *d_z;
    BzlaBvDomain *res_x, *res_y, *res_z;
    BzlaBitVector *(*bvfun)(
        BzlaMemMgr *, const BzlaBitVector *, const BzlaBitVector *);
    bool (*bvpropfun)(BzlaMemMgr *,
                      BzlaBvDomain *,
                      BzlaBvDomain *,
                      BzlaBvDomain *,
                      BzlaBvDomain **,
                      BzlaBvDomain **,
                      BzlaBvDomain **);

    num_consts = generate_consts(bw, &consts);

    for (uint32_t i = 0; i < num_consts; i++)
    {
      d_z   = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      str_z = consts[i];

      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x   = bzla_bvdomain_new_from_char(d_mm, consts[j]);
        str_x = consts[j];

        for (uint32_t k = 0; k < num_consts; k++)
        {
          BitwuzlaKind kind;
          d_y   = bzla_bvdomain_new_from_char(d_mm, consts[k]);
          str_y = consts[k];

          if (op == TEST_BVPROP_AND)
          {
            kind      = BITWUZLA_KIND_BV_AND;
            bvpropfun = bzla_bvprop_and;
            bvfun     = bzla_bv_and;
          }
          else if (op == TEST_BVPROP_OR)
          {
            kind      = BITWUZLA_KIND_BV_OR;
            bvpropfun = bzla_bvprop_or;
            bvfun     = bzla_bv_or;
          }
          else
          {
            ASSERT_EQ(op, TEST_BVPROP_XOR);
            kind      = BITWUZLA_KIND_BV_XOR;
            bvpropfun = bzla_bvprop_xor;
            bvfun     = bzla_bv_xor;
          }

          res = bvpropfun(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    2,
                    false,
                    kind,
                    0,
                    0,
                    res);

          if (res)
          {
            check_synth(d_x, d_y, d_z, 0, res_z, op, 0, 0);
          }

          to_str(res_x, &str_res_x, 0, true);
          to_str(res_y, &str_res_y, 0, true);
          to_str(res_z, &str_res_z, 0, true);

          ASSERT_TRUE(res || !is_valid(d_mm, res_x, res_y, res_z, 0));

          ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_x)
                      || !bzla_bvdomain_is_valid(d_mm, res_x)
                      || !bzla_bv_compare(d_x->lo, res_x->lo));
          ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_y)
                      || !bzla_bvdomain_is_valid(d_mm, res_y)
                      || !bzla_bv_compare(d_y->lo, res_y->lo));
          ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_z)
                      || !bzla_bvdomain_is_valid(d_mm, res_z)
                      || !bzla_bv_compare(d_z->lo, res_z->lo));

          if (res && bzla_bvdomain_is_fixed(d_mm, d_x)
              && bzla_bvdomain_is_fixed(d_mm, d_y))
          {
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_x));
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bvfun(d_mm, res_x->lo, res_y->lo);
              ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
              ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
              ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_z));
              ASSERT_FALSE(bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvdomain_is_fixed(d_mm, d_z))
            {
              ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_z));
              tmp = bvfun(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
                ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bvfun(d_mm, res_x->lo, res_y->lo);
                ASSERT_FALSE(bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }

          if (bzla_bvdomain_is_valid(d_mm, res_z))
          {
            ASSERT_TRUE(bzla_bvdomain_is_valid(d_mm, res_x));
            ASSERT_TRUE(bzla_bvdomain_is_valid(d_mm, res_y));

            for (uint32_t l = 0; l < bw; l++)
            {
              if (op == TEST_BVPROP_AND)
              {
                ASSERT_TRUE(str_z[l] != '1'
                            || (str_x[l] != '0' && str_y[l] != '0'));
                ASSERT_TRUE(str_z[l] != '0'
                            || (str_x[l] != '1' || str_y[l] != '1'));

                ASSERT_TRUE(str_z[l] != '1' || str_x[l] != '1'
                            || str_res_y[l] == '1');
                ASSERT_TRUE(str_z[l] != '1' || str_y[l] != '1'
                            || str_res_x[l] == '1');
                ASSERT_TRUE(str_z[l] != '0' || str_x[l] != '1'
                            || str_res_y[l] == '0');
                ASSERT_TRUE(str_z[l] != '0' || str_y[l] != '1'
                            || str_res_x[l] == '0');
              }
              else if (op == TEST_BVPROP_OR)
              {
                ASSERT_TRUE(str_z[l] != '1' || str_x[l] != '0'
                            || str_y[l] != '0');
                ASSERT_TRUE(str_z[l] != '0'
                            || (str_x[l] != '1' && str_y[l] != '1'));

                ASSERT_TRUE(str_z[l] != '0' || str_x[l] != '0'
                            || str_res_y[l] == '0');
                ASSERT_TRUE(str_z[l] != '0' || str_y[l] != '0'
                            || str_res_x[l] == '0');
                ASSERT_TRUE(str_z[l] != '1' || str_x[l] != '0'
                            || str_res_y[l] == '1');
                ASSERT_TRUE(str_z[l] != '1' || str_y[l] != '0'
                            || str_res_x[l] == '1');
              }
              else
              {
                ASSERT_EQ(op, TEST_BVPROP_XOR);
                ASSERT_TRUE(str_z[l] != '1'
                            || (str_x[l] != '0' || str_y[l] != '0')
                            || (str_x[l] != '1' || str_y[l] != '1'));
                ASSERT_TRUE(str_z[l] != '0'
                            || ((str_x[l] != '0' || str_y[l] != '1')
                                && (str_x[l] != '1' || str_y[l] != '0')));

                ASSERT_TRUE(str_z[l] != '1' || str_x[l] != '1'
                            || str_res_y[l] == '0');
                ASSERT_TRUE(str_z[l] != '1' || str_y[l] != '1'
                            || str_res_x[l] == '0');
                ASSERT_TRUE(str_z[l] != '0' || str_x[l] != '0'
                            || str_res_y[l] == '0');
                ASSERT_TRUE(str_z[l] != '0' || str_y[l] != '0'
                            || str_res_x[l] == '0');
                ASSERT_TRUE(str_z[l] != '0' || str_x[l] != '1'
                            || str_res_y[l] == '1');
                ASSERT_TRUE(str_z[l] != '0' || str_y[l] != '1'
                            || str_res_x[l] == '1');
              }
            }
          }
          else
          {
            bool valid = true;
            for (uint32_t l = 0; l < bw && valid; l++)
            {
              if ((op == TEST_BVPROP_AND
                   && ((str_z[l] == '0' && str_x[l] != '0' && str_y[l] != '0')
                       || (str_z[l] == '1'
                           && (str_x[l] == '0' || str_y[l] == '0'))))
                  || (op == TEST_BVPROP_OR
                      && ((str_z[l] == '1' && str_x[l] != '1'
                           && str_y[l] != '1')
                          || (str_z[l] == '0'
                              && (str_x[l] == '1' || str_y[l] == '1'))))
                  || (op == TEST_BVPROP_XOR
                      && ((str_z[l] == '1'
                           && ((str_x[l] != '0' && str_y[l] != '0')
                               || (str_x[l] != '1' && str_y[l] != '1')))
                          || (str_z[l] == '0'
                              && ((str_x[l] != '1' && str_y[l] != '0')
                                  || (str_x[l] != '0' && str_y[l] != '1'))))))
              {
                valid = false;
              }
            }
            ASSERT_FALSE(valid);
          }

          bzla_mem_freestr(d_mm, str_res_x);
          bzla_mem_freestr(d_mm, str_res_y);
          bzla_mem_freestr(d_mm, str_res_z);

          bzla_bvdomain_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvdomain_free(d_mm, d_x);
      }
      bzla_bvdomain_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_and(uint32_t bw) { test_and_or_xor(TEST_BVPROP_AND, bw); }

  void test_or(uint32_t bw) { test_and_or_xor(TEST_BVPROP_OR, bw); }

  void test_xor(uint32_t bw) { test_and_or_xor(TEST_BVPROP_XOR, bw); }

  void test_eq(uint32_t bw)
  {
    bool res;
    char **consts;
    uint32_t num_consts;
    const char *values_z[] = {"x", "0", "1"};
    BzlaBvDomain *d_x, *d_y, *d_z, *res_x, *res_y, *res_z;
    BzlaBitVector *tmp;

    num_consts = generate_consts(bw, &consts);

    for (size_t k = 0; k < 3; k++)
    {
      d_z = bzla_bvdomain_new_from_char(d_mm, values_z[k]);
      for (size_t i = 0; i < num_consts; i++)
      {
        d_x = bzla_bvdomain_new_from_char(d_mm, consts[i]);
        for (size_t j = 0; j < num_consts; j++)
        {
          d_y = bzla_bvdomain_new_from_char(d_mm, consts[j]);

          res = bzla_bvprop_eq(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    2,
                    false,
                    BITWUZLA_KIND_EQUAL,
                    0,
                    0,
                    res);
          if (res)
          {
            check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_EQ, 0, 0);
          }

          if (res && bzla_bvdomain_is_fixed(d_mm, d_x)
              && bzla_bvdomain_is_fixed(d_mm, d_y))
          {
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_x));
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_eq(d_mm, res_x->lo, res_y->lo);
              ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
              ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
              ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_z));
              ASSERT_FALSE(bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvdomain_is_fixed(d_mm, d_z))
            {
              ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_z));
              tmp = bzla_bv_eq(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
                ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bzla_bv_eq(d_mm, res_x->lo, res_y->lo);
                ASSERT_FALSE(bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }
          bzla_bvdomain_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvdomain_free(d_mm, d_x);
      }
      bzla_bvdomain_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_not(uint32_t bw)
  {
    bool res;
    uint32_t num_consts;
    char **consts;
    BzlaBvDomain *d_x, *d_z, *res_x, *res_z;

    num_consts = generate_consts(bw, &consts);

    for (uint32_t i = 0; i < num_consts; i++)
    {
      d_x = bzla_bvdomain_new_from_char(d_mm, consts[i]);

      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_z = bzla_bvdomain_new_from_char(d_mm, consts[j]);
        res = bzla_bvprop_not(d_mm, d_x, d_z, &res_x, &res_z);
        check_sat(d_x,
                  0,
                  d_z,
                  0,
                  res_x,
                  0,
                  res_z,
                  0,
                  1,
                  false,
                  BITWUZLA_KIND_BV_NOT,
                  0,
                  0,
                  res);

        if (bzla_bvdomain_is_valid(d_mm, res_z))
        {
          ASSERT_TRUE(res);
          ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_x)
                      || !bzla_bv_compare(d_x->lo, res_x->lo));
          ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_z)
                      || !bzla_bv_compare(d_z->lo, res_z->lo));
          ASSERT_TRUE(bzla_bvdomain_is_valid(d_mm, res_x));
          ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_z)
                      || (bzla_bvdomain_is_fixed(d_mm, res_x)
                          && bzla_bvdomain_is_fixed(d_mm, res_z)));
          check_not(res_x, res_z);
        }
        else
        {
          ASSERT_FALSE(res);
          bool valid = true;
          for (uint32_t k = 0; k < bw && valid; k++)
          {
            if (consts[i][k] != 'x' && consts[i][k] == consts[j][k])
            {
              valid = false;
            }
          }
          ASSERT_FALSE(valid);
        }
        bzla_bvdomain_free(d_mm, d_z);
        TEST_BVPROP_RELEASE_RES_XZ;
      }
      bzla_bvdomain_free(d_mm, d_x);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_slice(uint32_t bw)
  {
    bool res;
    uint32_t num_consts;
    char *buf, **consts;
    BzlaBvDomain *d_x, *d_z, *res_x, *res_z;

    num_consts = generate_consts(bw, &consts);
    BZLA_CNEWN(d_mm, buf, bw + 1);

    for (uint32_t i = 0; i < num_consts; i++)
    {
      d_x = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        for (uint32_t lower = 0; lower < bw; lower++)
        {
          for (uint32_t upper = lower; upper < bw; upper++)
          {
            memset(buf, 0, bw + 1);
            memcpy(buf, &consts[j][bw - 1 - upper], upper - lower + 1);
            ASSERT_GT(strlen(buf), 0u);
            ASSERT_EQ(strlen(buf), upper - lower + 1);

            d_z = bzla_bvdomain_new_from_char(d_mm, buf);
            res =
                bzla_bvprop_slice(d_mm, d_x, d_z, upper, lower, &res_x, &res_z);
            /* not compositional but eq always returns true */
            ASSERT_TRUE(res || !is_valid(d_mm, res_x, 0, res_z, 0));
            check_sat(d_x,
                      0,
                      d_z,
                      0,
                      res_x,
                      0,
                      res_z,
                      0,
                      1,
                      false,
                      BITWUZLA_KIND_BV_EXTRACT,
                      upper,
                      lower,
                      res);
            if (res)
            {
              check_synth(
                  d_x, 0, d_z, 0, res_z, TEST_BVPROP_SLICE, upper, lower);
            }

            ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_x)
                        || !bzla_bvdomain_is_valid(d_mm, res_x)
                        || !bzla_bv_compare(d_x->lo, res_x->lo));
            ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_z)
                        || !bzla_bvdomain_is_valid(d_mm, res_z)
                        || !bzla_bv_compare(d_z->lo, res_z->lo));

            if (bzla_bvdomain_is_valid(d_mm, res_z))
            {
              ASSERT_TRUE(bzla_bvdomain_is_valid(d_mm, res_x));
              char *str_res_x = from_domain(d_mm, res_x);
              char *str_res_z = from_domain(d_mm, res_z);
              for (uint32_t k = 0; k < upper - lower + 1; k++)
              {
                ASSERT_EQ(str_res_z[k], str_res_x[bw - 1 - upper + k]);
              }
              bzla_mem_freestr(d_mm, str_res_x);
              bzla_mem_freestr(d_mm, str_res_z);
            }
            else
            {
              ASSERT_FALSE(bzla_bvdomain_is_valid(d_mm, res_x));
              bool valid = true;
              for (uint32_t k = 0; k < bw; k++)
              {
                if (buf[k] != consts[i][bw - 1 - upper + k])
                {
                  valid = false;
                  break;
                }
              }
              ASSERT_FALSE(valid);
            }
            bzla_bvdomain_free(d_mm, d_z);
            TEST_BVPROP_RELEASE_RES_XZ;
          }
        }
      }
      bzla_bvdomain_free(d_mm, d_x);
    }
    BZLA_DELETEN(d_mm, buf, bw + 1);
    free_consts(bw, num_consts, consts);
  }

  void test_concat(uint32_t bw)
  {
    uint32_t i, j, k, num_consts;
    char *s_const, **consts;
    BzlaBvDomain *d_x, *d_y, *d_z;

    num_consts = generate_consts(bw, &consts);

    for (i = 1; i < bw; i++)
    {
      j = bw - i;
      for (k = 0; k < num_consts; k++)
      {
        d_x = bzla_bvdomain_new_init(d_mm, i);
        d_y = bzla_bvdomain_new_init(d_mm, j);
        ASSERT_EQ(i + j, bw);
        d_z = bzla_bvdomain_new_init(d_mm, bw);
        check_concat(d_x, d_y, d_z);
        TEST_BVPROP_RELEASE_D_XYZ;

        s_const = slice_str_const(consts[k], 0, i - 1);
        d_x     = bzla_bvdomain_new_from_char(d_mm, s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_y = bzla_bvdomain_new_init(d_mm, j);
        d_z = bzla_bvdomain_new_init(d_mm, bw);
        check_concat(d_x, d_y, d_z);
        TEST_BVPROP_RELEASE_D_XYZ;

        d_x     = bzla_bvdomain_new_init(d_mm, i);
        s_const = slice_str_const(consts[k], i, bw - 1);
        d_y     = bzla_bvdomain_new_from_char(d_mm, s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = bzla_bvdomain_new_init(d_mm, bw);
        check_concat(d_x, d_y, d_z);
        TEST_BVPROP_RELEASE_D_XYZ;

        d_x = bzla_bvdomain_new_init(d_mm, i);
        d_y = bzla_bvdomain_new_init(d_mm, j);
        d_z = bzla_bvdomain_new_from_char(d_mm, consts[k]);
        check_concat(d_x, d_y, d_z);
        TEST_BVPROP_RELEASE_D_XYZ;

        s_const = slice_str_const(consts[k], 0, i - 1);
        d_x     = bzla_bvdomain_new_from_char(d_mm, s_const);
        bzla_mem_freestr(d_mm, s_const);
        s_const = slice_str_const(consts[k], i, bw - 1);
        d_y     = bzla_bvdomain_new_from_char(d_mm, s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = bzla_bvdomain_new_init(d_mm, bw);
        check_concat(d_x, d_y, d_z);
        TEST_BVPROP_RELEASE_D_XYZ;

        s_const = slice_str_const(consts[k], 0, i - 1);
        d_x     = bzla_bvdomain_new_from_char(d_mm, s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_y = bzla_bvdomain_new_init(d_mm, j);
        d_z = bzla_bvdomain_new_from_char(d_mm, consts[k]);
        check_concat(d_x, d_y, d_z);
        TEST_BVPROP_RELEASE_D_XYZ;

        d_x     = bzla_bvdomain_new_init(d_mm, i);
        s_const = slice_str_const(consts[k], i, bw - 1);
        d_y     = bzla_bvdomain_new_from_char(d_mm, s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = bzla_bvdomain_new_from_char(d_mm, consts[k]);
        check_concat(d_x, d_y, d_z);
        TEST_BVPROP_RELEASE_D_XYZ;

        s_const = slice_str_const(consts[k], 0, i - 1);
        d_x     = bzla_bvdomain_new_from_char(d_mm, s_const);
        bzla_mem_freestr(d_mm, s_const);
        s_const = slice_str_const(consts[k], i, bw - 1);
        d_y     = bzla_bvdomain_new_from_char(d_mm, s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = bzla_bvdomain_new_from_char(d_mm, consts[k]);
        check_concat(d_x, d_y, d_z);
        TEST_BVPROP_RELEASE_D_XYZ;
      }
    }
    free_consts(bw, num_consts, consts);
  }

  void test_sext(uint32_t bw)
  {
    bool res;
    uint32_t n, i, j, num_consts;
    char **consts;
    BzlaBvDomain *d_x, *d_z, *res_x, *res_z;

    num_consts = generate_consts(bw, &consts);

    for (i = 0; i < num_consts; i++)
    {
      d_z = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      for (j = 0; j < num_consts; j++)
      {
        for (n = 1; n < bw; n++)
        {
          d_x = bzla_bvdomain_new_from_char(d_mm, consts[j] + n);
          res = bzla_bvprop_sext(d_mm, d_x, d_z, &res_x, &res_z);
          check_sat(d_x,
                    0,
                    d_z,
                    0,
                    res_x,
                    0,
                    res_z,
                    0,
                    1,
                    false,
                    BITWUZLA_KIND_BV_SIGN_EXTEND,
                    n,
                    0,
                    res);

          ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, d_x)
                      || !bzla_bvdomain_is_valid(d_mm, res_x)
                      || !bzla_bv_compare(d_x->lo, res_x->lo));
          ASSERT_TRUE(!res || !bzla_bvdomain_is_fixed(d_mm, d_z)
                      || !bzla_bvdomain_is_valid(d_mm, res_z)
                      || !bzla_bv_compare(d_z->lo, res_z->lo));
          check_sext(res_x, res_z);
          TEST_BVPROP_RELEASE_RES_XZ;
          bzla_bvdomain_free(d_mm, d_x);
        }
      }
      bzla_bvdomain_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_cond(uint32_t bw)
  {
    bool res;
    uint32_t num_consts;
    char **consts;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_c, *d_x, *d_y, *d_z;
    BzlaBvDomain *res_c, *res_x, *res_y, *res_z;

    num_consts = generate_consts(bw, &consts);

    for (uint32_t c = 0; c < 3; c++)
    {
      if (c > 1)
      {
        d_c = bzla_bvdomain_new_init(d_mm, 1);
      }
      else
      {
        tmp = bzla_bv_uint64_to_bv(d_mm, c, 1);
        d_c = bzla_bvdomain_new(d_mm, tmp, tmp);
        bzla_bv_free(d_mm, tmp);
      }

      for (uint32_t i = 0; i < num_consts; i++)
      {
        d_z = bzla_bvdomain_new_from_char(d_mm, consts[i]);
        for (uint32_t j = 0; j < num_consts; j++)
        {
          d_x = bzla_bvdomain_new_from_char(d_mm, consts[j]);
          for (uint32_t k = 0; k < num_consts; k++)
          {
            d_y = bzla_bvdomain_new_from_char(d_mm, consts[k]);

            res = bzla_bvprop_cond(
                d_mm, d_x, d_y, d_z, d_c, &res_x, &res_y, &res_z, &res_c);
            check_sat(d_x,
                      d_y,
                      d_z,
                      d_c,
                      res_x,
                      res_y,
                      res_z,
                      res_c,
                      3,
                      false,
                      BITWUZLA_KIND_ITE,
                      0,
                      0,
                      res);
            if (res) check_cond(res_x, res_y, res_z, res_c);

            bzla_bvdomain_free(d_mm, d_y);
            TEST_BVPROP_RELEASE_RES_XYZ;
            bzla_bvdomain_free(d_mm, res_c);
          }
          bzla_bvdomain_free(d_mm, d_x);
        }
        bzla_bvdomain_free(d_mm, d_z);
      }
      bzla_bvdomain_free(d_mm, d_c);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_add(uint32_t bw, bool no_overflows)
  {
    bool res;
    uint32_t num_consts;
    char **consts;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_x, *d_y, *d_z;
    BzlaBvDomain *res_x, *res_y, *res_z;

    num_consts = generate_consts(bw, &consts);

    for (uint32_t i = 0; i < num_consts; i++)
    {
      d_z = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = bzla_bvdomain_new_from_char(d_mm, consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = bzla_bvdomain_new_from_char(d_mm, consts[k]);

          res = bzla_bvprop_add_aux(
              d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z, no_overflows);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    2,
                    no_overflows,
                    BITWUZLA_KIND_BV_ADD,
                    0,
                    0,
                    res);

          if (bzla_bvdomain_is_fixed(d_mm, d_x)
              && bzla_bvdomain_is_fixed(d_mm, d_y))
          {
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_x));
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_add(d_mm, res_x->lo, res_y->lo);
              ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
              ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
              ASSERT_TRUE(no_overflows || bzla_bvdomain_is_fixed(d_mm, res_z));
              ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, res_z)
                          || !bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvdomain_is_fixed(d_mm, d_z))
            {
              ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_z));
              tmp = bzla_bv_add(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
                ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bzla_bv_add(d_mm, res_x->lo, res_y->lo);
                ASSERT_FALSE(bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }
          bzla_bvdomain_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvdomain_free(d_mm, d_x);
      }
      bzla_bvdomain_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  /* In these mul cases, the AIG layer is better in propagating const bits
   * than the domain propagators. For now we thus expect this to fail. */
  bool mul_expect_fail(BzlaBvDomain *d_x,
                       BzlaBvDomain *d_y,
                       BzlaBvDomain *d_z,
                       bool no_overflows)
  {
    bool res     = false;
    char *char_x = 0, *char_y = 0, *char_z = 0;

    char_z            = bzla_bvdomain_to_char(d_mm, d_z);
    std::string str_z = char_z;
    if (str_z != "xxx")
    {
      bzla_mem_freestr(d_mm, char_z);
      return false;
    }

    char_x            = bzla_bvdomain_to_char(d_mm, d_x);
    char_y            = bzla_bvdomain_to_char(d_mm, d_y);
    std::string str_x = char_x;
    std::string str_y = char_y;

    if (str_x == "011")
    {
      if (str_y == "0x1" || str_y == "1x1")
      {
        res = true;
      }
    }
    else if (str_x == "01x" && str_y == "111")
    {
      res = true;
    }
    else if (str_x == "0x1")
    {
      if (!no_overflows)
      {
        if (str_y == "1x1" || str_y == "111")
        {
          res = true;
        }
      }

      if (str_y == "011" || str_y == "0x1")
      {
        res = true;
      }
    }
    else if (str_x == "111")
    {
      if (!no_overflows)
      {
        if (str_y == "0x1")
        {
          res = true;
        }
      }

      if (str_y == "01x" || str_y == "11x" || str_y == "1x1")
      {
        res = true;
      }
    }
    else if (str_x == "11x" && str_y == "111")
    {
      res = true;
    }
    else if (str_x == "1x1")
    {
      if (!no_overflows)
      {
        if (str_y == "0x1")
        {
          res = true;
        }
      }

      if (str_y == "1x1" || str_y == "111" || str_y == "011")
      {
        res = true;
      }
    }

    bzla_mem_freestr(d_mm, char_x);
    bzla_mem_freestr(d_mm, char_y);
    bzla_mem_freestr(d_mm, char_z);
    return res;
  }

  void test_mul(uint32_t bw, bool no_overflows)
  {
    bool res, expect_fail;
    uint32_t num_consts;
    char **consts;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_x, *d_y, *d_z;
    BzlaBvDomain *res_x, *res_y, *res_z;

    num_consts = generate_consts(bw, &consts);

    for (uint32_t i = 0; i < num_consts; i++)
    {
      d_z = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = bzla_bvdomain_new_from_char(d_mm, consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = bzla_bvdomain_new_from_char(d_mm, consts[k]);

          res = bzla_bvprop_mul_aux(
              d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z, no_overflows);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    2,
                    no_overflows,
                    BITWUZLA_KIND_BV_MUL,
                    0,
                    0,
                    res);
          if (res)
          {
            expect_fail = mul_expect_fail(d_x, d_y, d_z, no_overflows);
            check_synth(
                d_x, d_y, d_z, 0, res_z, TEST_BVPROP_MUL, 0, 0, expect_fail);
          }

          if (bzla_bvdomain_is_fixed(d_mm, d_x)
              && bzla_bvdomain_is_fixed(d_mm, d_y))
          {
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_x));
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_mul(d_mm, res_x->lo, res_y->lo);
              ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
              ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
              ASSERT_TRUE(no_overflows || bzla_bvdomain_is_fixed(d_mm, res_z));
              ASSERT_TRUE(!bzla_bvdomain_is_fixed(d_mm, res_z)
                          || !bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvdomain_is_fixed(d_mm, d_z))
            {
              ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_z));
              tmp = bzla_bv_mul(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
                ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bzla_bv_mul(d_mm, res_x->lo, res_y->lo);
                ASSERT_FALSE(bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }

          bzla_bvdomain_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvdomain_free(d_mm, d_x);
      }
      bzla_bvdomain_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  /* In these udiv cases, the AIG layer is better in propagating const bits
   * than the domain propagators. For now we thus expect this to fail. */
  bool udiv_expect_fail(BzlaBvDomain *d_x, BzlaBvDomain *d_y, BzlaBvDomain *d_z)
  {
    bool res     = false;
    char *char_x = 0, *char_y = 0, *char_z = 0;

    char_z = bzla_bvdomain_to_char(d_mm, d_z);
    char_x = bzla_bvdomain_to_char(d_mm, d_x);
    char_y = bzla_bvdomain_to_char(d_mm, d_y);

    std::string str_z = char_z;
    std::string str_x = char_x;
    std::string str_y = char_y;

    //// one bit
    if (str_z == "x")
    {
      if (str_x == "1")
      {
        if (str_y == "x")
        {
          res = true;
        }
      }
    }

    //// two bits
    if (str_z == "xx")
    {
      if (str_x == "01")
      {
        if (str_y == "1x" || str_y == "0x")
        {
          res = true;
        }
      }
      else if (str_x == "0x")
      {
        if (str_y == "1x")
        {
          res = true;
        }
      }
      else if (str_x == "1x")
      {
        if (str_y == "1x" || str_y == "0x" || str_y == "x0")
        {
          res = true;
        }
      }
      else if (str_x == "x0")
      {
        if (str_y == "01" || str_y == "1x" || str_y == "x1")
        {
          res = true;
        }
      }
      else if (str_x == "x1")
      {
        if (str_y == "0x" || str_y == "01" || str_y == "1x")
        {
          res = true;
        }
      }
      else if (str_x == "10")
      {
        if (str_y == "1x" || str_y == "0x" || str_y == "x0" || str_y == "x1")
        {
          res = true;
        }
      }
      else if (str_x == "11")
      {
        if (str_y == "1x" || str_y == "0x" || str_y == "x0" || str_y == "x1"
            || str_y == "xx")
        {
          res = true;
        }
      }
      else if (str_x == "xx")
      {
        if (str_y == "1x")
        {
          res = true;
        }
      }
    }

    //// three bits
    if (str_z == "xxx")
    {
      if (str_x == "001")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "10x" || str_y == "1xx"
            || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "00x")
      {
        if (str_y == "01x" || str_y == "10x" || str_y == "1xx"
            || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "010")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x0" || str_y == "0x1"
            || str_y == "10x" || str_y == "1x0" || str_y == "1xx"
            || str_y == "x01" || str_y == "x1x" || str_y == "xx1")
        {
          res = true;
        }
      }
      else if (str_x == "011")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x0" || str_y == "0x1"
            || str_y == "0xx" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "01x")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x0" || str_y == "10x"
            || str_y == "1x0" || str_y == "1xx" || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "0x0")
      {
        if (str_y == "01x" || str_y == "0x1" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x01" || str_y == "x1x"
            || str_y == "001")
        {
          res = true;
        }
      }
      else if (str_x == "0x1")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x1x" || str_y == "001")
        {
          res = true;
        }
      }
      else if (str_x == "0xx")
      {
        if (str_y == "01x" || str_y == "10x" || str_y == "1x0" || str_y == "1xx"
            || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "100")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0x1" || str_y == "01x"
            || str_y == "10x" || str_y == "1x0" || str_y == "1xx"
            || str_y == "1xx" || str_y == "x00" || str_y == "x1x"
            || str_y == "x00" || str_y == "x01" || str_y == "x10"
            || str_y == "xx1")
        {
          res = true;
        }
      }
      else if (str_x == "101")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0x1" || str_y == "01x"
            || str_y == "10x" || str_y == "1x0" || str_y == "1xx"
            || str_y == "11x" || str_y == "x00" || str_y == "x01"
            || str_y == "x0x" || str_y == "x1x" || str_y == "x10"
            || str_y == "xx1")
        {
          res = true;
        }
      }
      else if (str_x == "10x")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x0" || str_y == "0x1"
            || str_y == "10x" || str_y == "11x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x1x" || str_y == "x00"
            || str_y == "x01" || str_y == "x10" || str_y == "xx1")
        {
          res = true;
        }
      }
      else if (str_x == "110")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x0" || str_y == "0x1"
            || str_y == "0xx" || str_y == "10x" || str_y == "1xx"
            || str_y == "x1x" || str_y == "1x0" || str_y == "x00"
            || str_y == "x10" || str_y == "x11" || str_y == "xx0")
        {
          res = true;
        }
      }
      else if (str_x == "111")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x0" || str_y == "0x1"
            || str_y == "0xx" || str_y == "10x" || str_y == "11x"
            || str_y == "1x0" || str_y == "1x1" || str_y == "1xx"
            || str_y == "x00" || str_y == "x01" || str_y == "x0x"
            || str_y == "x1x" || str_y == "x10" || str_y == "xx0")
        {
          res = true;
        }
      }
      else if (str_x == "11x")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x0" || str_y == "0x1"
            || str_y == "0xx" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x1x" || str_y == "x00"
            || str_y == "x10" || str_y == "xx0")
        {
          res = true;
        }
      }
      else if (str_x == "1x0")
      {
        if (str_y == "00x" || str_y == "001" || str_y == "0x0" || str_y == "01x"
            || str_y == "10x" || str_y == "1x0" || str_y == "1xx"
            || str_y == "x1x" || str_y == "x00")
        {
          res = true;
        }
      }
      else if (str_x == "1x1")
      {
        if (str_y == "00x" || str_y == "001" || str_y == "01x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "0x0" || str_y == "101"
            || str_y == "10x" || str_y == "x00" || str_y == "x01"
            || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "1xx")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "x00" || str_y == "01x"
            || str_y == "10x" || str_y == "1x0" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "x00")
      {
        if (str_y == "0x1" || str_y == "x01" || str_y == "x10" || str_y == "001"
            || str_y == "010" || str_y == "01x" || str_y == "10x"
            || str_y == "1x0" || str_y == "1xx" || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "x01")
      {
        if (str_y == "00x" || str_y == "0x1" || str_y == "001" || str_y == "010"
            || str_y == "01x" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "11x" || str_y == "x01"
            || str_y == "x1x" || str_y == "x10")
        {
          res = true;
        }
      }
      else if (str_x == "x0x")
      {
        if (str_y == "0x1" || str_y == "001" || str_y == "010" || str_y == "01x"
            || str_y == "10x" || str_y == "1x0" || str_y == "1xx"
            || str_y == "x1x" || str_y == "11x" || str_y == "x01"
            || str_y == "x10")
        {
          res = true;
        }
      }
      else if (str_x == "x10")
      {
        if (str_y == "00x" || str_y == "011" || str_y == "0x0" || str_y == "0x1"
            || str_y == "001" || str_y == "010" || str_y == "01x"
            || str_y == "10x" || str_y == "1x0" || str_y == "1xx"
            || str_y == "x1x" || str_y == "x11")
        {
          res = true;
        }
      }
      else if (str_x == "x11")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "001" || str_y == "010"
            || str_y == "01x" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "x1x")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "001" || str_y == "010"
            || str_y == "01x" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "xx0")
      {
        if (str_y == "001" || str_y == "01x" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "xx1")
      {
        if (str_y == "00x" || str_y == "001" || str_y == "01x" || str_y == "10x"
            || str_y == "1x0" || str_y == "1xx" || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "xxx")
      {
        if (str_y == "01x" || str_y == "10x" || str_y == "1x0" || str_y == "1xx"
            || str_y == "x1x")
        {
          res = true;
        }
      }
    }

    bzla_mem_freestr(d_mm, char_x);
    bzla_mem_freestr(d_mm, char_y);
    bzla_mem_freestr(d_mm, char_z);
    return res;
  }

  void test_udiv(uint32_t bw)
  {
    bool res, expect_fail;
    bool is_fixed_x, is_fixed_y, is_fixed_z;
    bool is_fixed_res_x, is_fixed_res_y, is_fixed_res_z;
    uint32_t num_consts;
    char **consts;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_x, *d_y, *d_z;
    BzlaBvDomain *res_x, *res_y, *res_z;

    num_consts = generate_consts(bw, &consts);
    for (uint32_t i = 0; i < num_consts; i++)
    {
      d_z = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = bzla_bvdomain_new_from_char(d_mm, consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = bzla_bvdomain_new_from_char(d_mm, consts[k]);

          res = bzla_bvprop_udiv(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    2,
                    false,
                    BITWUZLA_KIND_BV_UDIV,
                    0,
                    0,
                    res);
          if (res)
          {
            expect_fail = udiv_expect_fail(d_x, d_y, d_z);
            check_synth(
                d_x, d_y, d_z, 0, res_z, TEST_BVPROP_UDIV, 0, 0, expect_fail);
          }

          is_fixed_x     = bzla_bvdomain_is_fixed(d_mm, d_x);
          is_fixed_y     = bzla_bvdomain_is_fixed(d_mm, d_y);
          is_fixed_z     = bzla_bvdomain_is_fixed(d_mm, d_z);
          is_fixed_res_x = bzla_bvdomain_is_fixed(d_mm, res_x);
          is_fixed_res_y = bzla_bvdomain_is_fixed(d_mm, res_y);
          is_fixed_res_z = bzla_bvdomain_is_fixed(d_mm, res_z);

          ASSERT_TRUE(!res || !is_fixed_x || is_fixed_res_x);
          ASSERT_TRUE(!res || !is_fixed_y || is_fixed_res_y);
          ASSERT_TRUE(!res || !is_fixed_z || is_fixed_res_z);

          if (res && is_fixed_x && is_fixed_y)
          {
            ASSERT_TRUE(is_fixed_res_z);
            ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
            ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_z));
            tmp = bzla_bv_udiv(d_mm, d_x->lo, d_y->lo);
            if (!bzla_bv_compare(tmp, d_z->lo))
            {
              ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
              ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
              bzla_bv_free(d_mm, tmp);
              tmp = bzla_bv_udiv(d_mm, d_x->lo, d_y->lo);
              ASSERT_FALSE(bzla_bv_compare(tmp, res_z->lo));
            }
            bzla_bv_free(d_mm, tmp);
          }

          if (res && is_fixed_x && is_fixed_z)
          {
            ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
            ASSERT_FALSE(bzla_bv_compare(d_z->lo, res_z->lo));
            // this is a check if any bits are propagated to y (they aren't)
            // for (uint32_t i = 0; i < res_y->lo->width; i++)
            //   ASSERT_TRUE (bzla_bvdomain_is_fixed_bit (d_y, i)
            //           || !bzla_bvdomain_is_fixed_bit (res_y, i));
            if (bzla_bvdomain_is_fixed(d_mm, res_y))
            {
              tmp = bzla_bv_udiv(d_mm, d_x->lo, res_y->lo);
              ASSERT_FALSE(bzla_bv_compare(tmp, d_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
          }

          if (res && is_fixed_y && is_fixed_z)
          {
            ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
            ASSERT_FALSE(bzla_bv_compare(d_z->lo, res_z->lo));
            // this is a check if any bits are propagated to x (they aren't)
            // for (uint32_t i = 0; i < res_x->lo->width; i++)
            //   ASSERT_TRUE (bzla_bvdomain_is_fixed_bit (d_x, i)
            //           || !bzla_bvdomain_is_fixed_bit (res_x, i));
            if (bzla_bvdomain_is_fixed(d_mm, res_x))
            {
              tmp = bzla_bv_udiv(d_mm, res_x->lo, d_y->lo);
              ASSERT_FALSE(bzla_bv_compare(tmp, d_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
          }

          bzla_bvdomain_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvdomain_free(d_mm, d_x);
      }
      bzla_bvdomain_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  /* In these urem cases, the AIG layer is better in propagating const bits
   * than the domain propagators. For now we thus expect this to fail. */
  bool urem_expect_fail(BzlaBvDomain *d_x, BzlaBvDomain *d_y, BzlaBvDomain *d_z)
  {
    bool res     = false;
    char *char_x = 0, *char_y = 0, *char_z = 0;

    char_z = bzla_bvdomain_to_char(d_mm, d_z);
    char_x = bzla_bvdomain_to_char(d_mm, d_x);
    char_y = bzla_bvdomain_to_char(d_mm, d_y);

    std::string str_z = char_z;
    std::string str_x = char_x;
    std::string str_y = char_y;

    //// one bit
    if (str_z == "x")
    {
      if ((str_x == "0" && str_y == "x") || (str_x == "x" && str_y == "1"))
      {
        res = true;
      }
    }

    //// two bits
    if (str_z == "xx")
    {
      if (str_x == "00")
      {
        if (str_y == "0x" || str_y == "x0" || str_y == "xx")
        {
          res = true;
        }
      }
      else if (str_x == "01")
      {
        if (str_y == "0x" || str_y == "1x" || str_y == "x0" || str_y == "x1"
            || str_y == "xx")
        {
          res = true;
        }
      }
      else if (str_x == "0x")
      {
        if (str_y == "0x" || str_y == "1x" || str_y == "x0" || str_y == "x1"
            || str_y == "xx" || str_y == "01")
        {
          res = true;
        }
      }
      else if (str_x == "10")
      {
        if (str_y == "0x" || str_y == "1x" || str_y == "x1" || str_y == "xx")
        {
          res = true;
        }
      }
      else if (str_x == "11")
      {
        if (str_y == "1x" || str_y == "x1")
        {
          res = true;
        }
      }
      else if (str_x == "1x")
      {
        if (str_y == "11" || str_y == "x1" || str_y == "01")
        {
          res = true;
        }
      }
      else if (str_x == "x0")
      {
        if (str_y == "0x" || str_y == "1x" || str_y == "x1" || str_y == "01"
            || str_y == "10")
        {
          res = true;
        }
      }
      else if (str_x == "x1")
      {
        if (str_y == "11" || str_y == "1x" || str_y == "x1" || str_y == "01"
            || str_y == "10")
        {
          res = true;
        }
      }
      else if (str_x == "xx")
      {
        if (str_y == "01" || str_y == "10")
        {
          res = true;
        }
      }
    }

    //// three bits
    if (str_z == "xxx")
    {
      if (str_x == "000")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0xx" || str_y == "x00"
            || str_y == "x0x" || str_y == "xx0" || str_y == "xxx")
        {
          res = true;
        }
      }
      else if (str_x == "001")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0x1" || str_y == "01x"
            || str_y == "10x" || str_y == "1xx" || str_y == "x01"
            || str_y == "x1x" || str_y == "0xx" || str_y == "x00"
            || str_y == "x0x" || str_y == "xx0" || str_y == "xx1"
            || str_y == "xxx")
        {
          res = true;
        }
      }
      else if (str_x == "010")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "01x" || str_y == "0x1"
            || str_y == "10x" || str_y == "1x0" || str_y == "0xx"
            || str_y == "1xx" || str_y == "x00" || str_y == "x01"
            || str_y == "x10" || str_y == "x0x" || str_y == "x1x"
            || str_y == "xx0" || str_y == "xx1" || str_y == "xxx")
        {
          res = true;
        }
      }
      else if (str_x == "011")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "01x" || str_y == "0x1"
            || str_y == "10x" || str_y == "1x0" || str_y == "0xx"
            || str_y == "1xx" || str_y == "x00" || str_y == "x01"
            || str_y == "x10" || str_y == "x11" || str_y == "x0x"
            || str_y == "x1x" || str_y == "xx0" || str_y == "xx1"
            || str_y == "xxx")
        {
          res = true;
        }
      }
      else if (str_x == "0x0")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "01x" || str_y == "0x1"
            || str_y == "10x" || str_y == "1x0" || str_y == "001"
            || str_y == "010" || str_y == "0xx" || str_y == "1xx"
            || str_y == "x00" || str_y == "x01" || str_y == "x10"
            || str_y == "x0x" || str_y == "x1x" || str_y == "xx0"
            || str_y == "xx1" || str_y == "xxx")
        {
          res = true;
        }
      }
      else if (str_x == "0x1")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "01x" || str_y == "0x1"
            || str_y == "10x" || str_y == "1x0" || str_y == "001"
            || str_y == "010" || str_y == "011" || str_y == "0xx"
            || str_y == "1xx" || str_y == "x00" || str_y == "x01"
            || str_y == "x10" || str_y == "x11" || str_y == "x0x"
            || str_y == "x1x" || str_y == "xx0" || str_y == "xx1"
            || str_y == "xxx")
        {
          res = true;
        }
      }
      else if (str_x == "00x")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0x1" || str_y == "10x"
            || str_y == "1xx" || str_y == "001" || str_y == "01x"
            || str_y == "0xx" || str_y == "x00" || str_y == "x01"
            || str_y == "x0x" || str_y == "x1x" || str_y == "xx0"
            || str_y == "xx1" || str_y == "xxx")
        {
          res = true;
        }
      }
      else if (str_x == "x10")
      {
        if (str_y == "00x" || str_y == "001" || str_y == "010" || str_y == "011"
            || str_y == "100" || str_y == "01x" || str_y == "0x1"
            || str_y == "101" || str_y == "10x" || str_y == "110"
            || str_y == "11x" || str_y == "1x0" || str_y == "x01"
            || str_y == "x10" || str_y == "x11")
        {
          res = true;
        }
      }
      else if (str_x == "x00")
      {
        if (str_y == "001" || str_y == "010" || str_y == "100" || str_y == "00x"
            || str_y == "011" || str_y == "01x" || str_y == "0x0"
            || str_y == "0x1" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x01" || str_y == "x10")
        {
          res = true;
        }
      }
      else if (str_x == "1x1")
      {
        if (str_y == "001" || str_y == "010" || str_y == "011" || str_y == "01x"
            || str_y == "101" || str_y == "10x" || str_y == "110"
            || str_y == "111" || str_y == "11x" || str_y == "x01"
            || str_y == "x10")
        {
          res = true;
        }
      }
      else if (str_x == "1x0")
      {
        if (str_y == "001" || str_y == "010" || str_y == "01x" || str_y == "0x1"
            || str_y == "00x" || str_y == "011" || str_y == "101"
            || str_y == "110" || str_y == "11x" || str_y == "x01"
            || str_y == "x10")
        {
          res = true;
        }
      }
      else if (str_x == "01x")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x0" || str_y == "0x1"
            || str_y == "001" || str_y == "011" || str_y == "0xx"
            || str_y == "10x" || str_y == "1x0" || str_y == "1xx"
            || str_y == "x00" || str_y == "x01" || str_y == "x0x"
            || str_y == "x10" || str_y == "x11" || str_y == "x1x"
            || str_y == "xx0" || str_y == "xx1" || str_y == "xxx")
        {
          res = true;
        }
      }
      else if (str_x == "100")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x0" || str_y == "0x1"
            || str_y == "10x" || str_y == "1x0" || str_y == "1xx"
            || str_y == "x01" || str_y == "x0x" || str_y == "x10"
            || str_y == "x1x" || str_y == "xx0" || str_y == "xx1")
        {
          res = true;
        }
      }
      else if (str_x == "101")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0x1" || str_y == "01x"
            || str_y == "10x" || str_y == "11x" || str_y == "1x0"
            || str_y == "1x1" || str_y == "1xx" || str_y == "x01"
            || str_y == "x0x" || str_y == "x10" || str_y == "xx0")
        {
          res = true;
        }
      }
      else if (str_x == "110")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x1" || str_y == "0xx"
            || str_y == "10x" || str_y == "11x" || str_y == "1x0"
            || str_y == "x01" || str_y == "x10" || str_y == "x11"
            || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "0xx")
      {
        if (str_y == "00x" || str_y == "001" || str_y == "0x0" || str_y == "0xx"
            || str_y == "010" || str_y == "011" || str_y == "01x"
            || str_y == "0x1" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx" || str_y == "x00" || str_y == "x01"
            || str_y == "x0x" || str_y == "x10" || str_y == "x11"
            || str_y == "x1x" || str_y == "xx0" || str_y == "xx1"
            || str_y == "xxx")
        {
          res = true;
        }
      }
      else if (str_x == "111")
      {
        if (str_y == "01x" || str_y == "0x1" || str_y == "10x" || str_y == "11x"
            || str_y == "1x0" || str_y == "1x1" || str_y == "1xx"
            || str_y == "x01" || str_y == "x10" || str_y == "x11"
            || str_y == "x1x" || str_y == "xx1")
        {
          res = true;
        }
      }
      else if (str_x == "11x")
      {
        if (str_y == "001" || str_y == "01x" || str_y == "0x1" || str_y == "10x"
            || str_y == "111" || str_y == "1x0" || str_y == "x01"
            || str_y == "x10")
        {
          res = true;
        }
      }
      else if (str_x == "10x")
      {
        if (str_y == "00x" || str_y == "001" || str_y == "0x0" || str_y == "101"
            || str_y == "10x" || str_y == "01x" || str_y == "0x1"
            || str_y == "11x" || str_y == "1x0" || str_y == "1x1"
            || str_y == "1xx" || str_y == "x01" || str_y == "x10"
            || str_y == "xx0")
        {
          res = true;
        }
      }
      else if (str_x == "1xx")
      {
        if (str_y == "001" || str_y == "010" || str_y == "011" || str_y == "01x"
            || str_y == "110" || str_y == "x10")
        {
          res = true;
        }
      }
      else if (str_x == "x0x")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "101" || str_y == "10x"
            || str_y == "001" || str_y == "010" || str_y == "011"
            || str_y == "01x" || str_y == "0x1" || str_y == "100"
            || str_y == "11x" || str_y == "1x0" || str_y == "1x1"
            || str_y == "1xx" || str_y == "x10")
        {
          res = true;
        }
      }
      else if (str_x == "x01")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "101" || str_y == "10x"
            || str_y == "001" || str_y == "010" || str_y == "011"
            || str_y == "01x" || str_y == "0x1" || str_y == "100"
            || str_y == "11x" || str_y == "1x0" || str_y == "1x1"
            || str_y == "1xx" || str_y == "x01" || str_y == "x10")
        {
          res = true;
        }
      }
      else if (str_x == "x11")
      {
        if (str_y == "011" || str_y == "01x" || str_y == "0x1" || str_y == "101"
            || str_y == "10x" || str_y == "110" || str_y == "111"
            || str_y == "001" || str_y == "010" || str_y == "100"
            || str_y == "11x" || str_y == "1x0" || str_y == "1x1"
            || str_y == "1xx" || str_y == "x01" || str_y == "x10"
            || str_y == "x11" || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "x1x")
      {
        if (str_y == "101" || str_y == "10x" || str_y == "110" || str_y == "1x0"
            || str_y == "001" || str_y == "010" || str_y == "011"
            || str_y == "0x1" || str_y == "01x" || str_y == "100"
            || str_y == "x01" || str_y == "x10")
        {
          res = true;
        }
      }
      else if (str_x == "xx0")
      {
        if (str_y == "00x" || str_y == "11x" || str_y == "001" || str_y == "010"
            || str_y == "011" || str_y == "100")
        {
          res = true;
        }
      }
      else if (str_x == "xx1")
      {
        if (str_y == "101" || str_y == "10x" || str_y == "001" || str_y == "010"
            || str_y == "011" || str_y == "100")
        {
          res = true;
        }
      }
      else if (str_x == "xxx")
      {
        if (str_y == "001" || str_y == "010" || str_y == "100")
        {
          res = true;
        }
      }
    }
    bzla_mem_freestr(d_mm, char_x);
    bzla_mem_freestr(d_mm, char_y);
    bzla_mem_freestr(d_mm, char_z);
    return res;
  }

  void test_urem(uint32_t bw)
  {
    bool res, expect_fail;
    bool is_fixed_x, is_fixed_y, is_fixed_z;
    bool is_fixed_res_x, is_fixed_res_y, is_fixed_res_z;
    uint32_t num_consts;
    char **consts;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_x, *d_y, *d_z;
    BzlaBvDomain *res_x, *res_y, *res_z;

    num_consts = generate_consts(bw, &consts);

    for (uint32_t i = 0; i < num_consts; i++)
    {
      d_z = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = bzla_bvdomain_new_from_char(d_mm, consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = bzla_bvdomain_new_from_char(d_mm, consts[k]);

          res = bzla_bvprop_urem(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    2,
                    false,
                    BITWUZLA_KIND_BV_UREM,
                    0,
                    0,
                    res);
          if (res)
          {
            expect_fail = urem_expect_fail(d_x, d_y, d_z);
            check_synth(
                d_x, d_y, d_z, 0, res_z, TEST_BVPROP_UREM, 0, 0, expect_fail);
          }

          is_fixed_x     = bzla_bvdomain_is_fixed(d_mm, d_x);
          is_fixed_y     = bzla_bvdomain_is_fixed(d_mm, d_y);
          is_fixed_z     = bzla_bvdomain_is_fixed(d_mm, d_z);
          is_fixed_res_x = bzla_bvdomain_is_fixed(d_mm, res_x);
          is_fixed_res_y = bzla_bvdomain_is_fixed(d_mm, res_y);
          is_fixed_res_z = bzla_bvdomain_is_fixed(d_mm, res_z);

          ASSERT_TRUE(!res || !is_fixed_x || is_fixed_res_x);
          ASSERT_TRUE(!res || !is_fixed_y || is_fixed_res_y);
          ASSERT_TRUE(!res || !is_fixed_z || is_fixed_res_z);

          if (res && is_fixed_x && is_fixed_y)
          {
            ASSERT_TRUE(is_fixed_res_z);
            ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
            ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_z));
            tmp = bzla_bv_urem(d_mm, d_x->lo, d_y->lo);
            if (!bzla_bv_compare(tmp, d_z->lo))
            {
              ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
              ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
              bzla_bv_free(d_mm, tmp);
              tmp = bzla_bv_urem(d_mm, d_x->lo, d_y->lo);
              ASSERT_FALSE(bzla_bv_compare(tmp, res_z->lo));
            }
            bzla_bv_free(d_mm, tmp);
          }

          if (res && is_fixed_x && is_fixed_z)
          {
            ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
            ASSERT_FALSE(bzla_bv_compare(d_z->lo, res_z->lo));
            if (bzla_bvdomain_is_fixed(d_mm, res_y))
            {
              tmp = bzla_bv_urem(d_mm, d_x->lo, res_y->lo);
              ASSERT_FALSE(bzla_bv_compare(tmp, d_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
          }

          if (res && is_fixed_y && is_fixed_z)
          {
            ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
            ASSERT_FALSE(bzla_bv_compare(d_z->lo, res_z->lo));
            if (bzla_bvdomain_is_fixed(d_mm, res_x))
            {
              tmp = bzla_bv_urem(d_mm, res_x->lo, d_y->lo);
              ASSERT_FALSE(bzla_bv_compare(tmp, d_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
          }

          bzla_bvdomain_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvdomain_free(d_mm, d_x);
      }
      bzla_bvdomain_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  /* In these ult cases, the AIG layer is better in propagating const bits
   * than the domain propagators. For now we thus expect this to fail. */
  bool ult_expect_fail(BzlaBvDomain *d_x, BzlaBvDomain *d_y, BzlaBvDomain *d_z)
  {
    bool res     = false;
    char *char_x = 0, *char_y = 0, *char_z = 0;

    char_z = bzla_bvdomain_to_char(d_mm, d_z);
    char_x = bzla_bvdomain_to_char(d_mm, d_x);
    char_y = bzla_bvdomain_to_char(d_mm, d_y);

    std::string str_z = char_z;
    std::string str_x = char_x;
    std::string str_y = char_y;

    if (str_z == "x")
    {
      if (str_x == "1")
      {
        if (str_y == "x")
        {
          res = true;
        }
      }
      else if (str_x == "01")
      {
        if (str_y == "0x" || str_y == "1x")
        {
          res = true;
        }
      }
      else if (str_x == "0x")
      {
        if (str_y == "1x")
        {
          res = true;
        }
      }
      else if (str_x == "1x")
      {
        if (str_y == "0x" || str_y == "x0")
        {
          res = true;
        }
      }
      else if (str_x == "10")
      {
        if (str_y == "0x" || str_y == "x0")
        {
          res = true;
        }
      }
      else if (str_x == "11")
      {
        if (str_y == "0x" || str_y == "1x" || str_y == "x0" || str_y == "x1"
            || str_y == "xx")
        {
          res = true;
        }
      }
      else if (str_x == "x1")
      {
        if (str_y == "01" || str_y == "0x")
        {
          res = true;
        }
      }
      else if (str_x == "001")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "10x" || str_y == "1xx"
            || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "00x")
      {
        if (str_y == "01x" || str_y == "10x" || str_y == "1xx"
            || str_y == "x1x")
        {
          res = true;
        }
      }
      else if (str_x == "010")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx")
        {
          res = true;
        }
      }
      else if (str_x == "011")
      {
        if (str_y == "00x" || str_y == "01x" || str_y == "0x0" || str_y == "0x1"
            || str_y == "0xx" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx")
        {
          res = true;
        }
      }
      else if (str_x == "01x")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx")
        {
          res = true;
        }
      }
      else if (str_x == "0x0")
      {
        if (str_y == "10x" || str_y == "1x0" || str_y == "1xx")
        {
          res = true;
        }
      }
      else if (str_x == "0x1")
      {
        if (str_y == "001" || str_y == "00x" || str_y == "10x" || str_y == "1x0"
            || str_y == "1xx")
        {
          res = true;
        }
      }
      else if (str_x == "0xx")
      {
        if (str_y == "10x" || str_y == "1x0" || str_y == "1xx")
        {
          res = true;
        }
      }
      else if (str_x == "100")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0xx"
            || str_y == "x00")
        {
          res = true;
        }
      }
      else if (str_x == "101")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0xx" || str_y == "10x"
            || str_y == "11x" || str_y == "x00" || str_y == "x01"
            || str_y == "x0x")
        {
          res = true;
        }
      }
      else if (str_x == "10x")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0xx" || str_y == "11x"
            || str_y == "x00")
        {
          res = true;
        }
      }
      else if (str_x == "110")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0xx" || str_y == "10x"
            || str_y == "1x0" || str_y == "x00" || str_y == "x01"
            || str_y == "x0x" || str_y == "x10" || str_y == "xx0")
        {
          res = true;
        }
      }
      else if (str_x == "111")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0xx" || str_y == "10x"
            || str_y == "11x" || str_y == "1x0" || str_y == "1x1"
            || str_y == "1xx" || str_y == "x00" || str_y == "x01"
            || str_y == "x0x" || str_y == "x10" || str_y == "x11"
            || str_y == "x1x" || str_y == "xx0" || str_y == "xx1"
            || str_y == "xxx")
        {
          res = true;
        }
      }
      else if (str_x == "11x")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0xx" || str_y == "10x"
            || str_y == "1x0" || str_y == "x00" || str_y == "x01"
            || str_y == "x0x" || str_y == "x10" || str_y == "xx0")
        {
          res = true;
        }
      }
      else if (str_x == "1x0")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0xx"
            || str_y == "x00")
        {
          res = true;
        }
      }
      else if (str_x == "1x1")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0xx" || str_y == "101"
            || str_y == "10x" || str_y == "x00" || str_y == "x01"
            || str_y == "x0x")
        {
          res = true;
        }
      }
      else if (str_x == "1xx")
      {
        if (str_y == "00x" || str_y == "0x0" || str_y == "0xx"
            || str_y == "x00")
        {
          res = true;
        }
      }
      else if (str_x == "x01")
      {
        if (str_y == "001" || str_y == "00x" || str_y == "11x")
        {
          res = true;
        }
      }
      else if (str_x == "x0x")
      {
        if (str_y == "11x")
        {
          res = true;
        }
      }
      else if (str_x == "x10")
      {
        if (str_y == "001" || str_y == "00x" || str_y == "010"
            || str_y == "0x0")
        {
          res = true;
        }
      }
      else if (str_x == "x11")
      {
        if (str_y == "001" || str_y == "00x" || str_y == "010" || str_y == "011"
            || str_y == "01x" || str_y == "0x0" || str_y == "0x1"
            || str_y == "0xx")
        {
          res = true;
        }
      }
      else if (str_x == "x1x")
      {
        if (str_y == "001" || str_y == "00x" || str_y == "010"
            || str_y == "0x0")
        {
          res = true;
        }
      }
      else if (str_x == "xx1")
      {
        if (str_y == "001" || str_y == "00x")
        {
          res = true;
        }
      }
    }

    bzla_mem_freestr(d_mm, char_x);
    bzla_mem_freestr(d_mm, char_y);
    bzla_mem_freestr(d_mm, char_z);
    return res;
  }

  void test_ult(uint32_t bw)
  {
    bool res, expect_fail;
    uint32_t num_consts, num_consts_z;
    char **consts, **consts_z;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_x, *d_y, *d_z;
    BzlaBvDomain *res_x, *res_y, *res_z;

    num_consts   = generate_consts(bw, &consts);
    num_consts_z = generate_consts(1, &consts_z);

    for (uint32_t i = 0; i < num_consts_z; i++)
    {
      d_z = bzla_bvdomain_new_from_char(d_mm, consts_z[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = bzla_bvdomain_new_from_char(d_mm, consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = bzla_bvdomain_new_from_char(d_mm, consts[k]);

          res = bzla_bvprop_ult(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    2,
                    false,
                    BITWUZLA_KIND_BV_ULT,
                    0,
                    0,
                    res);
          if (res)
          {
            expect_fail = ult_expect_fail(d_x, d_y, d_z);
            check_synth(
                d_x, d_y, d_z, 0, res_z, TEST_BVPROP_ULT, 0, 0, expect_fail);
          }

          if (bzla_bvdomain_is_fixed(d_mm, d_x)
              && bzla_bvdomain_is_fixed(d_mm, d_y))
          {
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_x));
            ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_ult(d_mm, res_x->lo, res_y->lo);
              ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
              ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
              ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_z));
              ASSERT_FALSE(bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvdomain_is_fixed(d_mm, d_z))
            {
              ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, res_z));
              tmp = bzla_bv_ult(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                ASSERT_FALSE(bzla_bv_compare(d_x->lo, res_x->lo));
                ASSERT_FALSE(bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bzla_bv_ult(d_mm, res_x->lo, res_y->lo);
                ASSERT_FALSE(bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }
          bzla_bvdomain_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvdomain_free(d_mm, d_x);
      }
      bzla_bvdomain_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
    free_consts(1, num_consts_z, consts_z);
  }

  Bzla *d_bzla           = nullptr;
  BzlaAIGVecMgr *d_avmgr = nullptr;

 private:
  void check_concat_result(BzlaBvDomain *d_x,
                           BzlaBvDomain *d_y,
                           BzlaBvDomain *d_z)
  {
    assert(bzla_bvdomain_is_valid(d_mm, d_x));
    assert(bzla_bvdomain_is_valid(d_mm, d_y));
    assert(bzla_bvdomain_is_valid(d_mm, d_z));

    size_t i, len_x, len_y;
    char *str_x = from_domain(d_mm, d_x);
    char *str_y = from_domain(d_mm, d_y);
    char *str_z = from_domain(d_mm, d_z);
    ASSERT_EQ(strlen(str_x) + strlen(str_y), strlen(str_z));

    for (i = 0, len_x = strlen(str_x); i < len_x; i++)
    {
      ASSERT_EQ(str_x[i], str_z[i]);
    }
    for (i = 0, len_y = strlen(str_y); i < len_y; i++)
    {
      ASSERT_EQ(str_y[i], str_z[i + len_x]);
    }
    bzla_mem_freestr(d_mm, str_x);
    bzla_mem_freestr(d_mm, str_y);
    bzla_mem_freestr(d_mm, str_z);
  }
};

TEST_F(TestBvProp, eq)
{
  test_eq(1);
  test_eq(2);
  test_eq(3);
}

TEST_F(TestBvProp, not )
{
  test_not(1);
  test_not(2);
  test_not(3);
}

TEST_F(TestBvProp, sll_const)
{
  test_sll_const(1);
  test_sll_const(2);
  test_sll_const(3);
}

TEST_F(TestBvProp, srl_const)
{
  test_srl_const(1);
  test_srl_const(2);
  test_srl_const(3);
}

TEST_F(TestBvProp, sll)
{
  test_sll(2);
#if TEST_BVPROP_THREE_BITS
  test_sll(3);
#endif
}

TEST_F(TestBvProp, srl)
{
  test_srl(2);
#if TEST_BVPROP_THREE_BITS
  test_srl(3);
#endif
}

TEST_F(TestBvProp, and)
{
  test_and(1);
  test_and(2);
#if TEST_BVPROP_THREE_BITS
  test_and(3);
#endif
}

TEST_F(TestBvProp, or)
{
  test_or(1);
  test_or(2);
#if TEST_BVPROP_THREE_BITS
  test_or(3);
#endif
}

TEST_F(TestBvProp, xor)
{
  test_xor(1);
  test_xor(2);
#if TEST_BVPROP_THREE_BITS
  test_xor(3);
#endif
}

TEST_F(TestBvProp, slice)
{
  test_slice(1);
  test_slice(2);
  test_slice(3);
}

TEST_F(TestBvProp, concat)
{
  test_concat(1);
  test_concat(2);
  test_concat(3);
}

TEST_F(TestBvProp, add)
{
  test_add(1, false);
  test_add(2, false);
#if TEST_BVPROP_THREE_BITS
  test_add(3, false);
#endif
  test_add(1, true);
  test_add(2, true);
#if TEST_BVPROP_THREE_BITS
  test_add(3, true);
#endif
}

TEST_F(TestBvProp, sext)
{
  test_sext(1);
  test_sext(2);
  test_sext(3);
}

TEST_F(TestBvProp, cond)
{
  test_cond(1);
  test_cond(2);
#if TEST_BVPROP_THREE_BITS
  test_cond(3);
#endif
}

TEST_F(TestBvProp, mul)
{
  test_mul(1, false);
  test_mul(2, false);
#if TEST_BVPROP_THREE_BITS
  test_mul(3, false);
#endif
  test_mul(1, true);
  test_mul(2, true);
#if TEST_BVPROP_THREE_BITS
  test_mul(3, true);
#endif
}

TEST_F(TestBvProp, ult)
{
  test_ult(1);
  test_ult(2);
  test_ult(3);
}

TEST_F(TestBvProp, udiv)
{
  test_udiv(1);
  test_udiv(2);
#if TEST_BVPROP_THREE_BITS
  test_udiv(3);
#endif
}

TEST_F(TestBvProp, urem)
{
  test_urem(1);
  test_urem(2);
#if TEST_BVPROP_THREE_BITS
  test_urem(3);
#endif
}
