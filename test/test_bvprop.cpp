/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2018-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "bzlaaigvec.h"
#include "bzlabvprop.h"
#include "utils/bzlamem.h"
#include "utils/bzlautil.h"
}

#define TEST_BVPROP_RELEASE_D_XZ \
  do                             \
  {                              \
    bzla_bvprop_free(d_mm, d_x); \
    bzla_bvprop_free(d_mm, d_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_RES_XZ \
  do                               \
  {                                \
    bzla_bvprop_free(d_mm, res_x); \
    bzla_bvprop_free(d_mm, res_z); \
  } while (0)

#define TEST_BVPROP_RELEASE_D_XYZ \
  do                              \
  {                               \
    bzla_bvprop_free(d_mm, d_x);  \
    bzla_bvprop_free(d_mm, d_y);  \
    bzla_bvprop_free(d_mm, d_z);  \
  } while (0)

#define TEST_BVPROP_RELEASE_RES_XYZ \
  do                                \
  {                                 \
    bzla_bvprop_free(d_mm, res_x);  \
    bzla_bvprop_free(d_mm, res_y);  \
    bzla_bvprop_free(d_mm, res_z);  \
  } while (0)

#define TEST_PROPBV_CONCAT                                                 \
  do                                                                       \
  {                                                                        \
    res = bzla_bvprop_concat(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z); \
    assert(res || !is_valid(d_mm, res_x, res_y, res_z, 0));                \
    check_sat(d_x,                                                         \
              d_y,                                                         \
              d_z,                                                         \
              0,                                                           \
              res_x,                                                       \
              res_y,                                                       \
              res_z,                                                       \
              0,                                                           \
              0,                                                           \
              boolector_concat,                                            \
              0,                                                           \
              0,                                                           \
              0,                                                           \
              0,                                                           \
              false, /* not compositional but eq always returns true */    \
              res);                                                        \
    assert(!bzla_bvprop_is_fixed(d_mm, d_x)                                \
           || !bzla_bv_compare(d_x->lo, res_x->lo));                       \
    assert(!bzla_bvprop_is_fixed(d_mm, d_y)                                \
           || !bzla_bv_compare(d_y->lo, res_y->lo));                       \
    assert(!bzla_bvprop_is_fixed(d_mm, d_z)                                \
           || !bzla_bv_compare(d_z->lo, res_z->lo));                       \
    check_concat(res_x, res_y, res_z);                                     \
    assert(bzla_bvprop_is_valid(d_mm, res_x));                             \
    assert(bzla_bvprop_is_valid(d_mm, res_y));                             \
    assert(bzla_bvprop_is_valid(d_mm, res_z));                             \
    assert(!bzla_bvprop_is_fixed(d_mm, d_x)                                \
           || bzla_bvprop_is_fixed(d_mm, res_x));                          \
    assert(!bzla_bvprop_is_fixed(d_mm, d_y)                                \
           || bzla_bvprop_is_fixed(d_mm, res_y));                          \
    assert(!bzla_bvprop_is_fixed(d_mm, d_z)                                \
           || (bzla_bvprop_is_fixed(d_mm, res_x)                           \
               && bzla_bvprop_is_fixed(d_mm, res_y)                        \
               && bzla_bvprop_is_fixed(d_mm, res_z)));                     \
    TEST_BVPROP_RELEASE_D_XYZ;                                             \
    TEST_BVPROP_RELEASE_RES_XYZ;                                           \
  } while (0)

class TestBvProp : public TestMm
{
 protected:
  enum BvPropOp
  {
    TEST_BVPROP_ADD,
    TEST_BVPROP_AND,
    TEST_BVPROP_CONCAT,
    TEST_BVPROP_EQ,
    TEST_BVPROP_ITE,
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

  static constexpr uint32_t TEST_BW         = 3;
  static constexpr uint32_t TEST_NUM_CONSTS = 27;
  static constexpr uint32_t TEST_CONST_LEN  = (TEST_BW + 1);

  void SetUp() override
  {
    TestMm::SetUp();
    d_bzla  = bzla_new();
    d_avmgr = bzla_aigvec_mgr_new(d_bzla);
  }

  void TearDown() override
  {
    bzla_aigvec_mgr_delete(d_avmgr);
    bzla_delete(d_bzla);
    TestMm::TearDown();
  }

  /* Initialize all possible values for 3-valued constants of bit-width bw */
  uint32_t generate_consts(uint32_t bw, char ***res)
  {
    assert(bw);
    assert(res);

    uint32_t psize, num_consts = 1;
    char bit = '0';

    for (uint32_t i = 0; i < bw; i++) num_consts *= 3;
    psize = num_consts;

    BZLA_NEWN(d_mm, *res, num_consts);
    for (uint32_t i = 0; i < num_consts; i++)
      BZLA_CNEWN(d_mm, (*res)[i], bw + 1);

    for (uint32_t i = 0; i < bw; i++)
    {
      psize = psize / 3;
      for (uint32_t j = 0; j < num_consts; j++)
      {
        (*res)[j][i] = bit;
        if ((j + 1) % psize == 0)
        {
          bit = bit == '0' ? '1' : (bit == '1' ? 'x' : '0');
        }
      }
    }
    return num_consts;
  }

  void free_consts(uint32_t bw, uint32_t num_consts, char **consts)
  {
    assert(bw);
    assert(consts);
    for (uint32_t i = 0; i < num_consts; i++)
      BZLA_DELETEN(d_mm, consts[i], bw + 1);
    BZLA_DELETEN(d_mm, consts, num_consts);
  }

  void to_str(BzlaBvDomain *d, char **res_lo, char **res_hi, bool print_short)
  {
    assert(d);
    assert(bzla_bv_get_width(d->lo) == bzla_bv_get_width(d->hi));

    if (print_short)
    {
      assert(res_lo);
      char *lo = bzla_bv_to_char(d_mm, d->lo);
      char *hi = bzla_bv_to_char(d_mm, d->hi);
      for (size_t i = 0, len = strlen(lo); i < len; i++)
      {
        if (lo[i] != hi[i])
        {
          if (lo[i] == '0' && hi[i] == '1')
          {
            lo[i] = 'x';
          }
          else
          {
            assert(lo[i] == '1' && hi[i] == '0');
            lo[i] = '?';
          }
        }
      }
      bzla_mem_freestr(d_mm, hi);
      *res_lo = lo;
      if (res_hi) *res_hi = 0;
    }
    else
    {
      assert(res_hi);
      *res_lo = bzla_bv_to_char(d_mm, d->lo);
      *res_hi = bzla_bv_to_char(d_mm, d->hi);
    }
  }

  void print_domain(BzlaBvDomain *d, bool print_short)
  {
    bzla_bvprop_print(d_mm, d, print_short);
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

  /* Create 2-valued bit-vector from 3-valued bit-vector 'bv' by initializing
   * 'x' values to 'bit'. */
  BzlaBitVector *to_bv(const char *c, char bit)
  {
    size_t len = strlen(c);
    char buf[len + 1];
    buf[len] = '\0';
    for (size_t i = 0; i < len; i++)
    {
      buf[i] = (c[i] == 'x') ? bit : c[i];
    }
    return bzla_bv_char_to_bv(d_mm, buf);
  }

  bool is_xxx_domain(BzlaMemMgr *mm, BzlaBvDomain *d)
  {
    assert(mm);
    assert(d);
    char *str_d = from_domain(mm, d);
    bool res    = strchr(str_d, '1') == NULL && strchr(str_d, '0') == NULL;
    bzla_mem_freestr(mm, str_d);
    return res;
  }

  bool is_valid(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain *d_c)
  {
    return (!d_x || bzla_bvprop_is_valid(mm, d_x))
           && (!d_y || bzla_bvprop_is_valid(mm, d_y))
           && (!d_z || bzla_bvprop_is_valid(mm, d_z))
           && (!d_c || bzla_bvprop_is_valid(mm, d_c));
  }

  bool is_fixed(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain *d_c)
  {
    return (!d_x || bzla_bvprop_is_fixed(mm, d_x))
           && (!d_y || bzla_bvprop_is_fixed(mm, d_y))
           && (!d_z || bzla_bvprop_is_fixed(mm, d_z))
           && (!d_c || bzla_bvprop_is_fixed(mm, d_c));
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

  /* Create hi for domain from 3-valued bit-vector 'bv'. */
  BzlaBitVector *to_hi(const char *bv) { return to_bv(bv, '1'); }

  /* Create lo for domain from 3-valued bit-vector 'bv'. */
  BzlaBitVector *to_lo(const char *bv) { return to_bv(bv, '0'); }

  /* Create domain from 3-valued bit-vector 'bv'. */
  BzlaBvDomain *create_domain(const char *bv)
  {
    BzlaBitVector *lo = to_lo(bv);
    BzlaBitVector *hi = to_hi(bv);
    BzlaBvDomain *res = bzla_bvprop_new(d_mm, lo, hi);
    bzla_bv_free(d_mm, lo);
    bzla_bv_free(d_mm, hi);
    return res;
  }

  /* Create 3-valued bit-vector from domain 'd'. */
  char *from_domain(BzlaMemMgr *mm, BzlaBvDomain *d)
  {
    assert(bzla_bvprop_is_valid(mm, d));
    char *lo = bzla_bv_to_char(mm, d->lo);
    char *hi = bzla_bv_to_char(mm, d->hi);

    size_t len = strlen(lo);
    for (size_t i = 0; i < len; i++)
    {
      if (lo[i] != hi[i])
      {
        /* lo[i] == '1' && hi[i] == '0' would be an invalid domain. */
        assert(lo[i] == '0');
        assert(hi[i] == '1');
        lo[i] = 'x';
      }
    }
    bzla_mem_freestr(mm, hi);
    return lo;
  }

#if 0
  bool check_const_bits (BzlaBvDomain *d, const char *expected)
  {
    assert (bzla_bvprop_is_valid (d_mm, d));
    size_t len = strlen (expected);
    uint32_t bit_lo, bit_hi;
    bool res = true;

    for (size_t i = 0; i < len && res; i++)
    {
      bit_lo = bzla_bv_get_bit (d->lo, len - 1 - i);
      bit_hi = bzla_bv_get_bit (d->hi, len - 1 - i);
      if (expected[i] == 'x')
      {
        res &= bit_lo != bit_hi;
      }
      else
      {
        res &= bit_lo == bit_hi;
      }
    }
    return res;
  }
#endif

  bool check_not(BzlaBvDomain *d_x, BzlaBvDomain *d_z)
  {
    assert(bzla_bvprop_is_valid(d_mm, d_x));
    assert(bzla_bvprop_is_valid(d_mm, d_z));
    bool res    = true;
    char *str_x = from_domain(d_mm, d_x);
    char *str_z = from_domain(d_mm, d_z);
    assert(strlen(str_x) == strlen(str_z));

    size_t len = strlen(str_x);
    for (size_t i = 0; i < len; i++)
    {
      assert(str_x[i] != 'x' || str_z[i] == 'x');
      assert(str_x[i] != '0' || str_z[i] == '1');
      assert(str_x[i] != '1' || str_z[i] == '0');
      assert(str_z[i] != '0' || str_x[i] == '1');
      assert(str_z[i] != '1' || str_x[i] == '0');
    }
    bzla_mem_freestr(d_mm, str_x);
    bzla_mem_freestr(d_mm, str_z);
    return res;
  }

  void check_sll_const(BzlaBvDomain *d_x, BzlaBvDomain *d_z, uint32_t n)
  {
    assert(bzla_bvprop_is_valid(d_mm, d_x));
    assert(bzla_bvprop_is_valid(d_mm, d_z));
    char *str_x = from_domain(d_mm, d_x);
    char *str_z = from_domain(d_mm, d_z);
    assert(strlen(str_x) == strlen(str_z));

    for (size_t i = 0, len = strlen(str_x); i < len; i++)
    {
      assert(i >= n || str_z[len - 1 - i] == '0');
      assert(i < n || str_z[len - 1 - i] == str_x[len - 1 - i + n]);
    }
    bzla_mem_freestr(d_mm, str_x);
    bzla_mem_freestr(d_mm, str_z);
  }

  void check_srl_const(BzlaBvDomain *d_x, BzlaBvDomain *d_z, uint32_t n)
  {
    assert(bzla_bvprop_is_valid(d_mm, d_x));
    assert(bzla_bvprop_is_valid(d_mm, d_z));
    char *str_x = from_domain(d_mm, d_x);
    char *str_z = from_domain(d_mm, d_z);
    assert(strlen(str_x) == strlen(str_z));

    for (size_t i = 0, len = strlen(str_x); i < len; i++)
    {
      assert(i >= n || str_z[i] == '0');
      assert(i < n || str_z[i] == str_x[i - n]);
    }
    bzla_mem_freestr(d_mm, str_x);
    bzla_mem_freestr(d_mm, str_z);
  }

  void check_concat(BzlaBvDomain *d_x, BzlaBvDomain *d_y, BzlaBvDomain *d_z)
  {
    assert(bzla_bvprop_is_valid(d_mm, d_x));
    assert(bzla_bvprop_is_valid(d_mm, d_y));
    assert(bzla_bvprop_is_valid(d_mm, d_z));
    size_t i, len_x, len_y;
    char *str_x = from_domain(d_mm, d_x);
    char *str_y = from_domain(d_mm, d_y);
    char *str_z = from_domain(d_mm, d_z);
    assert(strlen(str_x) + strlen(str_y) == strlen(str_z));

    for (i = 0, len_x = strlen(str_x); i < len_x; i++)
    {
      assert(str_x[i] == str_z[i]);
    }
    for (i = 0, len_y = strlen(str_y); i < len_y; i++)
    {
      assert(str_y[i] == str_z[i + len_x]);
    }
    bzla_mem_freestr(d_mm, str_x);
    bzla_mem_freestr(d_mm, str_y);
    bzla_mem_freestr(d_mm, str_z);
  }

  void check_sext(BzlaBvDomain *d_x, BzlaBvDomain *d_z)
  {
    if (bzla_bvprop_is_valid(d_mm, d_x) && bzla_bvprop_is_valid(d_mm, d_z))
    {
      size_t i, len_x, len_z, n;
      char *str_x = from_domain(d_mm, d_x);
      char *str_z = from_domain(d_mm, d_z);

      len_x = strlen(str_x);
      len_z = strlen(str_z);
      n     = len_z - len_x;

      for (i = 0; i < n; i++) assert(str_z[i] == str_x[0]);
      for (i = 0; i < len_x; i++) assert(str_z[i + n] == str_x[i]);

      bzla_mem_freestr(d_mm, str_x);
      bzla_mem_freestr(d_mm, str_z);
    }
  }

  void check_ite(BzlaBvDomain *d_x,
                 BzlaBvDomain *d_y,
                 BzlaBvDomain *d_z,
                 BzlaBvDomain *d_c)
  {
    assert(bzla_bv_get_width(d_c->lo) == 1);
    assert(bzla_bv_get_width(d_c->hi) == 1);
    assert(bzla_bvprop_is_valid(d_mm, d_x));
    assert(bzla_bvprop_is_valid(d_mm, d_y));
    assert(bzla_bvprop_is_valid(d_mm, d_z));
    assert(bzla_bvprop_is_valid(d_mm, d_c));

    char *str_x = from_domain(d_mm, d_x);
    char *str_y = from_domain(d_mm, d_y);
    char *str_z = from_domain(d_mm, d_z);
    char *str_c = from_domain(d_mm, d_c);

    if (str_c[0] == '0')
    {
      assert(!strcmp(str_z, str_y));
    }
    else if (str_c[0] == '1')
    {
      assert(!strcmp(str_z, str_x));
    }
    else
    {
      size_t len = strlen(str_x);
      assert(len == strlen(str_y));
      assert(len == strlen(str_z));

      if (strcmp(str_z, str_x) && strcmp(str_z, str_y))
      {
        for (size_t i = 0; i < len; i++)
        {
          assert(
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

  bool check_synth(BzlaBvDomain *d_x,
                   BzlaBvDomain *d_y,
                   BzlaBvDomain *d_z,
                   BzlaBvDomain *d_c,
                   BzlaBvDomain *res_z,
                   BvPropOp op,
                   uint32_t upper,
                   uint32_t lower)
  {
    BzlaAIGVec *av_x = 0, *av_y = 0, *av_c = 0, *av_res = 0;

    if (bzla_bvprop_has_fixed_bits(d_mm, d_z))
    {
      return true;
    }
    if ((op == TEST_BVPROP_SLL || op == TEST_BVPROP_SRL)
        && (!bzla_util_is_power_of_2(bzla_bv_get_width(d_x->lo))
            || bzla_util_log_2(bzla_bv_get_width(d_x->lo))
                   != bzla_bv_get_width(d_y->lo)))
    {
      return true;
    }

    char *str_res_z = from_domain(d_mm, res_z);
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
        assert(op == TEST_BVPROP_ITE);
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

    bzla_aigvec_release_delete(d_avmgr, av_res);
    bzla_mem_freestr(d_mm, str_res_z);

    return result;
  }

  void check_sat_fix_bits(Bzla *bzla, BoolectorNode *var, const char bits[])
  {
    assert(bzla);
    assert(var);
    assert(bits);

    uint32_t idx;
    uint32_t w = boolector_get_width(bzla, var);
    BoolectorNode *eq, *slice, *one, *zero;

    assert(w == strlen(bits));

    one  = boolector_const(bzla, "1");
    zero = boolector_const(bzla, "0");
    for (size_t i = 0; i < w; i++)
    {
      idx = w - i - 1;
      if (bits[i] != 'x')
      {
        slice = boolector_slice(bzla, var, idx, idx);
        eq    = boolector_eq(bzla, slice, bits[i] == '1' ? one : zero);
        boolector_assert(bzla, eq);
        boolector_release(bzla, eq);
        boolector_release(bzla, slice);
      }
    }
    boolector_release(bzla, one);
    boolector_release(bzla, zero);
  }

  void check_sat(
      BzlaBvDomain *d_x,
      BzlaBvDomain *d_y,
      BzlaBvDomain *d_z,
      BzlaBvDomain *d_c,
      BzlaBvDomain *res_x,
      BzlaBvDomain *res_y,
      BzlaBvDomain *res_z,
      BzlaBvDomain *res_c,
      BoolectorNode *(*unfun)(Bzla *, BoolectorNode *),
      BoolectorNode *(*binfun)(Bzla *, BoolectorNode *, BoolectorNode *),
      BoolectorNode *(*binofun)(Bzla *, BoolectorNode *, BoolectorNode *),
      BoolectorNode *(*extfun)(Bzla *, BoolectorNode *, uint32_t),
      uint32_t hi,
      uint32_t lo,
      bool decompositional,
      bool valid)
  {
    assert(d_x);
    assert(d_z);
    assert(res_x);
    assert(res_z);
    assert(!d_c || (!unfun && !binfun && !extfun));
    assert(!d_y || d_c || binfun || extfun);
    assert(!extfun || hi);
    assert(!binofun || binfun);

    int32_t sat_res;
    uint32_t bwx, bwy, bwz;
    char *str_x, *str_y, *str_z, *str_c;
#if 0
    char *str_res_x, *str_res_y, *str_res_z, *str_res_c;
#endif
    Bzla *bzla;
    BoolectorNode *x, *y, *z, *c, *fun, *ofun, *_not, *eq;
    BoolectorSort swx, swy, swz, s1;

    str_x = from_domain(d_mm, d_x);
    str_y = 0;
    str_z = from_domain(d_mm, d_z);
    str_c = 0;
#if 0
    str_res_x = str_res_y = str_res_c = str_res_z = 0;
#endif

    bzla = boolector_new();
    boolector_set_opt(bzla, BZLA_OPT_MODEL_GEN, 1);
    boolector_set_opt(bzla, BZLA_OPT_INCREMENTAL, 1);
    bwx = bzla_bv_get_width(d_x->lo);
    swx = boolector_bitvec_sort(bzla, bwx);
    bwz = bzla_bv_get_width(d_z->lo);
    swz = boolector_bitvec_sort(bzla, bwz);
    s1  = boolector_bitvec_sort(bzla, 1);
    x   = boolector_var(bzla, swx, "x");
    z   = boolector_var(bzla, swz, "z");
    y   = 0;
    c   = 0;

    if (d_y)
    {
      str_y = from_domain(d_mm, d_y);
      bwy   = bzla_bv_get_width(d_y->lo);
      swy   = boolector_bitvec_sort(bzla, bwy);
      y     = boolector_var(bzla, swy, "y");
    }

    if (d_c)
    {
      assert(y);
      str_c = from_domain(d_mm, d_c);
      c     = boolector_var(bzla, s1, "c");
      fun   = boolector_cond(bzla, c, x, y);
    }
    else if (unfun)
    {
      assert(!binfun && !extfun);
      fun = unfun(bzla, x);
    }
    else if (binfun)
    {
      assert(y);
      assert(!unfun && !extfun);
      fun = binfun(bzla, x, y);
      if (binofun)
      {
        ofun = binofun(bzla, x, y);
        _not = boolector_not(bzla, ofun);
        boolector_assert(bzla, _not);
        boolector_release(bzla, _not);
        boolector_release(bzla, ofun);
      }
    }
    else if (extfun)
    {
      assert(!unfun && !binfun);
      fun = extfun(bzla, x, hi);
    }
    else
    {
      fun = boolector_slice(bzla, x, hi, lo);
    }
    eq = boolector_eq(bzla, fun, z);
    boolector_assert(bzla, eq);
    boolector_release(bzla, fun);
    boolector_release(bzla, eq);

    boolector_push(bzla, 1);
    check_sat_fix_bits(bzla, x, str_x);
    if (str_y)
    {
      check_sat_fix_bits(bzla, y, str_y);
    }
    check_sat_fix_bits(bzla, z, str_z);
    if (str_c)
    {
      check_sat_fix_bits(bzla, c, str_c);
    }

    // boolector_dump_smt2 (bzla, stdout);
    sat_res = boolector_sat(bzla);
    boolector_pop(bzla, 1);

    assert(sat_res != BZLA_RESULT_SAT
           || (valid && is_valid(d_mm, res_x, res_y, res_z, res_c)));
    assert(sat_res != BZLA_RESULT_UNSAT
           || ((decompositional
                || (!valid && !is_valid(d_mm, res_x, res_y, res_z, res_c)))
               && (!decompositional || !valid
                   || !is_fixed(d_mm, res_x, res_y, res_z, res_c))));

    /* Check correctness of results res_* for valid domains. */
#if 0
    if (valid)
    {
      str_res_x = from_domain (d_mm, res_x);
      str_res_z = from_domain (d_mm, res_z);
      if (res_y)
      {
        str_res_y = from_domain (d_mm, res_y);
      }
      if (res_c)
      {
        str_res_c = from_domain (d_mm, res_c);
      }
      boolector_push (bzla, 1);
      check_sat_fix_bits (bzla, x, str_res_x);
      if (str_res_y)
      {
        check_sat_fix_bits (bzla, y, str_res_y);
      }
      check_sat_fix_bits (bzla, z, str_res_z);
      if (str_res_c)
      {
        check_sat_fix_bits (bzla, c, str_res_c);
      }
      sat_res = boolector_sat (bzla);
      if (sat_res != BZLA_RESULT_SAT)
      {
        printf ("\n");
        printf ("x: ");
        print_domain (d_x, true);
        if (d_y)
        {
          printf ("y: ");
          print_domain (d_y, true);
        }
        if (d_c)
        {
          printf ("c: ");
          print_domain (d_c, true);
        }
        printf ("z: ");
        print_domain (d_z, true);
        printf ("x': ");
        print_domain (res_x, true);
        if (res_y)
        {
          printf ("y': ");
          print_domain (res_y, true);
        }
        if (res_c)
        {
          printf ("c': ");
          print_domain (res_c, true);
        }
        printf ("z': ");
        print_domain (res_z, true);
      }
      assert (sat_res == BZLA_RESULT_SAT);
      boolector_pop (bzla, 1);
      bzla_mem_freestr (d_mm, str_res_x);
      bzla_mem_freestr (d_mm, str_res_z);
      if (str_res_y)
      {
        bzla_mem_freestr (d_mm, str_res_y);
      }
      if (str_res_c)
      {
        bzla_mem_freestr (d_mm, str_res_c);
      }
    }
#endif

    // printf ("sat_res %d\n", sat_res);
    // if (sat_res == BOOLECTOR_SAT)
    //{
    //  boolector_print_model (bzla, "btor", stdout);
    //}

    boolector_release(bzla, x);
    if (c) boolector_release(bzla, c);
    if (y) boolector_release(bzla, y);
    boolector_release(bzla, z);
    boolector_release_sort(bzla, swx);
    if (y) boolector_release_sort(bzla, swy);
    boolector_release_sort(bzla, swz);
    boolector_release_sort(bzla, s1);
    boolector_delete(bzla);
    bzla_mem_freestr(d_mm, str_x);
    if (str_c) bzla_mem_freestr(d_mm, str_c);
    if (str_y) bzla_mem_freestr(d_mm, str_y);
    bzla_mem_freestr(d_mm, str_z);
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
      d_z = create_domain(consts[i]);
      for (j = 0; j < num_consts; j++)
      {
        d_x = create_domain(consts[j]);

        for (n = 0; n < bw + 1; n++)
        {
          bv_n = bzla_bv_uint64_to_bv(d_mm, n, bw);
          d_y  = bzla_bvprop_new(d_mm, bv_n, bv_n);
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
                      0,
                      boolector_srl,
                      0,
                      0,
                      0,
                      0,
                      false,
                      res);
            assert(
                !res
                || check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_SRL, 0, 0));
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
                      0,
                      boolector_sll,
                      0,
                      0,
                      0,
                      0,
                      false,
                      res);
            assert(
                !res
                || check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_SLL, 0, 0));
          }
          assert(res || !is_valid(d_mm, res_x, 0, res_z, 0));

          assert(!bzla_bvprop_is_fixed(d_mm, d_x)
                 || !bzla_bvprop_is_valid(d_mm, res_x)
                 || !bzla_bv_compare(d_x->lo, res_x->lo));
          assert(!res || !bzla_bvprop_is_fixed(d_mm, d_z)
                 || !bzla_bvprop_is_valid(d_mm, res_z)
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
          bzla_bvprop_free(d_mm, d_y);
        }
        bzla_bvprop_free(d_mm, d_x);
      }
      bzla_bvprop_free(d_mm, d_z);
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
      d_z = create_domain(consts[i]);
      for (j = 0; j < num_consts; j++)
      {
        d_x = create_domain(consts[j]);

        for (k = 0; k < num_consts; k++)
        {
          d_y = create_domain(consts[k]);
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
                      0,
                      boolector_srl,
                      0,
                      0,
                      0,
                      0,
                      true,
                      res);
            assert(
                !res
                || check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_SRL, 0, 0));
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
                      0,
                      boolector_sll,
                      0,
                      0,
                      0,
                      0,
                      true,
                      res);
            assert(
                !res
                || check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_SLL, 0, 0));
          }

          assert(!bzla_bvprop_is_fixed(d_mm, d_x)
                 || !bzla_bvprop_is_valid(d_mm, res_x)
                 || !bzla_bv_compare(d_x->lo, res_x->lo));
          assert(!bzla_bvprop_is_fixed(d_mm, d_y)
                 || !bzla_bvprop_is_valid(d_mm, res_y)
                 || !bzla_bv_compare(d_y->lo, res_y->lo));
          assert(!res || !bzla_bvprop_is_fixed(d_mm, d_z)
                 || !bzla_bvprop_is_valid(d_mm, res_z)
                 || !bzla_bv_compare(d_z->lo, res_z->lo));
          TEST_BVPROP_RELEASE_RES_XYZ;
          bzla_bvprop_free(d_mm, d_y);
        }
        bzla_bvprop_free(d_mm, d_x);
      }
      bzla_bvprop_free(d_mm, d_z);
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
    BoolectorNode *(*boolectorfun)(Bzla *, BoolectorNode *, BoolectorNode *);
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
      d_z   = create_domain(consts[i]);
      str_z = consts[i];

      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x   = create_domain(consts[j]);
        str_x = consts[j];

        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y   = create_domain(consts[k]);
          str_y = consts[k];

          if (op == TEST_BVPROP_AND)
          {
            boolectorfun = boolector_and;
            bvpropfun    = bzla_bvprop_and;
            bvfun        = bzla_bv_and;
          }
          else if (op == TEST_BVPROP_OR)
          {
            boolectorfun = boolector_or;
            bvpropfun    = bzla_bvprop_or;
            bvfun        = bzla_bv_or;
          }
          else
          {
            assert(op == TEST_BVPROP_XOR);
            boolectorfun = boolector_xor;
            bvpropfun    = bzla_bvprop_xor;
            bvfun        = bzla_bv_xor;
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
                    0,
                    boolectorfun,
                    0,
                    0,
                    0,
                    0,
                    false,
                    res);
          assert(!res || check_synth(d_x, d_y, d_z, 0, res_z, op, 0, 0));

          to_str(res_x, &str_res_x, 0, true);
          to_str(res_y, &str_res_y, 0, true);
          to_str(res_z, &str_res_z, 0, true);

          assert(res || !is_valid(d_mm, res_x, res_y, res_z, 0));

          assert(!bzla_bvprop_is_fixed(d_mm, d_x)
                 || !bzla_bvprop_is_valid(d_mm, res_x)
                 || !bzla_bv_compare(d_x->lo, res_x->lo));
          assert(!bzla_bvprop_is_fixed(d_mm, d_y)
                 || !bzla_bvprop_is_valid(d_mm, res_y)
                 || !bzla_bv_compare(d_y->lo, res_y->lo));
          assert(!bzla_bvprop_is_fixed(d_mm, d_z)
                 || !bzla_bvprop_is_valid(d_mm, res_z)
                 || !bzla_bv_compare(d_z->lo, res_z->lo));

          if (res && bzla_bvprop_is_fixed(d_mm, d_x)
              && bzla_bvprop_is_fixed(d_mm, d_y))
          {
            assert(bzla_bvprop_is_fixed(d_mm, res_x));
            assert(bzla_bvprop_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bvfun(d_mm, res_x->lo, res_y->lo);
              assert(!bzla_bv_compare(d_x->lo, res_x->lo));
              assert(!bzla_bv_compare(d_y->lo, res_y->lo));
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              assert(!bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvprop_is_fixed(d_mm, d_z))
            {
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              tmp = bvfun(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                assert(!bzla_bv_compare(d_x->lo, res_x->lo));
                assert(!bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bvfun(d_mm, res_x->lo, res_y->lo);
                assert(!bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }

          if (bzla_bvprop_is_valid(d_mm, res_z))
          {
            assert(bzla_bvprop_is_valid(d_mm, res_x));
            assert(bzla_bvprop_is_valid(d_mm, res_y));

            for (uint32_t l = 0; l < bw; l++)
            {
              if (op == TEST_BVPROP_AND)
              {
                assert(str_z[l] != '1' || (str_x[l] != '0' && str_y[l] != '0'));
                assert(str_z[l] != '0' || (str_x[l] != '1' || str_y[l] != '1'));
                assert(str_z[l] != '1' || str_x[l] != '1'
                       || str_res_y[l] == '1');
                assert(str_z[l] != '1' || str_y[l] != '1'
                       || str_res_x[l] == '1');
                assert(str_z[l] != '0' || str_x[l] != '1'
                       || str_res_y[l] == '0');
                assert(str_z[l] != '0' || str_y[l] != '1'
                       || str_res_x[l] == '0');
              }
              else if (op == TEST_BVPROP_OR)
              {
                assert(str_z[l] != '1' || str_x[l] != '0' || str_y[l] != '0');
                assert(str_z[l] != '0' || (str_x[l] != '1' && str_y[l] != '1'));

                assert(str_z[l] != '0' || str_x[l] != '0'
                       || str_res_y[l] == '0');
                assert(str_z[l] != '0' || str_y[l] != '0'
                       || str_res_x[l] == '0');
                assert(str_z[l] != '1' || str_x[l] != '0'
                       || str_res_y[l] == '1');
                assert(str_z[l] != '1' || str_y[l] != '0'
                       || str_res_x[l] == '1');
              }
              else
              {
                assert(op == TEST_BVPROP_XOR);
                assert(str_z[l] != '1' || (str_x[l] != '0' || str_y[l] != '0')
                       || (str_x[l] != '1' || str_y[l] != '1'));
                assert(str_z[l] != '0'
                       || ((str_x[l] != '0' || str_y[l] != '1')
                           && (str_x[l] != '1' || str_y[l] != '0')));
                assert(str_z[l] != '1' || str_x[l] != '1'
                       || str_res_y[l] == '0');
                assert(str_z[l] != '1' || str_y[l] != '1'
                       || str_res_x[l] == '0');
                assert(str_z[l] != '0' || str_x[l] != '0'
                       || str_res_y[l] == '0');
                assert(str_z[l] != '0' || str_y[l] != '0'
                       || str_res_x[l] == '0');
                assert(str_z[l] != '0' || str_x[l] != '1'
                       || str_res_y[l] == '1');
                assert(str_z[l] != '0' || str_y[l] != '1'
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
            assert(!valid);
          }

          bzla_mem_freestr(d_mm, str_res_x);
          bzla_mem_freestr(d_mm, str_res_y);
          bzla_mem_freestr(d_mm, str_res_z);

          bzla_bvprop_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvprop_free(d_mm, d_x);
      }
      bzla_bvprop_free(d_mm, d_z);
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
      d_z = create_domain(values_z[k]);
      for (size_t i = 0; i < num_consts; i++)
      {
        d_x = create_domain(consts[i]);
        for (size_t j = 0; j < num_consts; j++)
        {
          d_y = create_domain(consts[j]);

          res = bzla_bvprop_eq(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    0,
                    boolector_eq,
                    0,
                    0,
                    0,
                    0,
                    true,
                    res);
          assert(!res
                 || check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_EQ, 0, 0));

          if (res && bzla_bvprop_is_fixed(d_mm, d_x)
              && bzla_bvprop_is_fixed(d_mm, d_y))
          {
            assert(bzla_bvprop_is_fixed(d_mm, res_x));
            assert(bzla_bvprop_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_eq(d_mm, res_x->lo, res_y->lo);
              assert(!bzla_bv_compare(d_x->lo, res_x->lo));
              assert(!bzla_bv_compare(d_y->lo, res_y->lo));
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              assert(!bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvprop_is_fixed(d_mm, d_z))
            {
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              tmp = bzla_bv_eq(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                assert(!bzla_bv_compare(d_x->lo, res_x->lo));
                assert(!bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bzla_bv_eq(d_mm, res_x->lo, res_y->lo);
                assert(!bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }
          bzla_bvprop_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvprop_free(d_mm, d_x);
      }
      bzla_bvprop_free(d_mm, d_z);
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
      d_x = create_domain(consts[i]);

      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_z = create_domain(consts[j]);
        res = bzla_bvprop_not(d_mm, d_x, d_z, &res_x, &res_z);
        check_sat(d_x,
                  0,
                  d_z,
                  0,
                  res_x,
                  0,
                  res_z,
                  0,
                  boolector_not,
                  0,
                  0,
                  0,
                  0,
                  0,
                  false,
                  res);

        if (bzla_bvprop_is_valid(d_mm, res_z))
        {
          assert(res);
          assert(!bzla_bvprop_is_fixed(d_mm, d_x)
                 || !bzla_bv_compare(d_x->lo, res_x->lo));
          assert(!bzla_bvprop_is_fixed(d_mm, d_z)
                 || !bzla_bv_compare(d_z->lo, res_z->lo));
          assert(bzla_bvprop_is_valid(d_mm, res_x));
          assert(!bzla_bvprop_is_fixed(d_mm, d_z)
                 || (bzla_bvprop_is_fixed(d_mm, res_x)
                     && bzla_bvprop_is_fixed(d_mm, res_z)));
          check_not(res_x, res_z);
        }
        else
        {
          assert(!res);
          bool valid = true;
          for (uint32_t k = 0; k < bw && valid; k++)
          {
            if (consts[i][k] != 'x' && consts[i][k] == consts[j][k])
            {
              valid = false;
            }
          }
          assert(!valid);
        }
        bzla_bvprop_free(d_mm, d_z);
        TEST_BVPROP_RELEASE_RES_XZ;
      }
      bzla_bvprop_free(d_mm, d_x);
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
      d_x = create_domain(consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        for (uint32_t lower = 0; lower < bw; lower++)
        {
          for (uint32_t upper = lower; upper < bw; upper++)
          {
            memset(buf, 0, bw + 1);
            memcpy(buf, &consts[j][bw - 1 - upper], upper - lower + 1);
            assert(strlen(buf) > 0);
            assert(strlen(buf) == upper - lower + 1);

            d_z = create_domain(buf);
            res =
                bzla_bvprop_slice(d_mm, d_x, d_z, upper, lower, &res_x, &res_z);
            /* not compositional but eq always returns true */
            assert(res || !is_valid(d_mm, res_x, 0, res_z, 0));
            check_sat(d_x,
                      0,
                      d_z,
                      0,
                      res_x,
                      0,
                      res_z,
                      0,
                      0,
                      0,
                      0,
                      0,
                      upper,
                      lower,
                      false,
                      res);
            assert(!res
                   || check_synth(
                       d_x, 0, d_z, 0, res_z, TEST_BVPROP_SLICE, upper, lower));

            assert(!bzla_bvprop_is_fixed(d_mm, d_x)
                   || !bzla_bvprop_is_valid(d_mm, res_x)
                   || !bzla_bv_compare(d_x->lo, res_x->lo));
            assert(!bzla_bvprop_is_fixed(d_mm, d_z)
                   || !bzla_bvprop_is_valid(d_mm, res_z)
                   || !bzla_bv_compare(d_z->lo, res_z->lo));

            if (bzla_bvprop_is_valid(d_mm, res_z))
            {
              assert(bzla_bvprop_is_valid(d_mm, res_x));
              char *str_res_x = from_domain(d_mm, res_x);
              char *str_res_z = from_domain(d_mm, res_z);
              for (uint32_t k = 0; k < upper - lower + 1; k++)
              {
                assert(str_res_z[k] == str_res_x[bw - 1 - upper + k]);
              }
              bzla_mem_freestr(d_mm, str_res_x);
              bzla_mem_freestr(d_mm, str_res_z);
            }
            else
            {
              assert(!bzla_bvprop_is_valid(d_mm, res_x));
              bool valid = true;
              for (uint32_t k = 0; k < bw; k++)
              {
                if (buf[k] != consts[i][bw - 1 - upper + k])
                {
                  valid = false;
                  break;
                }
              }
              assert(!valid);
            }
            bzla_bvprop_free(d_mm, d_z);
            TEST_BVPROP_RELEASE_RES_XZ;
          }
        }
      }
      bzla_bvprop_free(d_mm, d_x);
    }
    BZLA_DELETEN(d_mm, buf, bw + 1);
    free_consts(bw, num_consts, consts);
  }

  void test_concat(uint32_t bw)
  {
    bool res;
    uint32_t i, j, k, num_consts;
    char *s_const, **consts;
    BzlaBvDomain *d_x, *d_y, *d_z, *res_x, *res_y, *res_z;

    num_consts = generate_consts(bw, &consts);

    for (i = 1; i < bw; i++)
    {
      j = bw - i;
      for (k = 0; k < num_consts; k++)
      {
        d_x = bzla_bvprop_new_init(d_mm, i);
        d_y = bzla_bvprop_new_init(d_mm, j);
        assert(i + j == bw);
        d_z = bzla_bvprop_new_init(d_mm, bw);
        TEST_PROPBV_CONCAT;

        s_const = slice_str_const(consts[k], 0, i - 1);
        d_x     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_y = bzla_bvprop_new_init(d_mm, j);
        d_z = bzla_bvprop_new_init(d_mm, bw);
        TEST_PROPBV_CONCAT;

        d_x     = bzla_bvprop_new_init(d_mm, i);
        s_const = slice_str_const(consts[k], i, bw - 1);
        d_y     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = bzla_bvprop_new_init(d_mm, bw);
        TEST_PROPBV_CONCAT;

        d_x = bzla_bvprop_new_init(d_mm, i);
        d_y = bzla_bvprop_new_init(d_mm, j);
        d_z = create_domain(consts[k]);
        TEST_PROPBV_CONCAT;

        s_const = slice_str_const(consts[k], 0, i - 1);
        d_x     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        s_const = slice_str_const(consts[k], i, bw - 1);
        d_y     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = bzla_bvprop_new_init(d_mm, bw);
        TEST_PROPBV_CONCAT;

        s_const = slice_str_const(consts[k], 0, i - 1);
        d_x     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_y = bzla_bvprop_new_init(d_mm, j);
        d_z = create_domain(consts[k]);
        TEST_PROPBV_CONCAT;

        d_x     = bzla_bvprop_new_init(d_mm, i);
        s_const = slice_str_const(consts[k], i, bw - 1);
        d_y     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = create_domain(consts[k]);
        TEST_PROPBV_CONCAT;

        s_const = slice_str_const(consts[k], 0, i - 1);
        d_x     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        s_const = slice_str_const(consts[k], i, bw - 1);
        d_y     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = create_domain(consts[k]);
        TEST_PROPBV_CONCAT;
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
      d_z = create_domain(consts[i]);
      for (j = 0; j < num_consts; j++)
      {
        for (n = 1; n < bw; n++)
        {
          d_x = create_domain(consts[j] + n);
          res = bzla_bvprop_sext(d_mm, d_x, d_z, &res_x, &res_z);
          check_sat(d_x,
                    0,
                    d_z,
                    0,
                    res_x,
                    0,
                    res_z,
                    0,
                    0,
                    0,
                    0,
                    boolector_sext,
                    n,
                    0,
                    false,
                    res);

          assert(!bzla_bvprop_is_fixed(d_mm, d_x)
                 || !bzla_bvprop_is_valid(d_mm, res_x)
                 || !bzla_bv_compare(d_x->lo, res_x->lo));
          assert(!res || !bzla_bvprop_is_fixed(d_mm, d_z)
                 || !bzla_bvprop_is_valid(d_mm, res_z)
                 || !bzla_bv_compare(d_z->lo, res_z->lo));
          check_sext(res_x, res_z);
          TEST_BVPROP_RELEASE_RES_XZ;
          bzla_bvprop_free(d_mm, d_x);
        }
      }
      bzla_bvprop_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_ite(uint32_t bw)
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
        d_c = bzla_bvprop_new_init(d_mm, 1);
      }
      else
      {
        tmp = bzla_bv_uint64_to_bv(d_mm, c, 1);
        d_c = bzla_bvprop_new(d_mm, tmp, tmp);
        bzla_bv_free(d_mm, tmp);
      }

      for (uint32_t i = 0; i < num_consts; i++)
      {
        d_z = create_domain(consts[i]);
        for (uint32_t j = 0; j < num_consts; j++)
        {
          d_x = create_domain(consts[j]);
          for (uint32_t k = 0; k < num_consts; k++)
          {
            d_y = create_domain(consts[k]);

            res = bzla_bvprop_ite(
                d_mm, d_x, d_y, d_z, d_c, &res_x, &res_y, &res_z, &res_c);
            check_sat(d_x,
                      d_y,
                      d_z,
                      d_c,
                      res_x,
                      res_y,
                      res_z,
                      res_c,
                      0,
                      0,
                      0,
                      0,
                      0,
                      0,
                      true,
                      res);
            if (res) check_ite(res_x, res_y, res_z, res_c);

            bzla_bvprop_free(d_mm, d_y);
            TEST_BVPROP_RELEASE_RES_XYZ;
            bzla_bvprop_free(d_mm, res_c);
          }
          bzla_bvprop_free(d_mm, d_x);
        }
        bzla_bvprop_free(d_mm, d_z);
      }
      bzla_bvprop_free(d_mm, d_c);
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
      d_z = create_domain(consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = create_domain(consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = create_domain(consts[k]);

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
                    0,
                    boolector_add,
                    no_overflows ? boolector_uaddo : 0,
                    0,
                    0,
                    0,
                    true,
                    res);

          if (bzla_bvprop_is_fixed(d_mm, d_x)
              && bzla_bvprop_is_fixed(d_mm, d_y))
          {
            assert(bzla_bvprop_is_fixed(d_mm, res_x));
            assert(bzla_bvprop_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_add(d_mm, res_x->lo, res_y->lo);
              assert(!bzla_bv_compare(d_x->lo, res_x->lo));
              assert(!bzla_bv_compare(d_y->lo, res_y->lo));
              assert(no_overflows || bzla_bvprop_is_fixed(d_mm, res_z));
              assert(!bzla_bvprop_is_fixed(d_mm, res_z)
                     || !bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvprop_is_fixed(d_mm, d_z))
            {
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              tmp = bzla_bv_add(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                assert(!bzla_bv_compare(d_x->lo, res_x->lo));
                assert(!bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bzla_bv_add(d_mm, res_x->lo, res_y->lo);
                assert(!bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }
          bzla_bvprop_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvprop_free(d_mm, d_x);
      }
      bzla_bvprop_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_mul(uint32_t bw, bool no_overflows)
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
      d_z = create_domain(consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = create_domain(consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = create_domain(consts[k]);

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
                    0,
                    boolector_mul,
                    no_overflows ? boolector_umulo : 0,
                    0,
                    0,
                    0,
                    true,
                    res);
          assert(
              !res
              || check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_MUL, 0, 0));

          if (bzla_bvprop_is_fixed(d_mm, d_x)
              && bzla_bvprop_is_fixed(d_mm, d_y))
          {
            assert(bzla_bvprop_is_fixed(d_mm, res_x));
            assert(bzla_bvprop_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_mul(d_mm, res_x->lo, res_y->lo);
              assert(!bzla_bv_compare(d_x->lo, res_x->lo));
              assert(!bzla_bv_compare(d_y->lo, res_y->lo));
              assert(no_overflows || bzla_bvprop_is_fixed(d_mm, res_z));
              assert(!bzla_bvprop_is_fixed(d_mm, res_z)
                     || !bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvprop_is_fixed(d_mm, d_z))
            {
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              tmp = bzla_bv_mul(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                assert(!bzla_bv_compare(d_x->lo, res_x->lo));
                assert(!bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bzla_bv_mul(d_mm, res_x->lo, res_y->lo);
                assert(!bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }

          bzla_bvprop_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvprop_free(d_mm, d_x);
      }
      bzla_bvprop_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_udiv(uint32_t bw)
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
      d_z = create_domain(consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = create_domain(consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = create_domain(consts[k]);

          res = bzla_bvprop_udiv(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    0,
                    boolector_udiv,
                    0,
                    0,
                    0,
                    0,
                    true,
                    res);
          assert(
              !res
              || check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_UDIV, 0, 0));

          if (bzla_bvprop_is_fixed(d_mm, d_x)
              && bzla_bvprop_is_fixed(d_mm, d_y))
          {
            assert(bzla_bvprop_is_fixed(d_mm, res_x));
            assert(bzla_bvprop_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_udiv(d_mm, res_x->lo, res_y->lo);
              assert(!bzla_bv_compare(d_x->lo, res_x->lo));
              assert(!bzla_bv_compare(d_y->lo, res_y->lo));
              assert(!bzla_bvprop_is_fixed(d_mm, res_z)
                     || !bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvprop_is_fixed(d_mm, d_z))
            {
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              tmp = bzla_bv_udiv(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                assert(!bzla_bv_compare(d_x->lo, res_x->lo));
                assert(!bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bzla_bv_udiv(d_mm, res_x->lo, res_y->lo);
                assert(!bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }

          bzla_bvprop_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvprop_free(d_mm, d_x);
      }
      bzla_bvprop_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_urem(uint32_t bw)
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
      d_z = create_domain(consts[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = create_domain(consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = create_domain(consts[k]);

          res = bzla_bvprop_urem(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    0,
                    boolector_urem,
                    0,
                    0,
                    0,
                    0,
                    true,
                    res);
          assert(
              !res
              || check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_UREM, 0, 0));

          if (bzla_bvprop_is_fixed(d_mm, d_x)
              && bzla_bvprop_is_fixed(d_mm, d_y))
          {
            assert(bzla_bvprop_is_fixed(d_mm, res_x));
            assert(bzla_bvprop_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_urem(d_mm, res_x->lo, res_y->lo);
              assert(!bzla_bv_compare(d_x->lo, res_x->lo));
              assert(!bzla_bv_compare(d_y->lo, res_y->lo));
              assert(!bzla_bvprop_is_fixed(d_mm, res_z)
                     || !bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvprop_is_fixed(d_mm, d_z))
            {
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              tmp = bzla_bv_urem(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                assert(!bzla_bv_compare(d_x->lo, res_x->lo));
                assert(!bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bzla_bv_urem(d_mm, res_x->lo, res_y->lo);
                assert(!bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }

          bzla_bvprop_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvprop_free(d_mm, d_x);
      }
      bzla_bvprop_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
  }

  void test_ult(uint32_t bw)
  {
    bool res;
    uint32_t num_consts, num_consts_z;
    char **consts, **consts_z;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_x, *d_y, *d_z;
    BzlaBvDomain *res_x, *res_y, *res_z;

    num_consts   = generate_consts(bw, &consts);
    num_consts_z = generate_consts(1, &consts_z);

    for (uint32_t i = 0; i < num_consts_z; i++)
    {
      d_z = create_domain(consts_z[i]);
      for (uint32_t j = 0; j < num_consts; j++)
      {
        d_x = create_domain(consts[j]);
        for (uint32_t k = 0; k < num_consts; k++)
        {
          d_y = create_domain(consts[k]);

          res = bzla_bvprop_ult(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
          check_sat(d_x,
                    d_y,
                    d_z,
                    0,
                    res_x,
                    res_y,
                    res_z,
                    0,
                    0,
                    boolector_ult,
                    0,
                    0,
                    0,
                    0,
                    true,
                    res);
          assert(
              !res
              || check_synth(d_x, d_y, d_z, 0, res_z, TEST_BVPROP_ULT, 0, 0));

          if (bzla_bvprop_is_fixed(d_mm, d_x)
              && bzla_bvprop_is_fixed(d_mm, d_y))
          {
            assert(bzla_bvprop_is_fixed(d_mm, res_x));
            assert(bzla_bvprop_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_ult(d_mm, res_x->lo, res_y->lo);
              assert(!bzla_bv_compare(d_x->lo, res_x->lo));
              assert(!bzla_bv_compare(d_y->lo, res_y->lo));
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              assert(!bzla_bv_compare(tmp, res_z->lo));
              bzla_bv_free(d_mm, tmp);
            }
            else if (bzla_bvprop_is_fixed(d_mm, d_z))
            {
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              tmp = bzla_bv_ult(d_mm, d_x->lo, d_y->lo);
              if (!bzla_bv_compare(tmp, d_z->lo))
              {
                assert(!bzla_bv_compare(d_x->lo, res_x->lo));
                assert(!bzla_bv_compare(d_y->lo, res_y->lo));
                bzla_bv_free(d_mm, tmp);
                tmp = bzla_bv_ult(d_mm, res_x->lo, res_y->lo);
                assert(!bzla_bv_compare(tmp, res_z->lo));
              }
              bzla_bv_free(d_mm, tmp);
            }
          }
          bzla_bvprop_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvprop_free(d_mm, d_x);
      }
      bzla_bvprop_free(d_mm, d_z);
    }
    free_consts(bw, num_consts, consts);
    free_consts(1, num_consts_z, consts_z);
  }

  uint32_t d_bw          = 0;
  uint32_t d_num_consts  = 1;
  char **d_consts        = nullptr;
  Bzla *d_bzla           = nullptr;
  BzlaAIGVecMgr *d_avmgr = nullptr;
};

TEST_F(TestBvProp, valid_domain)
{
  BzlaBitVector *lo, *hi;
  BzlaBvDomain *d;

  /* check valid */
  lo = bzla_bv_char_to_bv(d_mm, "0101011");
  hi = bzla_bv_char_to_bv(d_mm, "1101011");
  d  = bzla_bvprop_new(d_mm, lo, hi);

  assert(bzla_bvprop_is_valid(d_mm, d));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvprop_free(d_mm, d);

  /* check invalid */
  lo = bzla_bv_char_to_bv(d_mm, "1101011");
  hi = bzla_bv_char_to_bv(d_mm, "0101011");
  d  = bzla_bvprop_new(d_mm, lo, hi);

  assert(!bzla_bvprop_is_valid(d_mm, d));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvprop_free(d_mm, d);
}

TEST_F(TestBvProp, fixed_domain)
{
  BzlaBitVector *lo, *hi;
  BzlaBvDomain *d;
  uint32_t i;

  /* check fixed */
  lo = bzla_bv_char_to_bv(d_mm, "0001111");
  hi = bzla_bv_char_to_bv(d_mm, "0001111");
  d  = bzla_bvprop_new(d_mm, lo, hi);
  assert(bzla_bvprop_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bv_get_width(d->lo); i++)
  {
    assert(bzla_bvprop_is_fixed_bit(d, i));
  }
  assert(bzla_bvprop_is_fixed_bit_false(d, 6));
  assert(bzla_bvprop_is_fixed_bit_false(d, 5));
  assert(bzla_bvprop_is_fixed_bit_false(d, 4));
  assert(bzla_bvprop_is_fixed_bit_true(d, 3));
  assert(bzla_bvprop_is_fixed_bit_true(d, 2));
  assert(bzla_bvprop_is_fixed_bit_true(d, 1));
  assert(bzla_bvprop_is_fixed_bit_true(d, 0));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvprop_free(d_mm, d);

  d = bzla_bvprop_new_init(d_mm, 7);
  assert(!bzla_bvprop_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bv_get_width(d->lo); i++)
  {
    assert(!bzla_bvprop_is_fixed_bit(d, i));
  }
  bzla_bvprop_fix_bit(d, 0, false);
  bzla_bvprop_fix_bit(d, 1, false);
  bzla_bvprop_fix_bit(d, 2, false);
  bzla_bvprop_fix_bit(d, 3, true);
  bzla_bvprop_fix_bit(d, 4, true);
  bzla_bvprop_fix_bit(d, 5, true);
  bzla_bvprop_fix_bit(d, 6, true);
  assert(bzla_bvprop_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bv_get_width(d->lo); i++)
  {
    assert(bzla_bvprop_is_fixed_bit(d, i));
  }
  assert(bzla_bvprop_is_fixed_bit_false(d, 0));
  assert(bzla_bvprop_is_fixed_bit_false(d, 1));
  assert(bzla_bvprop_is_fixed_bit_false(d, 2));
  assert(bzla_bvprop_is_fixed_bit_true(d, 3));
  assert(bzla_bvprop_is_fixed_bit_true(d, 4));
  assert(bzla_bvprop_is_fixed_bit_true(d, 5));
  assert(bzla_bvprop_is_fixed_bit_true(d, 6));
  bzla_bvprop_free(d_mm, d);

  /* check not fixed */
  lo = bzla_bv_char_to_bv(d_mm, "0001111");
  hi = bzla_bv_char_to_bv(d_mm, "0001011");
  d  = bzla_bvprop_new(d_mm, lo, hi);
  assert(!bzla_bvprop_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bv_get_width(d->lo); i++)
  {
    assert(i == 2 || bzla_bvprop_is_fixed_bit(d, i));
  }
  assert(bzla_bvprop_is_fixed_bit_false(d, 6));
  assert(bzla_bvprop_is_fixed_bit_false(d, 5));
  assert(bzla_bvprop_is_fixed_bit_false(d, 4));
  assert(bzla_bvprop_is_fixed_bit_true(d, 3));
  assert(!bzla_bvprop_is_fixed_bit(d, 2));
  assert(bzla_bvprop_is_fixed_bit_true(d, 1));
  assert(bzla_bvprop_is_fixed_bit_true(d, 0));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvprop_free(d_mm, d);

  d = bzla_bvprop_new_init(d_mm, 7);
  assert(!bzla_bvprop_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bv_get_width(d->lo); i++)
  {
    assert(!bzla_bvprop_is_fixed_bit(d, i));
  }
  bzla_bvprop_fix_bit(d, 0, false);
  bzla_bvprop_fix_bit(d, 1, false);
  bzla_bvprop_fix_bit(d, 2, false);
  bzla_bvprop_fix_bit(d, 3, true);
  bzla_bvprop_fix_bit(d, 5, true);
  bzla_bvprop_fix_bit(d, 6, true);
  assert(!bzla_bvprop_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bv_get_width(d->lo); i++)
  {
    assert(i == 4 || bzla_bvprop_is_fixed_bit(d, i));
  }
  assert(bzla_bvprop_is_fixed_bit_false(d, 0));
  assert(bzla_bvprop_is_fixed_bit_false(d, 1));
  assert(bzla_bvprop_is_fixed_bit_false(d, 2));
  assert(!bzla_bvprop_is_fixed_bit(d, 4));
  assert(bzla_bvprop_is_fixed_bit_true(d, 3));
  assert(bzla_bvprop_is_fixed_bit_true(d, 5));
  assert(bzla_bvprop_is_fixed_bit_true(d, 6));
  bzla_bvprop_free(d_mm, d);
}

TEST_F(TestBvProp, init_domain)
{
  BzlaBvDomain *d = bzla_bvprop_new_init(d_mm, 32);
  assert(bzla_bvprop_is_valid(d_mm, d));
  assert(!bzla_bvprop_is_fixed(d_mm, d));
  bzla_bvprop_free(d_mm, d);
}

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
  test_sll(3);
}

TEST_F(TestBvProp, srl)
{
  test_srl(2);
  test_srl(3);
}

TEST_F(TestBvProp, and)
{
  test_and(1);
  test_and(2);
  test_and(3);
}

TEST_F(TestBvProp, or)
{
  test_or(1);
  test_or(2);
  test_or(3);
}

TEST_F(TestBvProp, xor)
{
  test_xor(1);
  test_xor(2);
  test_xor(3);
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
  test_add(3, false);
  test_add(1, true);
  test_add(2, true);
  test_add(3, true);
}

TEST_F(TestBvProp, sext)
{
  test_sext(1);
  test_sext(2);
  test_sext(3);
}

TEST_F(TestBvProp, ite)
{
  test_ite(1);
  test_ite(2);
  test_ite(3);
}

TEST_F(TestBvProp, mul)
{
  test_mul(1, false);
  test_mul(2, false);
  test_mul(3, false);
  test_mul(1, true);
  test_mul(2, true);
  test_mul(3, true);
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
  test_udiv(3);
}

TEST_F(TestBvProp, urem)
{
  test_urem(1);
  test_urem(2);
  test_urem(3);
}
