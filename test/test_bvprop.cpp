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
#include "bzlabvprop.h"
#include "utils/bzlamem.h"
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
  static constexpr uint32_t TEST_BW         = 3;
  static constexpr uint32_t TEST_NUM_CONSTS = 27;
  static constexpr uint32_t TEST_CONST_LEN  = (TEST_BW + 1);

  static constexpr uint32_t TEST_BVPROP_AND = 0;
  static constexpr uint32_t TEST_BVPROP_OR  = 1;
  static constexpr uint32_t TEST_BVPROP_XOR = 2;

  /* Initialize all possible values for 3-valued constants of bit-width bw */
  void generate_consts(uint32_t bw)
  {
    assert(bw);
    assert(!d_consts);
    assert(!d_bw);

    char bit = '0';
    size_t psize;

    d_bw = bw;
    for (size_t i = 0; i < d_bw; i++) d_num_consts *= 3;
    psize = d_num_consts;

    BZLA_NEWN(d_mm, d_consts, d_num_consts);
    for (size_t i = 0; i < d_num_consts; i++)
      BZLA_CNEWN(d_mm, d_consts[i], d_bw + 1);

    for (size_t i = 0; i < d_bw; i++)
    {
      psize = psize / 3;
      for (size_t j = 0; j < d_num_consts; j++)
      {
        d_consts[j][i] = bit;
        if ((j + 1) % psize == 0)
        {
          bit = bit == '0' ? '1' : (bit == '1' ? 'x' : '0');
        }
      }
    }
  }

  void free_consts()
  {
    assert(d_bw);
    assert(d_consts);
    for (size_t i = 0; i < d_num_consts; i++)
      BZLA_DELETEN(d_mm, d_consts[i], d_bw + 1);
    BZLA_DELETEN(d_mm, d_consts, d_num_consts);
    d_num_consts = 1;
    d_consts     = 0;
    d_bw         = 0;
  }

  void print_domain(BzlaBvDomain *d, bool print_short)
  {
    if (print_short)
    {
      char *lo   = bzla_bv_to_char(d_mm, d->lo);
      char *hi   = bzla_bv_to_char(d_mm, d->hi);
      size_t len = strlen(lo);
      for (size_t i = 0; i < len; i++)
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
      printf("%s\n", lo);
      bzla_mem_freestr(d_mm, hi);
      bzla_mem_freestr(d_mm, lo);
    }
    else
    {
      char *s = bzla_bv_to_char(d_mm, d->lo);
      printf("lo: %s, ", s);
      bzla_mem_freestr(d_mm, s);
      s = bzla_bv_to_char(d_mm, d->hi);
      printf("hi: %s\n", s);
      bzla_mem_freestr(d_mm, s);
    }
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

  bool is_false_eq(const char *a, const char *b)
  {
    assert(strlen(a) == strlen(b));
    size_t len = strlen(a);
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

  bool is_true_eq(const char *a, const char *b)
  {
    assert(strlen(a) == strlen(b));
    size_t len = strlen(a);
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

  bool check_const_bits(BzlaBvDomain *d, const char *expected)
  {
    assert(bzla_bvprop_is_valid(d_mm, d));
    size_t len = strlen(expected);
    uint32_t bit_lo, bit_hi;
    bool res = true;

    for (size_t i = 0; i < len && res; i++)
    {
      bit_lo = bzla_bv_get_bit(d->lo, len - 1 - i);
      bit_hi = bzla_bv_get_bit(d->hi, len - 1 - i);
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

  void check_sat(BzlaBvDomain *d_x,
                 BzlaBvDomain *d_y,
                 BzlaBvDomain *d_z,
                 BzlaBvDomain *d_c,
                 BzlaBvDomain *res_x,
                 BzlaBvDomain *res_y,
                 BzlaBvDomain *res_z,
                 BzlaBvDomain *res_c,
                 BoolectorNode *(*unfun)(Bzla *, BoolectorNode *),
                 BoolectorNode *(*binfun)(Bzla *,
                                          BoolectorNode *,
                                          BoolectorNode *),
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

    size_t i;
    int32_t sat_res;
    uint32_t bwx, bwy, bwz, idx;
    char *str_x, *str_y, *str_z, *str_c;
    Bzla *bzla;
    BoolectorNode *x, *y, *z, *c, *fun, *eq, *slice, *one, *zero;
    BoolectorSort swx, swy, swz, s1;

    str_x = from_domain(d_mm, d_x);
    str_y = 0;
    str_z = from_domain(d_mm, d_z);
    str_c = 0;

    bzla = boolector_new();
    boolector_set_opt(bzla, BZLA_OPT_MODEL_GEN, 1);
    bwx  = bzla_bv_get_width(d_x->lo);
    swx  = boolector_bitvec_sort(bzla, bwx);
    bwz  = bzla_bv_get_width(d_z->lo);
    swz  = boolector_bitvec_sort(bzla, bwz);
    s1   = boolector_bitvec_sort(bzla, 1);
    one  = boolector_one(bzla, s1);
    zero = boolector_zero(bzla, s1);
    x    = boolector_var(bzla, swx, "x");
    z    = boolector_var(bzla, swz, "z");
    y    = 0;
    c    = 0;

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

    for (i = 0; i < bwx; i++)
    {
      idx = bwx - i - 1;
      if (str_x[i] != 'x')
      {
        slice = boolector_slice(bzla, x, idx, idx);
        eq    = boolector_eq(bzla, slice, str_x[i] == '1' ? one : zero);
        boolector_assert(bzla, eq);
        boolector_release(bzla, eq);
        boolector_release(bzla, slice);
      }
    }
    if (str_y)
    {
      for (i = 0; i < bwy; i++)
      {
        idx = bwy - i - 1;
        if (str_y[i] != 'x')
        {
          slice = boolector_slice(bzla, y, idx, idx);
          eq    = boolector_eq(bzla, slice, str_y[i] == '1' ? one : zero);
          boolector_assert(bzla, eq);
          boolector_release(bzla, eq);
          boolector_release(bzla, slice);
        }
      }
    }
    for (i = 0; i < bwz; i++)
    {
      idx = bwz - i - 1;
      if (str_z[i] != 'x')
      {
        slice = boolector_slice(bzla, z, idx, idx);
        eq    = boolector_eq(bzla, slice, str_z[i] == '1' ? one : zero);
        boolector_assert(bzla, eq);
        boolector_release(bzla, eq);
        boolector_release(bzla, slice);
      }
    }
    if (str_c)
    {
      if (str_c[0] != 'x')
      {
        eq = boolector_eq(bzla, c, str_c[0] == '1' ? one : zero);
        boolector_assert(bzla, eq);
        boolector_release(bzla, eq);
      }
    }

    // boolector_dump_smt2 (bzla, stdout);
    sat_res = boolector_sat(bzla);
    assert(sat_res != BZLA_RESULT_SAT
           || (valid && is_valid(d_mm, res_x, res_y, res_z, res_c)));
    assert(sat_res != BZLA_RESULT_UNSAT
           || ((decompositional
                || (!valid && !is_valid(d_mm, res_x, res_y, res_z, res_c)))
               && (!decompositional || !valid
                   || !is_fixed(d_mm, res_x, res_y, res_z, res_c))));

    // printf ("sat_res %d\n", sat_res);
    // if (sat_res == BOOLECTOR_SAT)
    //{
    //  boolector_print_model (bzla, "btor", stdout);
    //}

    boolector_release(bzla, x);
    if (c) boolector_release(bzla, c);
    if (y) boolector_release(bzla, y);
    boolector_release(bzla, z);
    boolector_release(bzla, one);
    boolector_release(bzla, zero);
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
    size_t i, j;
    uint32_t n;
    BzlaBitVector *bv_n;
    BzlaBvDomain *d_x, *d_y, *d_z, *res_x, *res_z;

    generate_consts(bw);

    for (i = 0; i < d_num_consts; i++)
    {
      d_z = create_domain(d_consts[i]);
      for (j = 0; j < d_num_consts; j++)
      {
        d_x = create_domain(d_consts[j]);

        for (n = 0; n < d_bw + 1; n++)
        {
          bv_n = bzla_bv_uint64_to_bv(d_mm, n, d_bw);
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
                      false,
                      res);
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
                      false,
                      res);
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
    free_consts();
  }

  void test_sll_const(uint32_t bw) { test_shift_const(bw, false); }

  void test_srl_const(uint32_t bw) { test_shift_const(bw, true); }

  void test_and_or_xor(int32_t op, uint32_t bw)
  {
    bool res;
    BzlaBvDomain *d_x, *d_y, *d_z;
    BzlaBvDomain *res_x, *res_y, *res_z;

    generate_consts(bw);

    for (size_t i = 0; i < d_num_consts; i++)
    {
      d_z = create_domain(d_consts[i]);
      for (size_t j = 0; j < d_num_consts; j++)
      {
        d_x = create_domain(d_consts[j]);
        for (size_t k = 0; k < d_num_consts; k++)
        {
          d_y = create_domain(d_consts[k]);

          if (op == TEST_BVPROP_AND)
          {
            res = bzla_bvprop_and(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
            check_sat(d_x,
                      d_y,
                      d_z,
                      0,
                      res_x,
                      res_y,
                      res_z,
                      0,
                      0,
                      boolector_and,
                      0,
                      0,
                      0,
                      false,
                      res);
          }
          else if (op == TEST_BVPROP_OR)
          {
            res = bzla_bvprop_or(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
            check_sat(d_x,
                      d_y,
                      d_z,
                      0,
                      res_x,
                      res_y,
                      res_z,
                      0,
                      0,
                      boolector_or,
                      0,
                      0,
                      0,
                      false,
                      res);
          }
          else
          {
            assert(op == TEST_BVPROP_XOR);
            res = bzla_bvprop_xor(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
            check_sat(d_x,
                      d_y,
                      d_z,
                      0,
                      res_x,
                      res_y,
                      res_z,
                      0,
                      0,
                      boolector_xor,
                      0,
                      0,
                      0,
                      false,
                      res);
          }
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

          if (bzla_bvprop_is_valid(d_mm, res_z))
          {
            assert(bzla_bvprop_is_valid(d_mm, res_x));
            assert(bzla_bvprop_is_valid(d_mm, res_y));

            for (size_t l = 0; l < d_bw; l++)
            {
              if (op == TEST_BVPROP_AND)
              {
                assert(d_consts[i][l] != '1'
                       || (d_consts[j][l] != '0' && d_consts[k][l] != '0'));
                assert(d_consts[i][l] != '0'
                       || (d_consts[j][l] != '1' || d_consts[k][l] != '1'));
              }
              else if (op == TEST_BVPROP_OR)
              {
                assert(d_consts[i][l] != '1' || d_consts[j][l] != '0'
                       || d_consts[k][l] != '0');
                assert(d_consts[i][l] != '0'
                       || (d_consts[j][l] != '1' && d_consts[k][l] != '1'));
              }
              else
              {
                assert(op == TEST_BVPROP_XOR);
                assert(d_consts[i][l] != '1'
                       || (d_consts[j][l] != '0' || d_consts[k][l] != '0')
                       || (d_consts[j][l] != '1' || d_consts[k][l] != '1'));
                assert(
                    d_consts[i][l] != '0'
                    || ((d_consts[j][l] != '0' || d_consts[k][l] != '1')
                        && (d_consts[j][l] != '1' || d_consts[k][l] != '0')));
              }
            }
          }
          else
          {
            bool valid = true;
            for (size_t l = 0; l < d_bw && valid; l++)
            {
              if ((op == TEST_BVPROP_AND
                   && ((d_consts[i][l] == '0' && d_consts[j][l] != '0'
                        && d_consts[k][l] != '0')
                       || (d_consts[i][l] == '1'
                           && (d_consts[j][l] == '0'
                               || d_consts[k][l] == '0'))))
                  || (op == TEST_BVPROP_OR
                      && ((d_consts[i][l] == '1' && d_consts[j][l] != '1'
                           && d_consts[k][l] != '1')
                          || (d_consts[i][l] == '0'
                              && (d_consts[j][l] == '1'
                                  || d_consts[k][l] == '1'))))
                  || (op == TEST_BVPROP_XOR
                      && ((d_consts[i][l] == '1'
                           && ((d_consts[j][l] != '0' && d_consts[k][l] != '0')
                               || (d_consts[j][l] != '1'
                                   && d_consts[k][l] != '1')))
                          || (d_consts[i][l] == '0'
                              && ((d_consts[j][l] != '1'
                                   && d_consts[k][l] != '0')
                                  || (d_consts[j][l] != '0'
                                      && d_consts[k][l] != '1'))))))
              {
                valid = false;
              }
            }
            assert(!valid);
          }
          bzla_bvprop_free(d_mm, d_y);
          TEST_BVPROP_RELEASE_RES_XYZ;
        }
        bzla_bvprop_free(d_mm, d_x);
      }
      bzla_bvprop_free(d_mm, d_z);
    }
    free_consts();
  }

  void test_and(uint32_t bw) { test_and_or_xor(TEST_BVPROP_AND, bw); }

  void test_or(uint32_t bw) { test_and_or_xor(TEST_BVPROP_OR, bw); }

  void test_xor(uint32_t bw) { test_and_or_xor(TEST_BVPROP_XOR, bw); }

  void test_eq(uint32_t bw)
  {
    char *str_z;
    BzlaBvDomain *d_x, *d_y, *res_xy, *res_z;

    generate_consts(bw);

    for (size_t i = 0; i < d_num_consts; i++)
    {
      d_x = create_domain(d_consts[i]);
      for (size_t j = 0; j < d_num_consts; j++)
      {
        d_y = create_domain(d_consts[j]);
        (void) bzla_bvprop_eq(d_mm, d_x, d_y, &res_xy, &res_z);
        if (bzla_bvprop_is_fixed(d_mm, res_z))
        {
          str_z = from_domain(d_mm, res_z);
          assert(strlen(str_z) == 1);
          assert(str_z[0] == '0' || str_z[0] == '1');
          if (str_z[0] == '0')
          {
            assert(!bzla_bvprop_is_valid(d_mm, res_xy));
            assert(is_false_eq(d_consts[i], d_consts[j]));
          }
          else
          {
            assert(str_z[0] == '1');
            assert(bzla_bvprop_is_valid(d_mm, res_xy));
            assert(bzla_bvprop_is_fixed(d_mm, res_xy));
            assert(is_true_eq(d_consts[i], d_consts[j]));
          }
          bzla_mem_freestr(d_mm, str_z);
        }
        else
        {
          assert(bzla_bvprop_is_valid(d_mm, res_xy));
          assert(!is_false_eq(d_consts[i], d_consts[j]));
          assert(!is_true_eq(d_consts[i], d_consts[j]));
        }
        bzla_bvprop_free(d_mm, d_y);
        bzla_bvprop_free(d_mm, res_xy);
        bzla_bvprop_free(d_mm, res_z);
      }
      bzla_bvprop_free(d_mm, d_x);
    }
    free_consts();
  }

  void test_not(uint32_t bw)
  {
    bool res;
    BzlaBvDomain *d_x, *d_z, *res_x, *res_z;

    generate_consts(bw);

    for (size_t i = 0; i < d_num_consts; i++)
    {
      d_x = create_domain(d_consts[i]);

      for (size_t j = 0; j < d_num_consts; j++)
      {
        d_z = create_domain(d_consts[j]);
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
          for (size_t k = 0; k < d_bw && valid; k++)
          {
            if (d_consts[i][k] != 'x' && d_consts[i][k] == d_consts[j][k])
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
    free_consts();
  }

  void test_slice(uint32_t bw)
  {
    bool res;
    char *buf;
    BzlaBvDomain *d_x, *d_z, *res_x, *res_z;

    generate_consts(bw);
    BZLA_CNEWN(d_mm, buf, d_bw + 1);

    for (size_t i = 0; i < d_num_consts; i++)
    {
      d_x = create_domain(d_consts[i]);
      for (size_t j = 0; j < d_num_consts; j++)
      {
        for (uint32_t lower = 0; lower < d_bw; lower++)
        {
          for (uint32_t upper = lower; upper < d_bw; upper++)
          {
            memset(buf, 0, d_bw + 1);
            memcpy(buf, &d_consts[j][d_bw - 1 - upper], upper - lower + 1);
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
                      upper,
                      lower,
                      false,
                      res);

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
              for (size_t k = 0; k < upper - lower + 1; k++)
              {
                assert(str_res_z[k] == str_res_x[d_bw - 1 - upper + k]);
              }
              bzla_mem_freestr(d_mm, str_res_x);
              bzla_mem_freestr(d_mm, str_res_z);
            }
            else
            {
              assert(!bzla_bvprop_is_valid(d_mm, res_x));
              bool valid = true;
              for (size_t k = 0; k < d_bw; k++)
              {
                if (buf[k] != d_consts[i][d_bw - 1 - upper + k])
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
    BZLA_DELETEN(d_mm, buf, d_bw + 1);
    free_consts();
  }

  void test_concat(uint32_t bw)
  {
    bool res;
    size_t i, j, k;
    char *s_const;
    BzlaBvDomain *d_x, *d_y, *d_z, *res_x, *res_y, *res_z;

    generate_consts(bw);

    for (i = 1; i < d_bw; i++)
    {
      j = d_bw - i;
      for (k = 0; k < d_num_consts; k++)
      {
        d_x = bzla_bvprop_new_init(d_mm, i);
        d_y = bzla_bvprop_new_init(d_mm, j);
        assert(i + j == d_bw);
        d_z = bzla_bvprop_new_init(d_mm, d_bw);
        TEST_PROPBV_CONCAT;

        s_const = slice_str_const(d_consts[k], 0, i - 1);
        d_x     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_y = bzla_bvprop_new_init(d_mm, j);
        d_z = bzla_bvprop_new_init(d_mm, d_bw);
        TEST_PROPBV_CONCAT;

        d_x     = bzla_bvprop_new_init(d_mm, i);
        s_const = slice_str_const(d_consts[k], i, d_bw - 1);
        d_y     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = bzla_bvprop_new_init(d_mm, d_bw);
        TEST_PROPBV_CONCAT;

        d_x = bzla_bvprop_new_init(d_mm, i);
        d_y = bzla_bvprop_new_init(d_mm, j);
        d_z = create_domain(d_consts[k]);
        TEST_PROPBV_CONCAT;

        s_const = slice_str_const(d_consts[k], 0, i - 1);
        d_x     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        s_const = slice_str_const(d_consts[k], i, d_bw - 1);
        d_y     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = bzla_bvprop_new_init(d_mm, d_bw);
        TEST_PROPBV_CONCAT;

        s_const = slice_str_const(d_consts[k], 0, i - 1);
        d_x     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_y = bzla_bvprop_new_init(d_mm, j);
        d_z = create_domain(d_consts[k]);
        TEST_PROPBV_CONCAT;

        d_x     = bzla_bvprop_new_init(d_mm, i);
        s_const = slice_str_const(d_consts[k], i, d_bw - 1);
        d_y     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = create_domain(d_consts[k]);
        TEST_PROPBV_CONCAT;

        s_const = slice_str_const(d_consts[k], 0, i - 1);
        d_x     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        s_const = slice_str_const(d_consts[k], i, d_bw - 1);
        d_y     = create_domain(s_const);
        bzla_mem_freestr(d_mm, s_const);
        d_z = create_domain(d_consts[k]);
        TEST_PROPBV_CONCAT;
      }
    }
    free_consts();
  }

  void test_sext(uint32_t bw)
  {
    bool res;
    size_t i, j;
    uint32_t n;
    BzlaBvDomain *d_x, *d_z, *res_x, *res_z;

    generate_consts(bw);

    for (i = 0; i < d_num_consts; i++)
    {
      d_z = create_domain(d_consts[i]);
      for (j = 0; j < d_num_consts; j++)
      {
        for (n = 1; n < d_bw; n++)
        {
          d_x = create_domain(d_consts[j] + n);
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
    free_consts();
  }

  void test_ite(uint32_t bw)
  {
    bool res;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_c, *d_x, *d_y, *d_z;
    BzlaBvDomain *res_c, *res_x, *res_y, *res_z;

    generate_consts(bw);

    for (size_t c = 0; c < 3; c++)
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

      for (size_t i = 0; i < d_num_consts; i++)
      {
        d_z = create_domain(d_consts[i]);
        for (size_t j = 0; j < d_num_consts; j++)
        {
          d_x = create_domain(d_consts[j]);
          for (size_t k = 0; k < d_num_consts; k++)
          {
            d_y = create_domain(d_consts[k]);

            res = bzla_bvprop_ite(
                d_mm, d_c, d_x, d_y, d_z, &res_c, &res_x, &res_y, &res_z);
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
                      false, /* we always get an invalid result if invalid */
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
    free_consts();
  }

  void test_add(uint32_t bw)
  {
    bool res;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_x, *d_y, *d_z;
    BzlaBvDomain *res_x, *res_y, *res_z;

    generate_consts(bw);

    for (size_t i = 0; i < d_num_consts; i++)
    {
      d_z = create_domain(d_consts[i]);
      for (size_t j = 0; j < d_num_consts; j++)
      {
        d_x = create_domain(d_consts[j]);
        for (size_t k = 0; k < d_num_consts; k++)
        {
          d_y = create_domain(d_consts[k]);

          res = bzla_bvprop_add(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
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
                    0,
                    0,
                    0,
                    true,
                    res);

          if (res && bzla_bvprop_is_fixed(d_mm, d_x)
              && bzla_bvprop_is_fixed(d_mm, d_y))
          {
            assert(bzla_bvprop_is_fixed(d_mm, res_x));
            assert(bzla_bvprop_is_fixed(d_mm, res_y));
            if (is_xxx_domain(d_mm, d_z))
            {
              tmp = bzla_bv_add(d_mm, res_x->lo, res_y->lo);
              assert(!bzla_bv_compare(d_x->lo, res_x->lo));
              assert(!bzla_bv_compare(d_y->lo, res_y->lo));
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              assert(!bzla_bv_compare(tmp, res_z->lo));
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
    free_consts();
  }

  void test_mul(uint32_t bw)
  {
    bool res;
    BzlaBitVector *tmp;
    BzlaBvDomain *d_x, *d_y, *d_z;
    BzlaBvDomain *res_x, *res_y, *res_z;

    generate_consts(bw);

    for (size_t i = 0; i < d_num_consts; i++)
    {
      d_z = create_domain(d_consts[i]);
      for (size_t j = 0; j < d_num_consts; j++)
      {
        d_x = create_domain(d_consts[j]);
        for (size_t k = 0; k < d_num_consts; k++)
        {
          d_y = create_domain(d_consts[k]);

          res = bzla_bvprop_mul(d_mm, d_x, d_y, d_z, &res_x, &res_y, &res_z);
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
              tmp = bzla_bv_mul(d_mm, res_x->lo, res_y->lo);
              assert(!bzla_bv_compare(d_x->lo, res_x->lo));
              assert(!bzla_bv_compare(d_y->lo, res_y->lo));
              assert(bzla_bvprop_is_fixed(d_mm, res_z));
              assert(!bzla_bv_compare(tmp, res_z->lo));
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
    free_consts();
  }

  uint32_t d_bw         = 0;
  uint32_t d_num_consts = 1;
  char **d_consts       = nullptr;
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

  /* check fixed */
  lo = bzla_bv_char_to_bv(d_mm, "0001111");
  hi = bzla_bv_char_to_bv(d_mm, "0001111");
  d  = bzla_bvprop_new(d_mm, lo, hi);

  assert(bzla_bvprop_is_fixed(d_mm, d));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvprop_free(d_mm, d);

  /* check not fixed */
  lo = bzla_bv_char_to_bv(d_mm, "0001111");
  hi = bzla_bv_char_to_bv(d_mm, "0001011");
  d  = bzla_bvprop_new(d_mm, lo, hi);

  assert(!bzla_bvprop_is_fixed(d_mm, d));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
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

TEST_F(TestBvProp, sll)
{
  test_sll_const(1);
  test_sll_const(2);
  test_sll_const(3);
}

TEST_F(TestBvProp, srl)
{
  test_srl_const(1);
  test_srl_const(2);
  test_srl_const(3);
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
  test_add(1);
  test_add(2);
  test_add(3);
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
  test_mul(1);
  test_mul(2);
  test_mul(3);
}
