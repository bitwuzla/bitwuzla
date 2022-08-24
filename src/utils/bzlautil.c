/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "utils/bzlautil.h"

#include <assert.h>
#include <limits.h>

#include "bzlacore.h"
#include "dumper/bzladumpbtor.h"
#include "utils/bzlastack.h"
#ifndef NDEBUG
#include <float.h>
#endif
#include <stdbool.h>
#include <stdint.h>

/*------------------------------------------------------------------------*/

bool
bzla_util_is_power_of_2(uint32_t x)
{
  assert(x > 0);
  return (x & (x - 1)) == 0;
}

bool
bzla_util_is_valid_real(const char *value)
{
  size_t len               = strlen(value);
  bool found_decimal_point = false;

  for (size_t i = 0; i < len; ++i)
  {
    if (!isdigit(value[i]))
    {
      if (i == 0 && value[i] == '-')
      {
        continue;
      }
      else if (value[i] == '.' && !found_decimal_point)
      {
        found_decimal_point = true;
        continue;
      }
      return false;
    }
  }
  return true;
}

uint32_t
bzla_util_log_2(uint32_t x)
{
  uint32_t result = 0;
  assert(x > 0);
  assert(bzla_util_is_power_of_2(x));
  while (x > 1)
  {
    x >>= 1;
    result++;
  }
  return result;
}

int32_t
bzla_util_pow_2(int32_t x)
{
  int32_t result = 1;
  assert(x >= 0);
  while (x > 0)
  {
    assert(result <= INT32_MAX / 2);
    result <<= 1;
    x--;
  }
  assert(result > 0);
  return result;
}

int32_t
bzla_util_next_power_of_2(int32_t x)
{
  int32_t i;
  assert(x > 0);
  x--;
  for (i = 1; i < (int32_t) sizeof(int32_t) * 8; i *= 2) x = x | (x >> i);
  return x + 1;
}

uint32_t
bzla_util_num_digits(uint32_t x)
{
  int32_t result;

  result = 0;
  do
  {
    x /= 10;
    result++;
  } while (x > 0);
  return result;
}

/*------------------------------------------------------------------------*/

static const char *digit2const_table[10] = {
    "",
    "1",
    "10",
    "11",
    "100",
    "101",
    "110",
    "111",
    "1000",
    "1001",
};

static const char *
digit2const(char ch)
{
  assert('0' <= ch);
  assert(ch <= '9');

  return digit2const_table[ch - '0'];
}

static const char *
strip_zeroes(const char *a)
{
  assert(a);

  while (*a == '0') a++;

  return a;
}

#ifndef NDEBUG

static bool
is_bin_str(const char *c)
{
  const char *p;
  char ch;

  assert(c != NULL);

  for (p = c; (ch = *p); p++)
    if (ch != '0' && ch != '1') return false;
  return true;
}

#endif

static char *
add_unbounded_bin_str(BzlaMemMgr *mm, const char *a, const char *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(is_bin_str(a));
  assert(is_bin_str(b));

  char *res, *r, c, x, y, s, *tmp;
  uint32_t alen, blen, rlen;
  const char *p, *q;

  a = strip_zeroes(a);
  b = strip_zeroes(b);

  if (!*a) return bzla_mem_strdup(mm, b);

  if (!*b) return bzla_mem_strdup(mm, a);

  alen = strlen(a);
  blen = strlen(b);
  rlen = (alen < blen) ? blen : alen;
  rlen++;

  BZLA_NEWN(mm, res, rlen + 1);

  p = a + alen;
  q = b + blen;

  c = '0';

  r  = res + rlen;
  *r = 0;

  while (res < r)
  {
    x    = (a < p) ? *--p : '0';
    y    = (b < q) ? *--q : '0';
    s    = x ^ y ^ c;
    c    = (x & y) | (x & c) | (y & c);
    *--r = s;
  }

  p = strip_zeroes(res);
  if ((p != res))
  {
    tmp = bzla_mem_strdup(mm, p);
    bzla_mem_freestr(mm, res);
    res = tmp;
  }

  return res;
}

static char *
mult_unbounded_bin_str(BzlaMemMgr *mm, const char *a, const char *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(is_bin_str(a));
  assert(is_bin_str(b));

  char *res, *r, c, x, y, s, m;
  uint32_t alen, blen, rlen, i;
  const char *p;

  a = strip_zeroes(a);

  if (!*a) return bzla_mem_strdup(mm, "");

  if (a[0] == '1' && !a[1]) return bzla_mem_strdup(mm, b);

  b = strip_zeroes(b);

  if (!*b) return bzla_mem_strdup(mm, "");

  if (b[0] == '1' && !b[1]) return bzla_mem_strdup(mm, a);

  alen = strlen(a);
  blen = strlen(b);
  rlen = alen + blen;
  BZLA_NEWN(mm, res, rlen + 1);
  res[rlen] = 0;

  for (r = res; r < res + blen; r++) *r = '0';

  for (p = a; p < a + alen; p++) *r++ = *p;

  assert(r == res + rlen);

  for (i = 0; i < alen; i++)
  {
    m = res[rlen - 1];
    c = '0';

    if (m == '1')
    {
      p = b + blen;
      r = res + blen;

      while (res < r && b < p)
      {
        assert(b < p);
        x  = *--p;
        y  = *--r;
        s  = x ^ y ^ c;
        c  = (x & y) | (x & c) | (y & c);
        *r = s;
      }
    }

    memmove(res + 1, res, rlen - 1);
    res[0] = c;
  }

  return res;
}

char *
bzla_util_dec_to_bin_str_n(BzlaMemMgr *mm, const char *str, uint32_t len)
{
  assert(mm);
  assert(str);

  const char *end, *p;
  char *res, *tmp;

  res = bzla_mem_strdup(mm, "");

  end = str + len;
  for (p = str; p < end; p++)
  {
    tmp = mult_unbounded_bin_str(mm, res, "1010"); /* *10 */
    bzla_mem_freestr(mm, res);
    res = tmp;

    tmp = add_unbounded_bin_str(mm, res, digit2const(*p));
    bzla_mem_freestr(mm, res);
    res = tmp;
  }

  assert(strip_zeroes(res) == res);
  if (strlen(res)) return res;
  bzla_mem_freestr(mm, res);
  return bzla_mem_strdup(mm, "0");
}

char *
bzla_util_dec_to_bin_str(BzlaMemMgr *mm, const char *str)
{
  assert(mm);
  assert(str);

  return bzla_util_dec_to_bin_str_n(mm, str, strlen(str));
}

char *
bzla_util_hex_to_bin_str_n(BzlaMemMgr *mm, const char *str, uint32_t len)
{
  assert(mm);
  assert(str);

  const char *p, *end;
  char *tmp, *res, *q;
  uint32_t blen;

  blen = 4 * len;
  BZLA_NEWN(mm, tmp, blen + 1);
  q = tmp;

  end = str + len;
  for (p = str; p < end; p++) switch (*p)
    {
      case '0':
        *q++ = '0';
        *q++ = '0';
        *q++ = '0';
        *q++ = '0';
        break;
      case '1':
        *q++ = '0';
        *q++ = '0';
        *q++ = '0';
        *q++ = '1';
        break;
      case '2':
        *q++ = '0';
        *q++ = '0';
        *q++ = '1';
        *q++ = '0';
        break;
      case '3':
        *q++ = '0';
        *q++ = '0';
        *q++ = '1';
        *q++ = '1';
        break;
      case '4':
        *q++ = '0';
        *q++ = '1';
        *q++ = '0';
        *q++ = '0';
        break;
      case '5':
        *q++ = '0';
        *q++ = '1';
        *q++ = '0';
        *q++ = '1';
        break;
      case '6':
        *q++ = '0';
        *q++ = '1';
        *q++ = '1';
        *q++ = '0';
        break;
      case '7':
        *q++ = '0';
        *q++ = '1';
        *q++ = '1';
        *q++ = '1';
        break;
      case '8':
        *q++ = '1';
        *q++ = '0';
        *q++ = '0';
        *q++ = '0';
        break;
      case '9':
        *q++ = '1';
        *q++ = '0';
        *q++ = '0';
        *q++ = '1';
        break;
      case 'A':
      case 'a':
        *q++ = '1';
        *q++ = '0';
        *q++ = '1';
        *q++ = '0';
        break;
      case 'B':
      case 'b':
        *q++ = '1';
        *q++ = '0';
        *q++ = '1';
        *q++ = '1';
        break;
      case 'C':
      case 'c':
        *q++ = '1';
        *q++ = '1';
        *q++ = '0';
        *q++ = '0';
        break;
      case 'D':
      case 'd':
        *q++ = '1';
        *q++ = '1';
        *q++ = '0';
        *q++ = '1';
        break;
      case 'E':
      case 'e':
        *q++ = '1';
        *q++ = '1';
        *q++ = '1';
        *q++ = '0';
        break;
      case 'F':
      case 'f':
      default:
        assert(*p == 'f' || *p == 'F');
        *q++ = '1';
        *q++ = '1';
        *q++ = '1';
        *q++ = '1';
        break;
    }

  assert(tmp + blen == q);
  *q++ = 0;

  res = bzla_mem_strdup(mm, strip_zeroes(tmp));
  bzla_mem_freestr(mm, tmp);

  if (strlen(res)) return res;
  bzla_mem_freestr(mm, res);
  return bzla_mem_strdup(mm, "0");
}

char *
bzla_util_hex_to_bin_str(BzlaMemMgr *mm, const char *str)
{
  assert(mm);
  assert(str);

  return bzla_util_hex_to_bin_str_n(mm, str, strlen(str));
}

/*------------------------------------------------------------------------*/

bool
bzla_util_check_bin_to_bv(BzlaMemMgr *mm, const char *str, uint32_t bw)
{
  assert(mm);
  assert(str);
  assert(str[0] != '-');
  assert(bw);

  (void) mm;
  return strlen(str) <= bw;
}

bool
bzla_util_check_dec_to_bv(BzlaMemMgr *mm, const char *str, uint32_t bw)
{
  assert(mm);
  assert(str);
  assert(bw);

  bool is_neg, is_min_val = false, res;
  char *bits;
  size_t size_bits;

  is_neg    = (str[0] == '-');
  bits      = bzla_util_dec_to_bin_str(mm, is_neg ? str + 1 : str);
  size_bits = strlen(bits);
  if (is_neg)
  {
    is_min_val = (bits[0] == '1');
    for (size_t i = 1; is_min_val && i < size_bits; i++)
      is_min_val = (bits[i] == '0');
  }
  res = ((is_neg && !is_min_val) || size_bits <= bw)
        && (!is_neg || is_min_val || size_bits + 1 <= bw);
  bzla_mem_freestr(mm, bits);
  return res;
}

bool
bzla_util_check_hex_to_bv(BzlaMemMgr *mm, const char *str, uint32_t bw)
{
  assert(mm);
  assert(str);
  assert(str[0] != '-');
  assert(bw);

  char *bits;
  bool res;

  bits = bzla_util_hex_to_bin_str(mm, str);
  res  = strlen(bits) <= bw;
  bzla_mem_freestr(mm, bits);
  return res;
}

/*------------------------------------------------------------------------*/
#ifdef BZLA_TIME_STATISTICS

#include <sys/resource.h>
#include <sys/time.h>
#include <time.h>

double
bzla_util_time_stamp(void)
{
  double res = 0;
  struct rusage u;
  if (!getrusage(RUSAGE_SELF, &u))
  {
    res += u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
    res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  }
  return res;
}

double
bzla_util_process_time_thread(void)
{
  struct timespec ts;
  double res = 0;
  if (!clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts))
    res += (double) ts.tv_sec + (double) ts.tv_nsec / 1000000000;
  return res;
}

double
bzla_util_current_time(void)
{
  double res = 0;
  struct timeval tv;
  if (!gettimeofday(&tv, 0))
  {
    res = 1e-6 * tv.tv_usec;
    res += tv.tv_sec;
  }
  return res;
}

#else

double
bzla_util_time_stamp(void)
{
  return 0;
}

double
bzla_util_process_time_thread(void)
{
  return 0;
}

double
bzla_util_current_time(void)
{
  return 0;
}

#endif

/*------------------------------------------------------------------------*/

#define BZLA_HAVE_STAT

#ifdef BZLA_HAVE_STAT
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
int32_t
bzla_util_file_exists(const char *path)
{
  struct stat buf;
  return !stat(path, &buf);
}
#else
int32_t
bzla_util_file_exists(const char *path)
{
  (void) path;
  return -1;
}
#endif

bool
bzla_util_file_has_suffix(const char *path, const char *suffix)
{
  int32_t l, k, d;
  l = strlen(path);
  k = strlen(suffix);
  d = l - k;
  if (d < 0) return 0;
  return !strcmp(path + d, suffix);
}

/*------------------------------------------------------------------------*/

#define BUFFER_SIZE 1024
#define BUFCONCAT(BUF, CLEN, NLEN, ARGS...) \
  if (NLEN < BUFFER_SIZE - 1)               \
  {                                         \
    assert(strlen(BUF) == CLEN);            \
    sprintf(BUF + CLEN, ##ARGS);            \
    CLEN = NLEN;                            \
    assert(strlen(BUF) == CLEN);            \
  }                                         \
  else                                      \
  {                                         \
    return "buffer exceeded";               \
  }

char g_bzla_strbuf[BUFFER_SIZE];
int32_t g_bzla_strbufpos = 0;

char *
bzla_util_node2string(const BzlaNode *exp)
{
  Bzla *bzla;
  BzlaNode *real_exp;
  const char *name, *tmp;
  char strbuf[BUFFER_SIZE], *bufstart, *bits;
  size_t cur_len, new_len;
  uint32_t i;

  if (!exp) return "0";

  real_exp = bzla_node_real_addr(exp);
  bzla     = real_exp->bzla;
  name     = g_bzla_op2str[real_exp->kind];

  strbuf[0] = '\0';
  cur_len   = 0;
  new_len   = bzla_util_num_digits(real_exp->id);

  if (bzla_node_is_inverted(exp)) new_len += 1;
  new_len += 1 + strlen(name); /* space + name */
  BUFCONCAT(strbuf, cur_len, new_len, "%d %s", bzla_node_get_id(exp), name);

  for (i = 0; i < real_exp->arity; i++)
  {
    new_len += 1; /* space */
    new_len += bzla_util_num_digits(bzla_node_real_addr(real_exp->e[i])->id);
    if (bzla_node_is_inverted(real_exp->e[i])) new_len += 1;
    BUFCONCAT(
        strbuf, cur_len, new_len, " %d", bzla_node_get_id(real_exp->e[i]));
  }

  if (bzla_node_is_bv_slice(real_exp))
  {
    new_len += bzla_util_num_digits(bzla_node_bv_slice_get_upper(exp)) + 1;
    new_len += bzla_util_num_digits(bzla_node_bv_slice_get_lower(exp)) + 1;
    BUFCONCAT(strbuf,
              cur_len,
              new_len,
              " %d %d",
              bzla_node_bv_slice_get_upper(exp),
              bzla_node_bv_slice_get_lower(exp));
  }
  else if ((bzla_node_is_var(real_exp) || bzla_node_is_uf(real_exp)
            || bzla_node_is_param(real_exp))
           && (tmp = bzla_node_get_symbol(bzla, real_exp)))
  {
    new_len += strlen(tmp) + 1;
    BUFCONCAT(strbuf, cur_len, new_len, " %s", tmp);
  }
  else if (bzla_node_is_bv_const(exp))
  {
    bits = bzla_bv_to_char(bzla->mm, bzla_node_bv_const_get_bits(real_exp));
    new_len += strlen(bits) + 1;
    BUFCONCAT(strbuf, cur_len, new_len, " %s", bits);
    bzla_mem_freestr(bzla->mm, bits);
  }
  else if (bzla_node_is_rm_const(exp))
  {
    new_len += 1 + 1;
    BUFCONCAT(strbuf, cur_len, new_len, " %d", bzla_node_rm_const_get_rm(exp));
  }

  assert(cur_len == strlen(strbuf));
  if (g_bzla_strbufpos + cur_len + 1 > BUFFER_SIZE - 1) g_bzla_strbufpos = 0;

  bufstart = g_bzla_strbuf + g_bzla_strbufpos;
  sprintf(bufstart, "%s", strbuf);
  g_bzla_strbufpos += cur_len + 1;

  return bufstart;
}

/*------------------------------------------------------------------------*/

char *
bzla_util_getenv_value(BzlaMemMgr *mm, const char *lname)
{
  char *res;
  BzlaCharStack uname;
  size_t i;

  BZLA_INIT_STACK(mm, uname);
  BZLA_PUSH_STACK(uname, 'B');
  BZLA_PUSH_STACK(uname, 'Z');
  BZLA_PUSH_STACK(uname, 'L');
  BZLA_PUSH_STACK(uname, 'A');

  for (i = 0; lname[i] != 0; i++)
  {
    if (lname[i] == '-' || lname[i] == '_' || lname[i] == ':') continue;
    BZLA_PUSH_STACK(uname, toupper((int32_t) lname[i]));
  }
  BZLA_PUSH_STACK(uname, 0);

  res = getenv(uname.start);
  BZLA_RELEASE_STACK(uname);
  return res;
}
