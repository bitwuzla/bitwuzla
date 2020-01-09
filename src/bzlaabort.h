/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2020 Aina Niemetz
 *  Copyright (C) 2013-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BZLAABORT_H_INCLUDED
#define BZLAABORT_H_INCLUDED

#include <stdbool.h>
#include <stdlib.h>

#include "bzlatypes.h"

/*------------------------------------------------------------------------*/

#define BZLA_WARN(cond, msg...)                                      \
  do                                                                 \
  {                                                                  \
    if (cond) bzla_abort_warn(false, __FILE__, __FUNCTION__, ##msg); \
  } while (0)

#define BZLA_WARN_DEPRECATED(msg...)                             \
  do                                                             \
  {                                                              \
    fprintf(stderr,                                              \
            "[%s] function %s is deprecated, use %s instead \n", \
            __FILE__,                                            \
            __FUNCTION__,                                        \
            ##msg);                                              \
    fflush(stderr);                                              \
  } while (0)

/*------------------------------------------------------------------------*/

void bzla_abort_fun(const char* msg);

void bzla_abort_warn(
    bool abort, const char* filename, const char* fun, const char* fmt, ...);

#define BZLA_ABORT(cond, msg...)                                    \
  do                                                                \
  {                                                                 \
    if (cond) bzla_abort_warn(true, __FILE__, __FUNCTION__, ##msg); \
  } while (0)

#define BZLA_ABORT_ARG_NULL(arg)                             \
  do                                                         \
  {                                                          \
    BZLA_ABORT((arg) == 0, "'%s' must not be NULL\n", #arg); \
  } while (0)

#define BZLA_ABORT_REFS_NOT_POS(arg)                          \
  do                                                          \
  {                                                           \
    BZLA_ABORT(bzla_node_real_addr(arg)->ext_refs < 1,        \
               "reference counter of '%s' must not be < 1\n", \
               #arg);                                         \
  } while (0)

#define BZLA_ABORT_BZLA_MISMATCH(argbtor, argnode)                        \
  do                                                                      \
  {                                                                       \
    BZLA_ABORT(bzla_node_real_addr(argnode)->bzla != (argbtor),           \
               "argument '%s' belongs to different Boolector instance\n", \
               #argnode);                                                 \
  } while (0)

#define BZLA_ABORT_IS_NOT_BV(arg)                                          \
  do                                                                       \
  {                                                                        \
    BZLA_ABORT(                                                            \
        !bzla_node_is_bv(bzla, arg), "'%s' must be a bit-vector\n", #arg); \
  } while (0)

#define BZLA_ABORT_IS_NOT_ARRAY(arg)                                       \
  do                                                                       \
  {                                                                        \
    BZLA_ABORT(!bzla_node_is_array(arg), "'%s' must be an array\n", #arg); \
  } while (0)

#define BZLA_ABORT_IS_NOT_FP(arg)                                              \
  do                                                                           \
  {                                                                            \
    BZLA_ABORT(                                                                \
        !bzla_node_is_fp(bzla, arg), "'%s' must be a floating-point\n", #arg); \
  } while (0)

#define BZLA_ABORT_IS_NOT_FP(arg)                                              \
  do                                                                           \
  {                                                                            \
    BZLA_ABORT(                                                                \
        !bzla_node_is_fp(bzla, arg), "'%s' must be a floating-point\n", #arg); \
  } while (0)

#define BZLA_ABORT_IS_NOT_RM(arg)                                  \
  do                                                               \
  {                                                                \
    BZLA_ABORT(!bzla_sort_is_rm(bzla, bzla_node_get_sort_id(arg)), \
               "'%s' must be a rounding mode\n",                   \
               #arg);                                              \
  } while (0)

#define BZLA_ABORT_IS_NOT_FUN(arg)                                  \
  do                                                                \
  {                                                                 \
    BZLA_ABORT(!bzla_sort_is_fun(bzla, bzla_node_get_sort_id(arg)), \
               "'%s' must be a function\n",                         \
               #arg);                                               \
  } while (0)

#define BZLA_ABORT_SORT_MISMATCH(argbw1, argbw2)                               \
  do                                                                           \
  {                                                                            \
    BZLA_ABORT(bzla_node_get_sort_id(argbw1) != bzla_node_get_sort_id(argbw2), \
               "sorts of '%s' and '%s' must match\n",                          \
               #argbw1,                                                        \
               #argbw2);                                                       \
  } while (0)

/*------------------------------------------------------------------------*/

#endif
