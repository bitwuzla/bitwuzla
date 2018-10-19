/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2020 Aina Niemetz.
 *  Copyright (C) 2013-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */
#ifndef BZLATRAPI_H_INCLUDED
#define BZLATRAPI_H_INCLUDED

#include <stdio.h>

#include "bzlacore.h"

#define BZLA_TRAPI_NODE_FMT "n%d@%p "
#define BZLA_TRAPI_SORT_FMT "s%d@%p "

#define BZLA_TRAPI_NODE_ID(exp)                                             \
  (bzla_node_is_inverted(exp) ? -bzla_node_real_addr(exp)->id : (exp)->id), \
      bzla_node_real_addr(exp)->bzla

#define BZLA_TRAPI_PRINT(args...)   \
  do                                \
  {                                 \
    if (!bzla->apitrace) break;     \
    bzla_trapi_print(bzla, ##args); \
  } while (0)

#define BZLA_TRAPI(args...)                 \
  do                                        \
  {                                         \
    if (!bzla->apitrace) break;             \
    bzla_trapi(bzla, __FUNCTION__, ##args); \
  } while (0)

#define BZLA_TRAPI_AUX(fun, args...) \
  do                                 \
  {                                  \
    if (!bzla->apitrace) break;      \
    bzla_trapi(bzla, fun, ##args);   \
  } while (0)

#define BZLA_TRAPI_RETURN(args...) \
  do                               \
  {                                \
    if (!bzla->apitrace) break;    \
    bzla_trapi(bzla, 0, ##args);   \
  } while (0)

#define BZLA_TRAPI_UNFUN_EXT(exp, fmt, args...) \
  BZLA_TRAPI(BZLA_TRAPI_NODE_FMT fmt, BZLA_TRAPI_NODE_ID(exp), ##args)

#define BZLA_TRAPI_UNFUN(exp) \
  BZLA_TRAPI(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(exp))

#define BZLA_TRAPI_BINFUN(e0, e1)                     \
  BZLA_TRAPI(BZLA_TRAPI_NODE_FMT BZLA_TRAPI_NODE_FMT, \
             BZLA_TRAPI_NODE_ID(e0),                  \
             BZLA_TRAPI_NODE_ID(e1))

#define BZLA_TRAPI_BINFUN_EXT(e0, e1, fmt, args...)       \
  BZLA_TRAPI(BZLA_TRAPI_NODE_FMT BZLA_TRAPI_NODE_FMT fmt, \
             BZLA_TRAPI_NODE_ID(e0),                      \
             BZLA_TRAPI_NODE_ID(e1),                      \
             ##args)

#define BZLA_TRAPI_TERFUN(e0, e1, e2)                                     \
  BZLA_TRAPI(BZLA_TRAPI_NODE_FMT BZLA_TRAPI_NODE_FMT BZLA_TRAPI_NODE_FMT, \
             BZLA_TRAPI_NODE_ID(e0),                                      \
             BZLA_TRAPI_NODE_ID(e1),                                      \
             BZLA_TRAPI_NODE_ID(e2))

#define BZLA_TRAPI_RETURN_NODE(res)                                    \
  do                                                                   \
  {                                                                    \
    if (res)                                                           \
    {                                                                  \
      BZLA_TRAPI_RETURN(BZLA_TRAPI_NODE_FMT, BZLA_TRAPI_NODE_ID(res)); \
    }                                                                  \
    else                                                               \
    {                                                                  \
      BZLA_TRAPI_RETURN("(nil)@%p");                                   \
    }                                                                  \
  } while (0)

#define BZLA_TRAPI_RETURN_PTR(res) BZLA_TRAPI_RETURN("%p", res)

#define BZLA_TRAPI_RETURN_STR(res) BZLA_TRAPI_RETURN("%s", res)

#define BZLA_TRAPI_RETURN_INT(res) BZLA_TRAPI_RETURN("%d", res)

#define BZLA_TRAPI_RETURN_UINT(res) BZLA_TRAPI_RETURN("%u", res)

#define BZLA_TRAPI_RETURN_BOOL(res) \
  BZLA_TRAPI_RETURN("%s", (res) ? "true" : "false")

#define BZLA_TRAPI_RETURN_SORT(sort) \
  BZLA_TRAPI_RETURN(BZLA_TRAPI_SORT_FMT, sort, bzla)

void bzla_trapi_print(Bzla* bzla, const char* msg, ...);

void bzla_trapi(Bzla* bzla, const char* fname, const char* msg, ...);

void bzla_trapi_open_trace(Bzla* bzla, const char* name);
#endif
