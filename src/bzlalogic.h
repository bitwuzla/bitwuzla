/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLALOGIC_H_INCLUDED
#define BZLALOGIC_H_INCLUDED

enum BzlaLogic
{
  BZLA_LOGIC_BV,
  BZLA_LOGIC_UFBV,
  BZLA_LOGIC_FP,
  BZLA_LOGIC_QF_ABV,
  BZLA_LOGIC_QF_ABVFP,
  BZLA_LOGIC_QF_ABVFPLRA,
  BZLA_LOGIC_QF_AUFBV,
  BZLA_LOGIC_QF_AUFBVFP,
  BZLA_LOGIC_QF_BV,
  BZLA_LOGIC_QF_BVFP,
  BZLA_LOGIC_QF_FP,
  BZLA_LOGIC_QF_UFBV,
  BZLA_LOGIC_QF_UFFP,
  BZLA_LOGIC_ALL,
};

typedef enum BzlaLogic BzlaLogic;

#endif
