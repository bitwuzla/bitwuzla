/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2015-2018 Mathias Preiner.
 *  Copyright (C) 2018-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLALOGIC_H_INCLUDED
#define BZLALOGIC_H_INCLUDED

enum BzlaLogic
{
  BZLA_LOGIC_BV,
  BZLA_LOGIC_QF_ABV,
  BZLA_LOGIC_QF_ABVFP,
  BZLA_LOGIC_QF_AUFBV,
  BZLA_LOGIC_QF_BV,
  BZLA_LOGIC_QF_BVFP,
  BZLA_LOGIC_QF_FP,
  BZLA_LOGIC_QF_UFBV,
  BZLA_LOGIC_QF_UFFP,
  BZLA_LOGIC_ALL,
};

typedef enum BzlaLogic BzlaLogic;

#endif
