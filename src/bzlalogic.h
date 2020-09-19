/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
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
  BZLA_LOGIC_QF_AUFBV,
  BZLA_LOGIC_QF_BV,
  BZLA_LOGIC_QF_UFBV,
  BZLA_LOGIC_ALL,
};

typedef enum BzlaLogic BzlaLogic;

#endif
