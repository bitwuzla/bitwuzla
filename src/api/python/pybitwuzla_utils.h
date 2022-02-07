/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef PYBITWUZLA_UTILS_H_INCLUDED
#define PYBITWUZLA_UTILS_H_INCLUDED

#include <Python.h>

#include "bitwuzla.h"

#if __cplusplus
extern "C" {
#endif

/*!
   Set a Python termination callback.

   :param bzla:  Bitwuzla instance.
   :param fun:   The termination callback Python function.
   :param state: The Python argument(s) to the termination callback function.

  .. note::
    This function is for Python API use only.
 */
void pybitwuzla_set_term(Bitwuzla* bitwuzla, PyObject* fun, PyObject* state);

/*!
  Delete a Bitwuzla instance (with possibly defined Python function
  callbacks) and free its resources.

  :param bzla: Bitwuzla instance.

  .. seealso::
    bitwuzla_delete

  .. note::
    This function is for Python API use only.
*/
void pybitwuzla_delete(Bitwuzla* bitwuzla);

#if __cplusplus
}
#endif
#endif
