/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "pybitwuzla_utils.h"

#include <assert.h>
#include <stdlib.h>

#include "utils/bzlaabort.h"

struct CallbackState
{
  int32_t (*callback)(void *);

  PyObject *fun;
  PyObject *state;
  uint32_t done;
};
typedef struct CallbackState CallbackState;

static int32_t
terminate_callback(void *state)
{
  assert(state);

  PyObject *res;
  PyGILState_STATE gstate;
  CallbackState *cbstate;

  gstate  = PyGILState_Ensure();
  cbstate = (CallbackState *) state;
  if (!cbstate->fun) return 0;
  if (cbstate->done) return 1;
  res = PyObject_CallObject((PyObject *) cbstate->fun,
                            (PyObject *) cbstate->state);
  if (PyErr_Occurred()) PyErr_Print();
  BZLA_ABORT(!res, "call to callback termination function failed");
  BZLA_ABORT(!PyBool_Check(res),
             "expected Boolean result for termination callback");
  if (res == Py_True)
  {
    cbstate->done = 1;
  }
  else
  {
    cbstate->done = 0;
  }
  Py_DECREF(res);
  PyGILState_Release(gstate);
  return cbstate->done;
}

void
pybitwuzla_set_term(Bitwuzla *bitwuzla, PyObject *fun, PyObject *state)
{
  assert(bitwuzla);

  Py_ssize_t i, size;
  PyObject *t, *tmp;
  CallbackState *cbstate;

  BZLA_ABORT(!PyCallable_Check(fun),
             "termination callback parameter is not callable");

  Py_XINCREF(fun);   /* inc ref to new callback */
  Py_XINCREF(state); /* inc ref to new state */

  cbstate = bitwuzla_get_termination_callback_state(bitwuzla);
  if (cbstate)
  {
    if (cbstate->fun) /* dec ref to prev callback */
    {
      Py_XDECREF((PyObject *) cbstate->fun);
    }
    if (cbstate->state) /* dec ref to prev state */
    {
      Py_XDECREF((PyObject *) cbstate->state);
    }
  }
  else
  {
    cbstate = (CallbackState *) malloc(sizeof(CallbackState));
    memset(cbstate, 0, sizeof(CallbackState));
  }

  cbstate->fun = fun;

  if (PyObject_TypeCheck(state, &PyTuple_Type))
  {
    Py_XINCREF(state);
    cbstate->state = state;
  }
  else if (PyObject_TypeCheck(state, &PyList_Type))
  {
    size = PyList_Size(state);
    tmp  = PyTuple_New(size);
    for (i = 0; i < size; i++)
    {
      t = PyList_GetItem(state, i);
      Py_XINCREF(t);
      PyTuple_SetItem(tmp, i, t);
    }
    cbstate->state = tmp;
  }
  else
  {
    Py_XINCREF(state);
    tmp = PyTuple_New(1);
    PyTuple_SetItem(tmp, 0, state);
    cbstate->state = tmp;
  }

  bitwuzla_set_termination_callback(bitwuzla, terminate_callback, cbstate);
}

void
pybitwuzla_delete(Bitwuzla *bitwuzla)
{
  assert(bitwuzla);
  CallbackState *cbstate = bitwuzla_get_termination_callback_state(bitwuzla);
  if (cbstate)
  {
    if (cbstate->fun)
    {
      Py_XDECREF(cbstate->fun);
    }
    if (cbstate->state)
    {
      Py_XDECREF(cbstate->state);
    }
  }
  bitwuzla_delete(bitwuzla);
}
