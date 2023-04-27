#include "terminator.h"

PyTerminator::PyTerminator(PyObject* terminator) : d_terminator(terminator)
{
  Py_XINCREF(terminator);
}

PyTerminator::~PyTerminator()
{
  if (d_terminator)
  {
    Py_XDECREF(d_terminator);
  }
}

bool
PyTerminator::terminate()
{
  PyGILState_STATE gstate = PyGILState_Ensure();
  PyObject* res           = PyObject_CallObject(d_terminator, nullptr);
  if (PyErr_Occurred())
  {
    PyErr_Print();
  }
  bool ret = res == Py_True;
  Py_XDECREF(res);
  PyGILState_Release(gstate);
  return ret;
}
