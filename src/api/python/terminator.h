#ifndef BITWUZLA_PY_TERMINATOR_H_INCLUDED
#define BITWUZLA_PY_TERMINATOR_H_INCLUDED

#include <Python.h>
#include <bitwuzla/cpp/bitwuzla.h>

class PyTerminator : public bitwuzla::Terminator
{
 public:
  PyTerminator() = delete;
  PyTerminator(PyObject* terminator);
  ~PyTerminator();

  bool terminate() override;

 private:
  PyObject* d_terminator = nullptr;
};

#endif
