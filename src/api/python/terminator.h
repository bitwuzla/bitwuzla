/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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
