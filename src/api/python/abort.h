/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BITWUZLA_PY_ABORT_H_INCLUDED
#define BITWUZLA_PY_ABORT_H_INCLUDED

#if __cplusplus
extern "C" {
#endif

void py_bitwuzla_abort_fun(const char* msg);

const char* py_bitwuzla_get_err_msg(void);

#if __cplusplus
}
#endif
#endif
