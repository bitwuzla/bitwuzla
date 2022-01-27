/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef PYBITWUZLA_ABORT_H_INCLUDED
#define PYBITWUZLA_ABORT_H_INCLUDED

#if __cplusplus
extern "C" {
#endif

void pybitwuzla_abort_fun(const char* msg);

const char* pybitwuzla_get_err_msg(void);

#if __cplusplus
}
#endif
#endif
