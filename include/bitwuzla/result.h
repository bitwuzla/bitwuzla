/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#if (!defined(BITWUZLA_API_USE_C_ENUMS)               \
     && !defined(BITWUZLA_API_RESULT_CPP_H_INCLUDED)) \
    || (defined(BITWUZLA_API_USE_C_ENUMS)             \
        && !defined(BITWUZLA_API_RESULT_C_H_INCLUDED))

#ifdef BITWUZLA_API_USE_C_ENUMS
#define EVALUE(name) BITWUZLA_##name
#endif

#ifndef BITWUZLA_API_USE_C_ENUMS
#include <iostream>
namespace bitwuzla {
#define ENUM(name) class name
#define EVALUE(name) name
#else
#define ENUM(name) Bitwuzla##name
#endif

/** A satisfiability result. */
enum ENUM(Result)
{
  EVALUE(SAT)     = 10,  ///< sat
  EVALUE(UNSAT)   = 20,  ///< unsat
  EVALUE(UNKNOWN) = 0,   ///< unknown
};

#ifdef BITWUZLA_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum ENUM(Result) ENUM(Result);
#endif
#endif

#undef ENUM
#undef EVALUE

#ifndef BITWUZLA_API_USE_C_ENUMS
std::ostream& operator<<(std::ostream& out, Result r);
}  // namespace bitwuzla
namespace std {
std::string to_string(bitwuzla::Result result);
}  // namespace std
#endif

#endif

#ifndef BITWUZLA_API_USE_C_ENUMS
#ifndef BITWUZLA_API_RESULT_CPP_H_INCLUDED
#define BITWUZLA_API_RESULT_CPP_H_INCLUDED
#endif
#else
#ifndef BITWUZLA_API_RESULT_C_H_INCLUDED
#define BITWUZLA_API_RESULT_C_H_INCLUDED
#endif
#endif
