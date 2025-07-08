/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/fp/symfpu_floating_point_typeinfo.h"

#include "node/node_manager.h"
#include "solver/fp/symfpu_nm.h"

namespace bzla {

/* --- SymFPUFloatingPointTypeInfo public ----------------------------------- */

SymFPUFloatingPointTypeInfo::SymFPUFloatingPointTypeInfo(const Type &type)
    : d_esize(type.fp_exp_size()), d_ssize(type.fp_sig_size())
{
  assert(type.is_fp());
  d_type = type;
}

SymFPUFloatingPointTypeInfo::SymFPUFloatingPointTypeInfo(uint32_t esize,
                                                         uint32_t ssize)
    : d_esize(esize), d_ssize(ssize)
{
  NodeManager &nm = fp::SymFpuNM::get();
  d_type          = nm.mk_fp_type(esize, ssize);
}

SymFPUFloatingPointTypeInfo::SymFPUFloatingPointTypeInfo(
    const SymFPUFloatingPointTypeInfo &other)
    : d_esize(other.d_esize), d_ssize(other.d_ssize)
{
  assert(other.d_type.is_fp());
  d_type = other.d_type;
}

SymFPUFloatingPointTypeInfo::~SymFPUFloatingPointTypeInfo() {}

const Type &
SymFPUFloatingPointTypeInfo::type() const
{
  return d_type;
}

std::string
SymFPUFloatingPointTypeInfo::str() const
{
  return d_type.str();
}

std::ostream &
operator<<(std::ostream &out, const SymFPUFloatingPointTypeInfo &type)
{
  out << type.str();
  return out;
}

}  // namespace bzla
