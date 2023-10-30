/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <cassert>

namespace bzla {

class NodeManager;

namespace fp {

class SymFpuNM
{
 public:
  static thread_local NodeManager *s_nm;

  SymFpuNM(NodeManager &nm)
  {
    d_prev_nm = s_nm;
    s_nm      = &nm;
  }

  ~SymFpuNM() { s_nm = d_prev_nm; }

  static NodeManager &get()
  {
    assert(s_nm != nullptr);
    return *s_nm;
  }

 private:
  NodeManager *d_prev_nm = nullptr;
};

}  // namespace fp
}  // namespace bzla
