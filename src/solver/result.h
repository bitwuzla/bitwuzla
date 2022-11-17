#ifndef BZLA_SOLVER_RESULT_H_INCLUDED
#define BZLA_SOLVER_RESULT_H_INCLUDED

#include <iostream>

namespace bzla {

enum class Result
{
  SAT,
  UNSAT,
  UNKNOWN
};

std::ostream& operator<<(std::ostream& out, const Result& r);

}  // namespace bzla

#endif
