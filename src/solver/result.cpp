#include "solver/result.h"

namespace bzla {

std::ostream&
operator<<(std::ostream& out, const Result& r)
{
  switch (r)
  {
    case Result::SAT: out << "sat"; break;
    case Result::UNSAT: out << "unsat"; break;
    case Result::UNKNOWN: out << "unknown"; break;
  }
  return out;
}

}  // namespace bzla
