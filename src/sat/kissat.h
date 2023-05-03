#ifndef BZLA_SAT_KISSAT_H_INCLUDED
#define BZLA_SAT_KISSAT_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_KISSAT
/*------------------------------------------------------------------------*/

extern "C" {
#include <kissat.h>
}

#include <memory>

#include "sat/sat_solver.h"

namespace bzla::sat {

class Kissat : public SatSolver
{
 public:
  Kissat();
  ~Kissat();

  void add(int32_t lit) override;
  void assume(int32_t lit) override;
  int32_t value(int32_t lit) override;
  bool failed(int32_t lit) override;
  int32_t fixed(int32_t lit) override;
  Result solve() override;
  void configure_terminator(Terminator *terminator) override;
  const char *get_name() const override { return "Kissat"; }
  const char *get_version() const override;

 private:
  kissat *d_solver = nullptr;
};

}  // namespace bzla::sat

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
