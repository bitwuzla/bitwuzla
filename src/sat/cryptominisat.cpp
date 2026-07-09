/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/*----------------------------------------------------------------------------*/
#ifdef BZLA_USE_CMS
/*----------------------------------------------------------------------------*/

#include "sat/cryptominisat.h"

#include "util/exceptions.h"

namespace bzla::sat {

/* --- CryptoMiniSat public ------------------------------------------------- */

CryptoMiniSat::CryptoMiniSat(uint32_t nthreads)
{
  assert(nthreads > 0);
  d_solver.reset(new CMSat::SATSolver());
  d_solver->set_num_threads(nthreads);
}

int32_t
CryptoMiniSat::new_var()
{
  return d_max_var++;
}

void
CryptoMiniSat::add(int32_t lit, int64_t cgroup_id)
{
  assert(std::abs(lit) < d_max_var);
  (void) cgroup_id;
  if (lit)
  {
    d_clause.push_back(import_lit(lit));
  }
  else
  {
    d_solver->add_clause(d_clause), d_clause.clear();
  }
}

void
CryptoMiniSat::assume(int32_t lit)
{
  d_assumptions.push_back(import_lit(lit));
}

int32_t
CryptoMiniSat::value(int32_t lit)
{
  assert(lit);
  const std::vector<CMSat::lbool> &model = d_solver->get_model();
  // Query the variable index directly instead of via import_lit(), which would
  // grow the solver as a side effect and index past the model. An unknown
  // literal (never added, or added after the last solve) has no model value.
  uint32_t var = std::abs(lit);
  if (var > model.size()) return 0;
  int32_t res = model[var - 1] == CMSat::l_True ? 1 : -1;
  return lit < 0 ? -res : res;
}

bool
CryptoMiniSat::failed(int32_t lit)
{
  assert(lit);
  if (d_failed_map.empty()) analyze_failed();
  // Avoid import_lit() here: it would grow the solver and read past
  // d_failed_map. An unknown literal cannot be part of the unsat core.
  uint32_t var = std::abs(lit);
  if (var > d_failed_map.size()) return false;
  return d_failed_map[var - 1];
}

int32_t
CryptoMiniSat::fixed(int32_t lit)
{
  assert(lit);
  if (d_assigned_map.empty()) analyze_fixed();
  // Avoid import_lit() here: it would grow the solver as a side effect of this
  // read-only query. An unknown literal has no implied value.
  uint32_t var = std::abs(lit);
  if (var > d_nvars) return 0;
  return lit < 0 ? -d_assigned_map[var - 1] : d_assigned_map[var - 1];
}

Result
CryptoMiniSat::solve()
{
  reset();
  CMSat::lbool res = d_solver->solve(&d_assumptions);
  d_assumptions.clear();
  if (res == CMSat::l_True) return Result::SAT;
  if (res == CMSat::l_False) return Result::UNSAT;
  return Result::UNKNOWN;
}

void
CryptoMiniSat::configure_terminator(Terminator *terminator)
{
  if (terminator)
  {
    throw Unsupported("terminator not supported in CryptoMiniSat");
  }
}

const char *
CryptoMiniSat::get_version() const
{
  return d_solver->get_version();
}

void
CryptoMiniSat::set_num_threads(uint32_t n_threads) const
{
  d_solver->set_num_threads(n_threads);
}

/* --- CryptoMiniSat private ------------------------------------------------ */

CMSat::Lit
CryptoMiniSat::import_lit(int32_t lit)
{
  assert(lit);
  uint32_t var   = std::abs(lit);
  uint32_t nvars = d_solver->nVars();
  if (var >= nvars)
  {
    d_solver->new_vars(var == nvars ? 1 : var - nvars);
  }
  return CMSat::Lit(var - 1, lit < 0);
}

void
CryptoMiniSat::analyze_failed()
{
  uint32_t nvars = d_solver->nVars();
  d_failed_map.resize(nvars);
  const std::vector<CMSat::Lit> &conflict = d_solver->get_conflict();
  for (size_t i = 0, n = conflict.size(); i < n; ++i)
  {
    uint32_t v = conflict[i].var();
    assert(v < nvars);
    d_failed_map[v] = true;
  }
}

void
CryptoMiniSat::analyze_fixed()
{
  assert(d_assigned_map.empty());
  assert(d_nvars == 0);
  d_nvars = d_solver->nVars();
  d_assigned_map.resize(d_nvars);
  const std::vector<CMSat::Lit> assigned_lits =
      d_solver->get_zero_assigned_lits();
  for (size_t i = 0, n = assigned_lits.size(); i < n; ++i)
  {
    CMSat::Lit cms_lit = assigned_lits[i];
    assert(cms_lit.var() < d_nvars);
    d_assigned_map[cms_lit.var()] = cms_lit.sign() ? -1 : 1;
  }
}

void
CryptoMiniSat::reset()
{
  d_failed_map.clear();
  d_assigned_map.clear();
  d_nvars = 0;
}

}  // namespace bzla::sat

/*----------------------------------------------------------------------------*/
#endif
/*----------------------------------------------------------------------------*/
