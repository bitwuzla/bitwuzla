/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_CMS
/*------------------------------------------------------------------------*/

#include "sat/cryptominisat.h"

namespace bzla::sat {

/* --- CryptoMiniSat public ------------------------------------------------- */

CryptoMiniSat::CryptoMiniSat() { d_solver.reset(new CMSat::SATSolver()); }

void
CryptoMiniSat::add(int32_t lit)
{
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
  const std::vector<CMSat::lbool> &model = d_solver->get_model();
  CMSat::Lit cms_lit                     = import_lit(lit);
  assert(cms_lit.var() < model.size());
  int32_t res = model[cms_lit.var()] == CMSat::l_True ? 1 : -1;
  return cms_lit.sign() ? -res : res;
}

bool
CryptoMiniSat::failed(int32_t lit)
{
  if (d_failed_map.empty()) analyze_failed();
  CMSat::Lit cms_lit = import_lit(lit);
  assert(cms_lit.var() < d_solver->nVars());
  return d_failed_map[cms_lit.var()];
}

int32_t
CryptoMiniSat::fixed(int32_t lit)
{
  if (d_assigned_map.empty()) analyze_fixed();
  CMSat::Lit cms_lit = import_lit(lit);
  uint32_t var       = cms_lit.var();
  if (var >= d_nvars) return 0;
  return cms_lit.sign() ? -d_assigned_map[var] : d_assigned_map[var];
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
  (void) terminator;
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

int32_t
CryptoMiniSat::new_var() const
{
  d_solver->new_var();
  return d_solver->nVars();
}

/* --- CryptoMiniSat private ------------------------------------------------ */

CMSat::Lit
CryptoMiniSat::import_lit(int32_t lit) const
{
  assert(lit);
  return CMSat::Lit(abs(lit) - 1, lit < 0);
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

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
