/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_MALLOB_H_INCLUDED
#define BZLA_SAT_MALLOB_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_MALLOB
/*------------------------------------------------------------------------*/

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "sat/sat_solver.h"
#include "solver/result.h"
#include "terminator.h"

namespace bzla::sat {

class MallobDaemon;

/**
 * Backend for Mallob (https://github.com/domschrei/mallob), a distributed
 * SAT solving platform.
 *
 * Mallob is an MPI application rather than a library. This backend acts as a
 * client of a running Mallob process (or cluster) via Mallob's filesystem
 * JSON API: each call to solve() writes the current CNF to a DIMACS file,
 * submits a one-shot SAT job to `<api-dir>/in/` and waits for the result
 * JSON in `<api-dir>/out/`.
 *
 * The Mallob process is either managed externally (option --mallob-api-dir
 * points to the job API directory of a running Mallob process, default
 * `.api/jobs.0`), or, if option --mallob-binary is set, launched and managed
 * automatically (see MallobDaemon in mallob.cpp).
 *
 * Assumptions are encoded as unit clauses of a fresh one-shot job (as in the
 * Gimsatul backend), thus failed() is not supported. Termination requests
 * are forwarded to Mallob by interrupting the submitted job.
 */
class Mallob : public SatSolver
{
 public:
  /**
   * Constructor.
   * @param api_dir  The job API directory of an externally managed Mallob
   *                 process (used if `binary` is empty).
   * @param binary   Path to the Mallob binary. If non-empty, a Mallob
   *                 process is launched and managed automatically and
   *                 `api_dir` is ignored.
   * @param launcher Launcher prefix (e.g. "mpirun -np 4") for the managed
   *                 Mallob process.
   * @param args     Additional arguments for the managed Mallob process.
   * @param nthreads Number of solver threads (-t) for the managed Mallob
   *                 process, 0 to use all available cores.
   */
  Mallob(const std::string &api_dir,
         const std::string &binary,
         const std::string &launcher,
         const std::string &args,
         uint32_t nthreads);
  ~Mallob();

  int32_t new_var() override;
  void add(int32_t lit, int64_t cgroup_id = 0) override;
  void assume(int32_t lit) override;
  int32_t value(int32_t lit) override;
  bool failed(int32_t lit) override;
  int32_t fixed(int32_t lit) override;
  Result solve() override;
  void configure_terminator(Terminator *terminator) override;
  const char *get_name() const override { return "Mallob"; }
  const char *get_version() const override;

 private:
  /** Get the job API directory, launching a managed Mallob if configured. */
  const std::string &api_dir();
  /** Write the current formula (plus assumptions as units) as DIMACS. */
  void write_dimacs(const std::string &path) const;
  /** Atomically place a job JSON file in `<api-dir>/in/`. */
  void submit_json(const std::string &file_name, const std::string &contents);
  /** Wait for the result JSON of the given job, forwarding termination
   *  requests as job interrupts. Returns false if no result could be
   *  retrieved (only possible after a termination request). */
  bool wait_for_result(const std::string &job_name,
                       const std::string &result_path);
  /** Extract the model from a result JSON (inline array or named pipe). */
  void parse_model(const std::string &json);

  /** The Mallob job API base directory (containing `in/` and `out/`). */
  std::string d_api_dir;
  /** Managed mode configuration (managed mode iff d_binary is non-empty). */
  std::string d_binary;
  std::string d_launcher;
  std::string d_args;
  uint32_t d_nthreads = 0;
  /** The managed Mallob process, shared between solver instances. */
  std::shared_ptr<MallobDaemon> d_daemon;
  /** Process-unique job name prefix of this solver instance. */
  std::string d_job_prefix;
  /** Number of solve() calls, used to make job names unique. */
  uint64_t d_num_solves = 0;
  Terminator *d_terminator = nullptr;
  int32_t d_max_var        = 1;
  int64_t d_num_clauses    = 0;
  std::vector<int32_t> d_literals;
  std::vector<int32_t> d_assumptions;
  /** Model of the last SAT result, indexed by variable, values -1/0/1. */
  std::vector<int8_t> d_model;
};

}  // namespace bzla::sat

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
