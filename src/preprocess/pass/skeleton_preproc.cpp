/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/skeleton_preproc.h"

#include <cadical/cadical.hpp>
#include <memory>

#include "bitblast/aig/aig_cnf.h"
#include "bitblast/aig_bitblaster.h"
#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#ifdef BZLA_USE_CADICAL
#include "sat/cadical.h"
#endif
#include "solver/bv/aig_bitblaster.h"

namespace bzla::preprocess::pass {

using namespace node;

class FixedListener : public CaDiCaL::FixedAssignmentListener
{
 public:
  ~FixedListener() {};

  void notify_fixed_assignment(int32_t lit) override { d_fixed.push_back(lit); }

  const auto& fixed() const { return d_fixed; }

 private:
  std::vector<int32_t> d_fixed;
};

class CnfSatInterface : public bitblast::SatInterface
{
 public:
  CnfSatInterface(sat::Cadical& solver) : d_solver(solver) {}

  void add(int64_t lit, int64_t aig_id = 0) override
  {
    (void) aig_id;
    d_solver.add(lit);
  }

  void add_clause(const std::initializer_list<int64_t>& literals,
                  int64_t aig_id = 0) override
  {
    for (const auto& lit : literals)
    {
      add(lit, aig_id);
    }
    add(0, aig_id);
  }

  bool value(int64_t lit) override
  {
    (void) lit;
    assert(false);
    return false;
  }

 private:
  sat::Cadical& d_solver;
};

/* --- PassSkeletonPreproc public ------------------------------------------- */

PassSkeletonPreproc::PassSkeletonPreproc(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "sp", "skeleton_preproc"),
      d_sat_solver(nullptr),
      d_assertion_lits(backtrack_mgr),
      d_assertions(backtrack_mgr),
      d_reset(backtrack_mgr),
      d_stats(env.statistics(), "preprocess::" + name() + "::")
{
}

PassSkeletonPreproc::~PassSkeletonPreproc() {}

void
PassSkeletonPreproc::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);
  (void) assertions;
#ifdef BZLA_USE_CADICAL
  // Disabled if unsat cores enabled.
  if (d_env.options().produce_unsat_cores())
  {
    return;
  }
  // New assertions introduced by this pass do not have a single 'parent',
  // and thus the assertion tracker does not yet support tracking this pass.
  // Both unsat cores and interpolants generation rely on the assertion tracker,
  // thus we disable this pass when either is enabled.
  // Note: If we reenable this pass for both in the future we will probably
  //       need separate tracker instances for each (they likely will require
  //       different tracking for this pass).
  if (d_env.options().produce_unsat_cores()
      || d_env.options().produce_interpolants())
  {
    return;
  }

  if (d_done)
  {
    return;
  }

  std::vector<Node> _assertions;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (assertion.is_value())
    {
      continue;
    }
    if (!processed(assertion))
    {
      cache_assertion(assertion);
      _assertions.push_back(assertion);
    }
  }

  // No new assertions encoded
  if (_assertions.empty())
  {
    return;
  }

  // Reset SAT solver if assertions were popped
  if (d_reset())
  {
    d_sat_solver.reset(new sat::Cadical());
    d_fixed_listener.reset(new FixedListener());
    d_sat_solver->solver()->connect_fixed_listener(d_fixed_listener.get());
    d_encode_cache.clear();
    d_reset = false;
    ++d_stats.num_resets;
  }

  CnfSatInterface cnf_sat(*d_sat_solver);
  bv::AigBitblaster bitblaster(true);
  bitblast::AigCnfEncoder cnf_encoder(cnf_sat);
  std::unordered_map<Node, bitblast::AigBitblaster::Bits> bb_cache;

  // Encode Boolean skeleton
  {
    util::Timer timer(d_stats.time_encode);
    for (const Node& assertion : _assertions)
    {
      bitblaster.bitblast(assertion);
      const auto& bits = bitblaster.bits(assertion);
      cnf_encoder.encode(bits[0], true);
      d_assertion_lits.insert(bits[0].get_id());
      d_assertions.push_back(assertion);
    }
  }

  d_stats.num_cnf_clauses = cnf_encoder.statistics().num_clauses;
  d_stats.num_cnf_lits    = cnf_encoder.statistics().num_literals;

  {
    util::Timer timer(d_stats.time_sat);
    d_sat_solver->solver()->simplify();
  }

  std::unordered_map<uint64_t, Node> node_map;
  for (const auto& [n, bits] : bb_cache)
  {
    assert(bits.size() == 1);
    const auto& aig = bits[0];
    node_map.emplace(aig.get_id(), n);
  }

  NodeManager& nm = d_env.nm();
  Rewriter& rw    = d_env.rewriter();
  for (const auto& lit : d_fixed_listener->fixed())
  {
    if (d_assertion_lits.find(lit) == d_assertion_lits.end())
    {
      bool inv = false;
      auto it  = node_map.find(lit);
      if (it == node_map.end())
      {
        it  = node_map.find(-lit);
        inv = true;
        if (it == node_map.end())
        {
          // Skip AIG internal nodes
          ++d_stats.num_fixed_unused;
          continue;
        }
      }

      Node new_assert = rw.invert_node_if(inv, it->second);
      if (new_assert.type().is_bv())
      {
        new_assert = nm.mk_node(
            Kind::EQUAL, {new_assert, nm.mk_value(BitVector::mk_true())});
      }

      assertions.push_back(new_assert, Node());
      ++d_stats.num_new_assertions;
    }
  }
  d_done = true;
  d_sat_solver.reset(new sat::Cadical());
  d_encode_cache.clear();
#endif
}

/* --- PassSkeletonPreproc private ------------------------------------------ */

int64_t
PassSkeletonPreproc::lit(const Node& term)
{
  assert(term.type().is_bool()
         || (term.type().is_bv() && term.type().bv_size() == 1));
  return (term.kind() == Kind::NOT || term.kind() == Kind::BV_NOT)
             ? -term[0].id()
             : term.id();
}

PassSkeletonPreproc::Statistics::Statistics(util::Statistics& stats,
                                            const std::string& prefix)
    : time_sat(stats.new_stat<util::TimerStatistic>(prefix + "time_sat")),
      time_encode(stats.new_stat<util::TimerStatistic>(prefix + "time_encode")),
      num_new_assertions(stats.new_stat<uint64_t>(prefix + "new_assertions")),
      num_resets(stats.new_stat<uint64_t>(prefix + "resets")),
      num_cnf_lits(stats.new_stat<uint64_t>(prefix + "cnf::lits")),
      num_cnf_clauses(stats.new_stat<uint64_t>(prefix + "cnf::clauses")),
      num_fixed_unused(stats.new_stat<uint64_t>(prefix + "fixed::unused"))
{
}

}  // namespace bzla::preprocess::pass
