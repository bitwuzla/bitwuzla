#include "solver/bv/bv_prop_solver.h"

#include <iostream>

#include "ls/bv/bitvector_domain.h"
#include "ls/ls_bv.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_set.h"
#include "option/option.h"
#include "solver/bv/bv_solver.h"
#include "solver/result.h"
#include "solving_context.h"
namespace bzla::bv {

using namespace bzla::node;

BvPropSolver::BvPropSolver(Env& env,
                           SolverState& state,
                           BvBitblastSolver& bb_solver)
    : Solver(env, state), d_bb_solver(bb_solver)
{
  const option::Options& options = d_env.options();

  d_ls.reset(new ls::LocalSearchBV(
      options.prop_nprops(), options.prop_nupdates(), options.seed()));

  d_ls->d_options.use_ineq_bounds        = options.prop_ineq_bounds();
  d_ls->d_options.use_opt_lt_concat_sext = options.prop_opt_lt_concat_sext();
  d_ls->d_options.prob_pick_inv_value    = options.prop_prob_pick_inv_value();
  d_ls->d_options.use_path_sel_essential =
      options.prop_path_sel() == option::PropPathSelection::ESSENTIAL;

  d_ls->d_options.prob_pick_ess_input =
      1000 - options.prop_prob_pick_random_input();

  d_ls->set_log_level(options.log_level());
  d_ls->init();

  d_use_sext       = options.prop_sext();
  d_use_const_bits = options.prop_const_bits();
}

BvPropSolver::~BvPropSolver() {}

Result
BvPropSolver::solve()
{
  // double start                = bzla_util_time_stamp();
  Result sat_result = Result::UNKNOWN;

  uint32_t verbosity = d_env.options().verbosity();
  uint64_t nprops    = d_env.options().prop_nprops();
  uint64_t nupdates  = d_env.options().prop_nupdates();

  uint32_t progress_steps     = 100;
  uint32_t progress_steps_inc = progress_steps * 10;

  // incremental: increase limit by given nprops/nupdates
  nprops += d_ls->d_statistics.d_nprops;
  d_ls->set_max_nprops(nprops);
  // BZLA_MSG(d_bzla->msg, 1, "Set propagation limit to %zu", nprops);
  nupdates += d_ls->d_statistics.d_nupdates;
  d_ls->set_max_nupdates(nupdates);
  // BZLA_MSG(d_bzla->msg, 1, "Set model update limit to %zu", nupdates);

  for (uint32_t j = 0;; ++j)
  {
    if (d_env.terminate() || (nprops && d_ls->d_statistics.d_nprops >= nprops)
        || (nupdates && d_ls->d_statistics.d_nupdates >= nupdates))
    {
      assert(sat_result == Result::UNKNOWN);
      goto DONE;
    }

    if (verbosity > 0 && j % progress_steps == 0)
    {
      // print_progress();
      if (j <= 1000000 && j >= progress_steps_inc)
      {
        progress_steps = progress_steps_inc;
        progress_steps_inc *= 10;
      }
    }

    bzla::ls::Result res = d_ls->move();

    if (res == bzla::ls::Result::UNSAT)
    {
      goto UNSAT;
    }

    if (res == bzla::ls::Result::SAT)
    {
      goto SAT;
    }
  }

SAT:
  sat_result = Result::SAT;
  goto DONE;
UNSAT:
  sat_result = Result::UNSAT;
DONE:
  // print_progress();

  // d_time_statistics.d_check_sat += bzla_util_time_stamp() - start;

  return sat_result;
}

void
BvPropSolver::register_assertion(const Node& assertion, bool top_level)
{
  (void) top_level;

  node::node_ref_vector visit{assertion};
  node::unordered_node_ref_set cache;

  if (d_use_const_bits)
  {
    d_bb_solver.bitblast(assertion);
  }

  while (!visit.empty())
  {
    const Node& cur = visit.back();
    visit.pop_back();

    if (d_node_map.find(cur) != d_node_map.end()) continue;

    if (cache.find(cur) != cache.end())
    {
      d_node_map[cur] = mk_node(cur);
    }
    else
    {
      cache.emplace(cur);
      visit.push_back(cur);
      if (!BvSolver::is_leaf(cur))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  }

  d_ls->register_root(d_node_map.at(assertion));
}

Node
BvPropSolver::value(const Node& term)
{
  assert(BvSolver::is_leaf(term));
  auto it = d_node_map.find(term);
  assert(it != d_node_map.end());
  const BitVector& value = d_ls->get_assignment(it->second);
  return NodeManager::get().mk_value(value);
}

uint64_t
BvPropSolver::mk_node(const Node& node)
{
  assert(node.type().is_bv() || node.type().is_bool());

  uint64_t res  = 0;
  uint64_t size = node.type().is_bool() ? 1 : node.type().bv_size();

  bzla::ls::BitVectorDomain domain(size);

  if (node.is_value())
  {
    if (node.type().is_bv())
    {
      domain.fix(node.value<BitVector>());
    }
    else
    {
      assert(node.type().is_bool());
      assert(domain.size() == 1);
      domain.fix_bit(0, node.value<bool>());
    }
  }
  else if (d_use_const_bits)
  {
    const auto& bits = d_bb_solver.bits(node);
    assert(bits.size() == size);

    for (uint64_t i = 0; i < size; ++i)
    {
      uint64_t idx = size - 1 - i;
      if (bits[i].is_true())
      {
        domain.fix_bit(idx, true);
        d_statistics.d_nfixed_bits += 1;
      }
      else if (bits[i].is_false())
      {
        domain.fix_bit(idx, false);
        d_statistics.d_nfixed_bits += 1;
      }
    }
    d_statistics.d_ntotal_bits += size;
  }

  switch (node.kind())
  {
    case Kind::BV_ADD:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_ADD,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::BV_AND:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_AND,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::BV_CONCAT:
      assert(node.num_children() == 2);
      {
        Node child;
        if (d_use_sext && node::utils::is_bv_sext(node, child))
        {
          res = d_ls->mk_indexed_node(bzla::ls::NodeKind::BV_SEXT,
                                      domain,
                                      d_node_map.at(child),
                                      {node[0].type().bv_size()});
        }
        else
        {
          res = d_ls->mk_node(bzla::ls::NodeKind::BV_CONCAT,
                              domain,
                              {d_node_map.at(node[0]), d_node_map.at(node[1])});
        }
      }
      break;
    case Kind::BV_EXTRACT:
      assert(node.num_children() == 1);
      res = d_ls->mk_indexed_node(bzla::ls::NodeKind::BV_EXTRACT,
                                  domain,
                                  d_node_map.at(node[0]),
                                  {node.index(0), node.index(1)});
      break;
    case Kind::BV_MUL:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_MUL,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::BV_NOT:
      assert(node.num_children() == 1);
      res = d_ls->mk_node(
          bzla::ls::NodeKind::BV_NOT, domain, {d_node_map.at(node[0])});
      break;
    case Kind::BV_ULT:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_ULT,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::BV_SHL:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_SHL,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::BV_SLT:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_SLT,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::BV_SHR:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_SHR,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::BV_UDIV:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_UDIV,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::BV_UREM:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_UREM,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::BV_XOR:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_XOR,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::AND:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::AND,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::EQUAL:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::EQ,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])});
      break;
    case Kind::ITE:
      assert(node.num_children() == 3);
      res = d_ls->mk_node(bzla::ls::NodeKind::ITE,
                          domain,
                          {d_node_map.at(node[0]),
                           d_node_map.at(node[1]),
                           d_node_map.at(node[2])});
      break;
    case Kind::NOT:
      assert(node.num_children() == 1);
      res = d_ls->mk_node(
          bzla::ls::NodeKind::NOT, domain, {d_node_map.at(node[0])});
      break;
    default:
      assert(BvSolver::is_leaf(node));
      res = d_ls->mk_node(domain.lo(), domain);
  }

  return res;
}

}  // namespace bzla::bv
