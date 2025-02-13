/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "sat/interpolants/tracer.h"

#include "node/node_utils.h"

using namespace bzla::node;

namespace bzla::sat::interpolants {

Tracer::Statistics::Statistics(util::Statistics& stats,
                               const std::string& prefix)
    : size_interpolant(
          stats.new_stat<uint64_t>(prefix + "sat::interpolant::size"))
{
}

Tracer::RevBitblasterCache
Tracer::compute_rev_bb_cache() const
{
  RevBitblasterCache res;
  // Get reverse mapping for nodes in bitblaster cache
  const auto& bb_cache = d_bitblaster.bitblaster_cache();
  for (const auto& p : bb_cache)
  {
#ifndef NDEBUG
    bool is_bv = p.first.type().is_bv();
#endif
    assert(is_bv || p.first.type().is_bool());
    for (size_t i = 0, size = p.second.size(); i < size; ++i)
    {
      const bitblast::AigNode& a = p.second[i];
      size_t j                   = size - 1 - i;
      assert(is_bv || j == 0);
      res.try_emplace(a.get_id(), p.first, j);
    }
  }
  return res;
}

Node
Tracer::get_node_from_bb_cache(int64_t aig_id, RevBitblasterCache& cache) const
{
  Node node;
  size_t idx     = 0;
  const auto& it = cache.find(aig_id);
  if (it != cache.end())
  {
    node       = it->second.first;
    idx        = it->second.second;
    bool is_bv = node.type().is_bv();
    assert(is_bv || idx == 0);
    if (is_bv)
    {
      node = utils::bv1_to_bool(
          d_nm, d_nm.mk_node(Kind::BV_EXTRACT, {node}, {idx, idx}));
    }
    return node;
  }
  const auto& nit = cache.find(-aig_id);
  if (nit != cache.end())
  {
    node       = utils::invert_node(d_nm, nit->second.first);
    idx        = nit->second.second;
    bool is_bv = node.type().is_bv();
    assert(is_bv || idx == 0);
    if (is_bv)
    {
      node = utils::bv1_to_bool(
          d_nm, d_nm.mk_node(Kind::BV_EXTRACT, {node}, {idx, idx}));
    }
    return node;
  }
  return Node();
}

std::ostream&
operator<<(std::ostream& out, Tracer::VariableKind kind)
{
  out << (kind == Tracer::VariableKind::A
              ? "A"
              : (kind == Tracer::VariableKind::B ? "B" : "GLOBAL"));
  return out;
}

std::ostream&
operator<<(std::ostream& out, Tracer::ClauseKind kind)
{
  out << (kind == Tracer::ClauseKind::A
              ? "A"
              : (kind == Tracer::ClauseKind::B ? "B" : "LEARNED"));
  return out;
}
}  // namespace bzla::sat::interpolants
