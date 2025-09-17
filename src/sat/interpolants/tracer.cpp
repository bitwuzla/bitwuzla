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
      auto [it, inserted] = res.try_emplace(a.get_id(), p.first, j);
      // If more than one node maps to the same AIG ID, we use the one with the
      // lowest node id. The reasoning behind this is that if multiple nodes map
      // to the same AIG, we want to use the one that is the closest to the
      // original term (lowest id).
      //
      // We have encountered this case with quantifiers, where a quantified term
      // and a term with skolems of the quantified variable that occurs in that
      // term map to the same AIG .
      //
      // For example (sk(56) is the skolem introduced for z):
      // @t56: (forall ((z (_ BitVec 2)))
      //         (not (= #b11 (concat ((_ extract 0 0) z) #b0))))
      // @t97: (not (and
      //              (not (forall ((z (_ BitVec 2)))
      //                     (not (= #b11 (concat ((_ extract 0 0) z) #b0)))))
      //              (not (= #b11 (concat ((_ extract 0 0) |sk(56)|) #b0)))))
      // Both map to the same AIG, but in the interpolant, we should not use
      // terms that are introduced via lemmas (the skolems, in this case).
      //
      // In general, it should always be more beneficial to use the node with
      // the lowest id. There's only one case where this may not be the case:
      // if a term x was introduced in a lemma and maps to the same AIG as a
      // term y and id(x) > id(y) but x does not contain y (and no skolems)
      // but is a simpler version of y. This would indicate that we are missing
      // a rewrite from y -> x.
      if (!inserted)
      {
        if (it->second.first.get().id() > p.first.id())
        {
          it->second.first  = p.first;
          it->second.second = j;
        }
      }
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
    node = it->second.first;
    idx  = it->second.second;
  }
  else
  {
    const auto& nit = cache.find(-aig_id);
    if (nit != cache.end())
    {
      node = utils::invert_node(d_nm, nit->second.first);
      idx  = nit->second.second;
    }
  }
  if (!node.is_null())
  {
    bool is_bv = node.type().is_bv();
    assert(is_bv || idx == 0);
    if (is_bv)
    {
      node = utils::bv1_to_bool(
          d_nm, d_nm.mk_node(Kind::BV_EXTRACT, {node}, {idx, idx}));
    }
  }
  return node;
}

}  // namespace bzla::sat::interpolants
