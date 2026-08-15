/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/abstract/abstraction_lemma_scorer.h"

#include <algorithm>
#include <cassert>
#include <iostream>

#include "node/kind_info.h"
#include "solver/bv/aig_bitblaster.h"
#include "solving_context.h"

namespace bzla::abstract {

using namespace node;

AbstractionLemmaScorer::AbstractionLemmaScorer(Env& env,
                                               const std::vector<Kind>& kinds)
    : d_env(env), d_rewriter(env.rewriter())
{
  for (Kind kind : kinds)
  {
    assert(KindInfo::num_children(kind) == 2);
    d_lemmas.emplace_back(kind, mk_lemmas(env.nm(), kind, false));
  }
}

void
AbstractionLemmaScorer::score_lemmas(uint64_t bv_size) const
{
  RankMap rank_map;
  for (const auto& [kind, lemmas] : d_lemmas)
  {
    score_lemmas(kind, lemmas, bv_size, rank_map);
  }
}

void
AbstractionLemmaScorer::score_lemmas(Kind kind,
                                     const Lemmas& lemmas,
                                     uint64_t bv_size,
                                     RankMap& rank_map) const
{
  NodeManager& nm = d_env.nm();
  uint64_t max    = static_cast<uint64_t>(1) << bv_size;
  std::vector<Node> values;
  std::vector<std::vector<std::vector<bool>>> results_lemmas(
      max, std::vector<std::vector<bool>>(max, std::vector<bool>(max, true)));

  // Create all possible values [0, max[
  for (uint64_t i = 0; i < max; ++i)
  {
    values.push_back(nm.mk_value(BitVector::from_ui(bv_size, i)));
  }

  // Compute all results for kind
  uint64_t optimal_score = 0;
  for (uint64_t i = 0; i < values.size(); ++i)
  {
    for (uint64_t j = 0; j < values.size(); ++j)
    {
      for (uint64_t k = 0; k < values.size(); ++k)
      {
        Node val = d_rewriter.eval(
            nm.mk_node(Kind::EQUAL,
                       {values[k], nm.mk_node(kind, {values[i], values[j]})}));
        assert(val.is_value());
        if (val.value<bool>())
        {
          ++optimal_score;
        }
      }
    }
  }

  std::cout << std::fixed;
  uint64_t max_score   = max * max * max;
  uint64_t final_score = max_score;
  std::cout << kind << " lemma score for bit-width " << bv_size
            << " (worst: " << final_score << ", best: " << max * max << ")"
            << std::endl;

  for (const auto& lem : lemmas)
  {
    uint64_t score            = 0;
    uint64_t prev_final_score = final_score;
    // Compute result for each triplet (x, s, t)
    for (uint64_t i = 0; i < values.size(); ++i)
    {
      for (uint64_t j = 0; j < values.size(); ++j)
      {
        for (uint64_t k = 0; k < values.size(); ++k)
        {
          Node inst = lem->instance(values[i], values[j], values[k]);
          if (inst.is_null())
          {
            inst = lem->instance(values[i],
                                 values[j],
                                 values[k],
                                 values[i],
                                 values[j],
                                 values[k]);
          }
          bool res = true;
          if (!inst.is_null())
          {
            inst = d_rewriter.rewrite(inst);
            assert(inst.is_value());
            res = inst.value<bool>();
          }

          // check commutative case
          if (KindInfo::is_commutative(kind))
          {
            Node instc = lem->instance(values[j], values[i], values[k]);
            if (instc.is_null())
            {
              instc = lem->instance(values[j],
                                    values[i],
                                    values[k],
                                    values[j],
                                    values[i],
                                    values[k]);
            }
            if (!instc.is_null())
            {
              instc = d_rewriter.rewrite(instc);
              res   = res & instc.value<bool>();
            }
          }

          auto overall_res = results_lemmas[i][j][k];
          // Count cases when lemma is true (including false positives)
          if (res)
          {
            ++score;
          }
          // Count number of ruled out triplets
          else if (overall_res)
          {
            --final_score;
          }
          results_lemmas[i][j][k] = overall_res & res;
        }
      }
    }
    rank_map[lem->kind()] = score;
    int64_t diff          = final_score - prev_final_score;
    std::cout << lem->kind() << ": " << score << "/" << max_score
              << " (final: " << final_score << ", diff: " << diff << ", "
              << static_cast<double>(diff) / max_score * 100 << "%)"
              << std::endl;
  }
  std::cout << "final score:   " << final_score << " "
            << static_cast<double>(final_score) / max_score * 100
            << "% (wrong results: " << final_score - (max * max) << ")"
            << std::endl;
  std::cout << "optimal score: " << optimal_score << " "
            << static_cast<double>(optimal_score) / max_score * 100 << "%"
            << std::endl;
}

void
AbstractionLemmaScorer::rank_lemmas_by_score(uint64_t bv_size)
{
  RankMap rank_map;
  for (const auto& [kind, lemmas] : d_lemmas)
  {
    score_lemmas(kind, lemmas, bv_size, rank_map);
  }
  print_rank_map(rank_map);
}

void
AbstractionLemmaScorer::rank_lemmas_by_circuit_size(uint64_t bv_size,
                                                    uint64_t circuit_bv_size)
{
  bv::AigBitblaster bb;
  NodeManager& nm = d_env.nm();
  Type bv         = nm.mk_bv_type(circuit_bv_size);
  std::unordered_map<Kind, std::vector<std::pair<LemmaKind, uint64_t>>>
      lemma_sizes;
  std::unordered_map<Kind, uint64_t> circuit_size;

  // First, rank lemmas by circuit size at bit-width `circuit_bv_size`.
  std::cout << "circuit sizes for bit-width " << circuit_bv_size << std::endl;
  for (const auto& [kind, lemmas] : d_lemmas)
  {
    Node x                       = nm.mk_const(bv);
    Node s                       = nm.mk_const(bv);
    Node t                       = nm.mk_const(bv);
    uint64_t size_overall_before = bb.num_aig_ands();
    for (const auto& lem : lemmas)
    {
      Node inst = lem->instance(x, s, t);
      if (inst.is_null())
      {
        // Conditional on x == s, hence manual computation needed
        if (lem->kind() == LemmaKind::BITBLAST_BV_MUL_SQUARE)
        {
          inst = nm.mk_node(
              Kind::IMPLIES,
              {nm.mk_node(Kind::EQUAL, {x, s}),
               nm.mk_node(Kind::EQUAL, {t, nm.mk_node(Kind::BV_MUL, {x, x})})});
        }
        else if (lem->kind() == LemmaKind::MUL1_POW2)
        {
          Node val_pow2 =
              nm.mk_value(BitVector::mk_one(bv.bv_size()).ibvshl(2));
          inst = lem->instance(val_pow2, s, t, x, s, t);
        }
        else if (lem->kind() == LemmaKind::MUL2_NEG_POW2)
        {
          Node val_pow2 =
              nm.mk_value(BitVector::mk_one(bv.bv_size()).ibvshl(2).ibvneg());
          inst = lem->instance(val_pow2, s, t, x, s, t);
        }
        else
        {
          inst = lem->instance(x, s, t, x, s, t);
        }
      }
      if (!inst.is_null())
      {
        inst                 = d_rewriter.rewrite(inst);
        uint64_t size_before = bb.num_aig_ands();
        bb.bitblast(inst);
        uint64_t circuit_size = bb.num_aig_ands() - size_before;
        lemma_sizes[kind].emplace_back(lem->kind(), circuit_size);
      }
    }
    std::cout << kind << " total lemma size: "
              << bb.num_aig_ands() - size_overall_before << std::endl;
    {
      Node op              = nm.mk_node(kind, {x, s});
      uint64_t size_before = bb.num_aig_ands();
      bb.bitblast(op);
      std::cout << kind << " circuit size: " << bb.num_aig_ands() - size_before
                << std::endl;
      circuit_size[kind] = bb.num_aig_ands() - size_before;
    }
  }
  RankMap rank_map;
  for (auto& [kind, lemmas] : d_lemmas)
  {
    auto& sizes = lemma_sizes[kind];
    std::sort(sizes.begin(), sizes.end(), [](const auto& p1, const auto& p2) {
      return p1.second < p2.second;
    });
    uint64_t sum = 0;
    bool reached = false;
    for (const auto& [lk, size] : sizes)
    {
      rank_map.emplace(lk, size);
      sum += size;
      std::cout << size << " " << lk << " (sum: " << sum << "/"
                << circuit_size[kind] << ")" << std::endl;
      if (!reached && sum >= circuit_size[kind])
      {
        std::cout << "--- circuit size reached (" << circuit_size[kind]
                  << ") ---" << std::endl;
        reached = true;
      }
    }

    // Then, score lemma schemas in the order determined by their circuit size.
    std::sort(lemmas.begin(),
              lemmas.end(),
              [&rank_map](const auto& l1, const auto& l2) {
                return rank_map[l1->kind()] < rank_map[l2->kind()];
              });
    RankMap score_map;
    score_lemmas(kind, lemmas, bv_size, score_map);
  }

  print_rank_map(rank_map);
}

void
AbstractionLemmaScorer::verify_lemmas(uint64_t bv_size) const
{
  option::Options opts;
  NodeManager& nm = d_env.nm();
  SolvingContext ctx(nm, opts, d_env.sat_factory());

  for (uint64_t size = 3; size < bv_size; ++size)
  {
    std::cout << "check bit-width " << size << std::endl;
    Node x = nm.mk_const(nm.mk_bv_type(size), "x");
    Node s = nm.mk_const(nm.mk_bv_type(size), "s");
    Node t = nm.mk_const(nm.mk_bv_type(size), "t");
    for (const auto& [kind, lemmas] : d_lemmas)
    {
      Node term = nm.mk_node(kind, {x, s});
      ctx.push();
      std::cout << "check: " << kind << std::endl;
      Node eq = nm.mk_node(Kind::EQUAL, {term, t});
      ctx.assert_formula(eq);
      size_t i = 0;
      for (const auto& lemma : lemmas)
      {
        std::cout << "\r" << ++i << "/" << lemmas.size() << std::flush;
        Node inst = lemma->instance(x, s, t);
        // may be null if lemma cannot be instantiated
        // (if not applicable, e.g., for pow2 lemmas)
        if (inst.is_null())
        {
          continue;
        }
        ctx.push();
        inst = nm.mk_node(Kind::NOT, {inst});
        ctx.assert_formula(inst);
        Result res = ctx.solve();
        if (res != Result::UNSAT)
        {
          std::cout << std::endl;
          std::cout << lemma->kind() << " failed" << std::endl;
          std::cout << "(assert " << eq << ")" << std::endl;
          std::cout << "(assert " << inst << ")" << std::endl;
          std::cout << "x: " << ctx.get_value(x) << std::endl;
          std::cout << "s: " << ctx.get_value(s) << std::endl;
          std::cout << "t: " << ctx.get_value(t) << std::endl;
        }
        ctx.pop();
      }
      std::cout << std::endl;
      ctx.pop();
    }
  }
}

void
AbstractionLemmaScorer::print_rank_map(const RankMap& rank_map) const
{
  std::cout << "std::unordered_map<LemmaKind, uint64_t> rank_map = {"
            << std::endl;
  for (const auto& [lk, size] : rank_map)
  {
    std::cout << "{LemmaKind::" << lk << "," << size << "}," << std::endl;
  }
  std::cout << "};" << std::endl;
}

}  // namespace bzla::abstract
