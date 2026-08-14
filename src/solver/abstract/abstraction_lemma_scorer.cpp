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

#include "solving_context.h"
#include "solver/bv/aig_bitblaster.h"

namespace bzla::abstract {

using namespace node;

void
AbstractionLemmaScorer::score_lemmas(node::Kind kind, uint64_t bv_size) const
{
  std::unordered_map<LemmaKind, uint64_t> map;
  score_lemmas_aux(kind, bv_size, map);
}

void
AbstractionLemmaScorer::score_lemmas_aux(
    node::Kind kind,
    uint64_t bv_size,
    std::unordered_map<LemmaKind, uint64_t>& rank_map) const
{
  NodeManager& nm = d_env.nm();
  uint64_t max    = 1u << bv_size;
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
  std::cout << "lemma score (worst: " << final_score << ", best: " << max * max
            << ")" << std::endl;

  for (const auto& lem : d_abstr_lemmas.at(kind))
  {
    uint64_t score            = 0;
    uint64_t prev_final_score = final_score;
    // Compute result for each triplet (x, s, t)
    for (uint64_t i = 0; i < values.size(); ++i)
    {
      for (uint64_t j = 0; j < values.size(); ++j)
      {
        // const Node& expected = results[i][j];
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
          if (kind == Kind::BV_MUL)
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
AbstractionLemmaScorer::rank_lemmas_by_circuit_size()
{
  Env env(d_env.nm(), d_env.sat_factory());
  bv::AigBitblaster bb;
  NodeManager& nm = d_env.nm();
  Type bv32       = nm.mk_bv_type(32);
  std::unordered_map<Kind, std::vector<std::pair<LemmaKind, uint64_t>>>
      lemma_sizes;

  std::unordered_map<Kind, uint64_t> circuit_size;
  for (const auto& [kind, lemmas] : d_abstr_lemmas)
  {
    if (KindInfo::num_children(kind) == 2)
    {
      Node x                       = nm.mk_const(bv32);
      Node s                       = nm.mk_const(bv32);
      Node t                       = nm.mk_const(bv32);
      uint64_t size_overall_before = bb.num_aig_ands();
      for (const auto& lem : lemmas)
      {
        Node inst = lem->instance(x, s, t);
        if (inst.is_null())
        {
          // Conditional on x == s, hence manual computation needed
          if (lem->kind() == LemmaKind::BITBLAST_BV_MUL_SQUARE)
          {
            inst =
                nm.mk_node(Kind::IMPLIES,
                           {nm.mk_node(Kind::EQUAL, {x, s}),
                            nm.mk_node(Kind::EQUAL,
                                       {t, nm.mk_node(Kind::BV_MUL, {x, x})})});
          }
          else if (lem->kind() == LemmaKind::MUL1_POW2)
          {
            Node val_pow2 =
                nm.mk_value(BitVector::mk_one(bv32.bv_size()).ibvshl(2));
            inst = lem->instance(val_pow2, s, t, x, s, t);
          }
          else if (lem->kind() == LemmaKind::MUL2_NEG_POW2)
          {
            Node val_pow2 = nm.mk_value(
                BitVector::mk_one(bv32.bv_size()).ibvshl(2).ibvneg());
            inst = lem->instance(val_pow2, s, t, x, s, t);
          }
          else
          {
            inst = lem->instance(x, s, t, x, s, t);
          }
        }
        if (!inst.is_null())
        {
          inst                 = env.rewriter().rewrite(inst);
          uint64_t size_before = bb.num_aig_ands();
          bb.bitblast(inst);
          uint64_t circuit_size = bb.num_aig_ands() - size_before;
          lemma_sizes[kind].emplace_back(lem->kind(), circuit_size);
        }
      }
      std::cout << kind << " total lemma size: "
                << bb.num_aig_ands() - size_overall_before << std::endl;
      {
        Node x               = nm.mk_const(bv32);
        Node s               = nm.mk_const(bv32);
        Node t               = nm.mk_node(kind, {x, s});
        uint64_t size_before = bb.num_aig_ands();
        bb.bitblast(t);
        std::cout << kind
                  << " circuit size: " << bb.num_aig_ands() - size_before
                  << std::endl;
        circuit_size[kind] = bb.num_aig_ands() - size_before;
      }
    }
  }

  std::unordered_map<LemmaKind, uint64_t> rank_map;
  for (auto& [k, lemmas] : lemma_sizes)
  {
    std::sort(lemmas.begin(), lemmas.end(), [](const auto& p1, const auto& p2) {
      return p1.second < p2.second;
    });
    uint64_t sum = 0;
    bool reached = false;
    for (const auto& [lk, size] : lemmas)
    {
      rank_map.emplace(lk, size);
      sum += size;
      std::cout << size << " " << lk << " (sum: " << sum << "/"
                << circuit_size[k] << ")" << std::endl;
      if (!reached && sum >= circuit_size[k])
      {
        std::cout << "--- circuit size reached (" << circuit_size[k] << ") ---"
                  << std::endl;
        reached = true;
      }
    }
    std::sort(d_abstr_lemmas.at(k).begin(),
              d_abstr_lemmas.at(k).end(),
              [&rank_map](const auto& l1, const auto& l2) {
                return rank_map[l1->kind()] < rank_map[l2->kind()];
              });
    std::cout << "score: " << k << std::endl;
    score_lemmas(k, 6);
  }

  std::cout << "final ranking:" << std::endl;
  std::cout << "std::unordered_map<LemmaKind, uint64_t> rank_map = {";
  for (const auto& [lk, size] : rank_map)
  {
    std::cout << "{LemmaKind::" << lk << "," << size << "}," << std::endl;
  }
  std::cout << "};" << std::endl;
  abort();
}

void
AbstractionLemmaScorer::rank_lemmas_by_score()
{
  std::unordered_map<LemmaKind, uint64_t> rank_map;
  score_lemmas_aux(Kind::BV_MUL, 6, rank_map);
  score_lemmas_aux(Kind::BV_UDIV, 6, rank_map);
  score_lemmas_aux(Kind::BV_UREM, 6, rank_map);

  std::cout << "std::unordered_map<LemmaKind, uint64_t> rank_map = {";
  for (const auto& [lk, score] : rank_map)
  {
    std::cout << "{LemmaKind::" << lk << "," << score << "}," << std::endl;
  }
  std::cout << "};" << std::endl;
  abort();
}

void
AbstractionLemmaScorer::verify_lemmas() const
{
  option::Options opts;
  NodeManager& nm = d_env.nm();
  SolvingContext ctx(nm, opts, d_env.sat_factory());

  for (uint64_t size = 4; size < 32; ++size)
  {
    std::cout << std::endl;
    std::cout << "check size=" << size << std::endl;
    Node x = nm.mk_const(nm.mk_bv_type(size), "x");
    Node s = nm.mk_const(nm.mk_bv_type(size), "s");
    Node t = nm.mk_const(nm.mk_bv_type(size), "t");
    for (const auto& [k, lemmas] : d_abstr_lemmas)
    {
      Node term = nm.mk_node(k, {x, s});
      ctx.push();
      std::cout << "check: " << k << std::endl;
      Node eq = nm.mk_node(Kind::EQUAL, {term, t});
      ctx.assert_formula(eq);
      size_t i = 0;
      for (const auto& lemma : lemmas)
      {
        std::cout << "\r" << ++i << "/" << lemmas.size() << std::flush;
        ctx.push();
        Node inst = lemma->instance(x, s, t);
        // may be null if lemma cannot be instantiated (if not applicable, e.g.,
        // for pow2 lemmas)
        if (inst.is_null())
        {
          continue;
        }
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
}  // namespace bzla::abstract
