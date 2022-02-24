/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlasynthterm.h"

extern "C" {
#include "bzlabeta.h"
#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlamodel.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlapartgen.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"
}

#include <iostream>  // debug
#include <unordered_map>
#include <unordered_set>

namespace bzla {
namespace synth {

typedef BzlaNode *(*BzlaUnOp)(Bzla *, BzlaNode *);
typedef BzlaNode *(*BzlaBinOp)(Bzla *, BzlaNode *, BzlaNode *);
typedef BzlaNode *(*BzlaTerOp)(Bzla *, BzlaNode *, BzlaNode *, BzlaNode *);

struct Op
{
  bool assoc;
  uint8_t arity;
  union
  {
    BzlaUnOp un;
    BzlaBinOp bin;
    BzlaTerOp ter;
    void *fun;
  };
  const char *name;
  uint32_t num_added;
};

typedef struct Op Op;

//////////////////////////////////////////////////////////////////////////////

class TermDb
{
 public:
  TermDb(Bzla *bzla) : d_bzla(bzla) { d_stats.narity.resize(3); }
  ~TermDb();

  void add(BzlaNode *n, uint32_t level);

  std::unordered_map<BzlaSortId, std::vector<BzlaNode *>> &get(uint32_t level);

  size_t size() const;

  struct
  {
    std::vector<uint32_t> nlevel;
    std::vector<uint32_t> narity;
  } d_stats;

 private:
  Bzla *d_bzla;
  std::vector<std::unordered_map<BzlaSortId, std::vector<BzlaNode *>>> d_terms;
  std::unordered_set<BzlaNode *> d_term_cache;  // TODO: check if really needed
};

TermDb::~TermDb()
{
  for (auto t : d_term_cache)
  {
    bzla_node_release(d_bzla, t);
  }
}

void
TermDb::add(BzlaNode *n, uint32_t level)
{
  assert(level > 0);

  if (d_term_cache.find(n) != d_term_cache.end())
  {
    return;
  }

  d_term_cache.insert(bzla_node_copy(d_bzla, n));

  BzlaSortId sid = bzla_node_get_sort_id(n);

  if (d_terms.size() <= level)
  {
    d_terms.resize(level + 1);
  }

  auto [it, inserted] = d_terms[level].emplace(sid, std::vector<BzlaNode *>());
  it->second.push_back(n);

  uint32_t arity = bzla_node_real_addr(n)->arity;

  d_stats.narity.resize(arity + 1);
  ++d_stats.narity[arity];

  d_stats.nlevel.resize(level + 1);
  ++d_stats.nlevel[level];
}

std::unordered_map<BzlaSortId, std::vector<BzlaNode *>> &
TermDb::get(uint32_t level)
{
  assert(level < d_terms.size());
  return d_terms[level];
}

size_t
TermDb::size() const
{
  return d_term_cache.size();
}

class TermSynthesizer
{
 public:
  TermSynthesizer(Bzla *bzla,
                  std::vector<BzlaNode *> &inputs,
                  std::vector<BzlaBitVectorTuple *> &values_in,
                  std::vector<BzlaBitVector *> &values_out,
                  std::vector<BzlaNode *> &consts);

  /** Synthesize candidate terms. */
  std::vector<BzlaNode *> synthesize_terms();

  // aux
  BzlaNode *synthesize_terms(Op ops[],
                             uint32_t nops,
                             uint32_t max_checks,
                             uint32_t max_level,
                             BzlaNode *prev_synth);

  bool check_term(uint32_t cur_level,
                  BzlaNode *exp,
                  BzlaPtrHashTable *sigs,
                  Op *op);

  std::tuple<bool, size_t, BzlaBitVectorTuple *> check_signature(BzlaNode *exp);

  BzlaBitVector *eval_candidate(BzlaNode *candidate,
                                BzlaBitVectorTuple *value_in,
                                BzlaBitVector *value_out);

 private:
  /** Check candidate terms. */
  bool check();

  Bzla *d_bzla;
  std::vector<BzlaNode *> d_inputs;
  std::vector<BzlaBitVectorTuple *> &d_values_in;
  std::vector<BzlaBitVector *> &d_values_out;
  std::unordered_map<BzlaNode *, size_t> d_values_in_map;
  std::vector<BzlaNode *> d_consts;

  std::unordered_set<int32_t> d_term_cache;

  TermDb d_terms;

  struct
  {
    uint64_t num_checks = 0;
  } d_stats;
};

TermSynthesizer::TermSynthesizer(Bzla *bzla,
                                 std::vector<BzlaNode *> &inputs,
                                 std::vector<BzlaBitVectorTuple *> &values_in,
                                 std::vector<BzlaBitVector *> &values_out,
                                 std::vector<BzlaNode *> &consts)
    : d_bzla(bzla),
      d_inputs(inputs),
      d_values_in(values_in),
      d_values_out(values_out),
      d_consts(consts),
      d_terms(bzla)
{
  for (size_t i = 0; i < d_inputs.size(); ++i)
  {
    d_values_in_map.emplace(d_inputs[i], i);
  }
}

/* ------------------------------------------------------------------------- */

BzlaBitVector *
TermSynthesizer::eval_candidate(BzlaNode *candidate,
                                BzlaBitVectorTuple *value_in,
                                BzlaBitVector *value_out)
{
  assert(candidate);
  assert(value_in);
  assert(value_out);

  size_t j;
  int32_t i, pos;
  BzlaNode *cur, *real_cur;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;
  BzlaHashTableData *d;
  BzlaBitVectorPtrStack arg_stack;
  BzlaMemMgr *mm;
  BzlaBitVector **bv, *result, *inv_result, *a;

  mm    = d_bzla->mm;
  cache = bzla_hashint_map_new(mm);

  BZLA_INIT_STACK(mm, arg_stack);
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, candidate);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);

    d = bzla_hashint_map_get(cache, real_cur->id);
    if (!d)
    {
      bzla_hashint_map_add(cache, real_cur->id);
      BZLA_PUSH_STACK(visit, cur);

      if (bzla_node_is_apply(real_cur)) continue;

      for (i = real_cur->arity - 1; i >= 0; i--)
        BZLA_PUSH_STACK(visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert(!bzla_node_is_fun(real_cur));
      // assert(!bzla_node_is_apply(real_cur));

      if (!bzla_node_is_apply(real_cur))
      {
        arg_stack.top -= real_cur->arity;
      }
      bv = arg_stack.top;

      switch (real_cur->kind)
      {
        case BZLA_BV_CONST_NODE:
          result = bzla_bv_copy(mm, bzla_node_bv_const_get_bits(real_cur));
          break;

        case BZLA_APPLY_NODE:
        case BZLA_PARAM_NODE:
        case BZLA_VAR_NODE:
          assert(d_values_in_map.find(real_cur) != d_values_in_map.end());
          pos    = d_values_in_map.at(real_cur);
          result = bzla_bv_copy(mm, value_in->bv[pos]);
          break;

        case BZLA_BV_SLICE_NODE:
          result = bzla_bv_slice(mm,
                                 bv[0],
                                 bzla_node_bv_slice_get_upper(real_cur),
                                 bzla_node_bv_slice_get_lower(real_cur));
          break;

        case BZLA_BV_AND_NODE: result = bzla_bv_and(mm, bv[0], bv[1]); break;

        case BZLA_BV_EQ_NODE: result = bzla_bv_eq(mm, bv[0], bv[1]); break;

        case BZLA_BV_ADD_NODE: result = bzla_bv_add(mm, bv[0], bv[1]); break;

        case BZLA_BV_MUL_NODE: result = bzla_bv_mul(mm, bv[0], bv[1]); break;

        case BZLA_BV_ULT_NODE: result = bzla_bv_ult(mm, bv[0], bv[1]); break;

        case BZLA_BV_SLT_NODE: result = bzla_bv_slt(mm, bv[0], bv[1]); break;

        case BZLA_BV_SLL_NODE: result = bzla_bv_sll(mm, bv[0], bv[1]); break;

        case BZLA_BV_SRL_NODE: result = bzla_bv_srl(mm, bv[0], bv[1]); break;

        case BZLA_BV_UDIV_NODE: result = bzla_bv_udiv(mm, bv[0], bv[1]); break;

        case BZLA_BV_UREM_NODE: result = bzla_bv_urem(mm, bv[0], bv[1]); break;

        case BZLA_BV_CONCAT_NODE:
          result = bzla_bv_concat(mm, bv[0], bv[1]);
          break;

        case BZLA_EXISTS_NODE:
        case BZLA_FORALL_NODE: result = bzla_bv_copy(mm, bv[1]); break;

        default:
          assert(real_cur->kind == BZLA_COND_NODE);
          if (bzla_bv_is_true(bv[0]))
            result = bzla_bv_copy(mm, bv[1]);
          else
            result = bzla_bv_copy(mm, bv[2]);
      }

      if (!bzla_node_is_apply(real_cur))
      {
        for (i = 0; i < real_cur->arity; i++) bzla_bv_free(mm, bv[i]);
      }

      d->as_ptr = bzla_bv_copy(mm, result);

    EVAL_EXP_PUSH_RESULT:
      if (bzla_node_is_inverted(cur))
      {
        inv_result = bzla_bv_not(mm, result);
        bzla_bv_free(mm, result);
        result = inv_result;
      }
      BZLA_PUSH_STACK(arg_stack, result);
    }
    else
    {
      result = bzla_bv_copy(mm, static_cast<BzlaBitVector *>(d->as_ptr));
      goto EVAL_EXP_PUSH_RESULT;
    }
  }

  assert(BZLA_COUNT_STACK(arg_stack) == 1);
  result = BZLA_POP_STACK(arg_stack);

  for (j = 0; j < cache->size; j++)
  {
    a = static_cast<BzlaBitVector *>(cache->data[j].as_ptr);
    if (!a) continue;
    bzla_bv_free(mm, a);
  }
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(arg_stack);
  bzla_hashint_map_delete(cache);

  return result;
}

std::tuple<bool, size_t, BzlaBitVectorTuple *>
TermSynthesizer::check_signature(BzlaNode *exp)
{
  size_t nmatches = 0;
  BzlaBitVectorTuple *inputs, *sig;
  BzlaBitVector *output, *res;
  BzlaMemMgr *mm;

  mm             = d_bzla->mm;
  size_t nvalues = d_values_in.size();
  sig            = bzla_bv_new_tuple(mm, nvalues);

  // TODO: optimization: only construct bit-vector instead of full signature
  for (size_t i = 0; i < nvalues; i++)
  {
    inputs = d_values_in[i];
    output = d_values_out[i];

    res = eval_candidate(exp, inputs, output);

    if (bzla_bv_compare(res, output) == 0)
    {
      nmatches++;
    }

    bzla_bv_add_to_tuple(mm, sig, res, i);
    bzla_bv_free(mm, res);
  }
  return std::make_tuple(nmatches == nvalues, nmatches, sig);
}

bool
TermSynthesizer::check_term(uint32_t cur_level,
                            BzlaNode *exp,
                            BzlaPtrHashTable *sigs,
                            Op *op)
{
  int32_t id;
  BzlaMemMgr *mm;

  id = bzla_node_get_id(exp);
  mm = d_bzla->mm;

  ++d_stats.num_checks;

  if (bzla_node_is_bv_const(exp) || d_term_cache.find(id) != d_term_cache.end())
  {
    return false;
  }

  auto [found_term, nmatches, sig] = check_signature(exp);

  // TODO: option for threshold
  size_t nvalues = d_values_in.size();
  if (nmatches / (double) nvalues >= 0.3)
  {
    found_term = true;
  }

  if (bzla_hashptr_table_get(sigs, sig))
  {
    assert(!found_term);
    bzla_bv_free_tuple(mm, sig);
    return false;
  }

  bzla_hashptr_table_add(sigs, sig);
  d_term_cache.insert(id);

  if (op) op->num_added++;

  d_terms.add(exp, cur_level);
  return found_term;
}

static inline void
report_stats(Bzla *bzla,
             double start,
             uint32_t cur_level,
             uint32_t num_checks,
             TermDb &term_db)
{
  double delta;
  delta = bzla_util_time_stamp() - start;
  BZLA_MSG(bzla->msg,
           2,
           "level: %u|%u(%u,%u,%u)|%u, %.2f/s, %.2fs, %.2f MiB",
           cur_level,
           term_db.size(),
           term_db.d_stats.narity[0],
           term_db.d_stats.narity[1],
           term_db.d_stats.narity[2],
           num_checks,
           num_checks / delta,
           delta,
           (float) bzla->mm->allocated / 1024 / 1024);
}

static void
report_op_stats(Bzla *bzla, Op ops[], uint32_t nops)
{
  uint32_t i;
  for (i = 0; i < nops; i++)
  {
    BZLA_MSG(bzla->msg, 2, "%s: %u", ops[i].name, ops[i].num_added);
  }
}

#define CHECK_DONE(exp)                                                    \
  {                                                                        \
    found_candidate = check_term(cur_level, exp, sigs, &ops[i]);           \
    if (found_candidate)                                                   \
    {                                                                      \
      goto DONE;                                                           \
    }                                                                      \
    bzla_node_release(d_bzla, exp);                                        \
    if (d_stats.num_checks % 10000 == 0)                                   \
    {                                                                      \
      report_stats(d_bzla, start, cur_level, d_stats.num_checks, d_terms); \
    }                                                                      \
    if (d_stats.num_checks % 1000 == 0 && bzla_terminate(d_bzla))          \
    {                                                                      \
      BZLA_MSG(d_bzla->msg, 1, "terminate");                               \
      goto DONE;                                                           \
    }                                                                      \
    if (d_stats.num_checks >= max_checks)                                  \
    {                                                                      \
      BZLA_MSG(d_bzla->msg, 2, "Check limit of %u reached", max_checks);   \
      goto DONE;                                                           \
    }                                                                      \
  }

BzlaNode *
TermSynthesizer::synthesize_terms(Op ops[],
                                  uint32_t nops,
                                  uint32_t max_checks,
                                  uint32_t max_level,
                                  BzlaNode *prev_synth)
{
  assert(ops);
  assert(nops > 0);

  double start;
  bool found_candidate = false, equal;
  uint32_t i, *tuple, cur_level = 1;
  BzlaNode *exp, *result = 0;
  BzlaPtrHashTable *sigs;
  BzlaMemMgr *mm;
  BzlaPartitionGenerator pg;
  BzlaPtrHashTableIterator it;
  BzlaSortId bool_sort;

  start     = bzla_util_time_stamp();
  mm        = d_bzla->mm;
  bool_sort = bzla_sort_bool(d_bzla);
  sigs      = bzla_hashptr_table_new(
      mm, (BzlaHashPtr) bzla_bv_hash_tuple, (BzlaCmpPtr) bzla_bv_compare_tuple);

  /* generate target signature */
  // Note: currently unused
  if (prev_synth)
  {
    found_candidate = check_term(cur_level, prev_synth, sigs, 0);
    if (d_stats.num_checks % 10000 == 0)
    {
      report_stats(d_bzla, start, cur_level, d_stats.num_checks, d_terms);
    }
    if (found_candidate)
    {
      exp = bzla_node_copy(d_bzla, prev_synth);
      BZLA_MSG(d_bzla->msg, 2, "previously synthesized term matches");
      goto DONE;
    }
  }

  // Check if any of the inputs matches the output values.
  for (BzlaNode *t : d_inputs)
  {
    found_candidate = check_term(cur_level, t, sigs, 0);
    if (d_stats.num_checks % 10000 == 0)
    {
      report_stats(d_bzla, start, cur_level, d_stats.num_checks, d_terms);
    }
    if (found_candidate)
    {
      exp = bzla_node_copy(d_bzla, t);
      goto DONE;
    }
  }

  // Check if output values are all equal (only if size of output values > 1).
  equal = true;
  for (size_t i = 1; i < d_values_out.size(); ++i)
  {
    if (bzla_bv_compare(d_values_out[i - 1], d_values_out[i]))
    {
      equal = false;
      break;
    }
  }
  if (equal)
  {
    found_candidate = true;
    exp             = bzla_exp_bv_const(d_bzla, d_values_out[0]);
    d_terms.add(exp, 1);
    goto DONE;
  }

  // Add provided constants to level 1.
  for (auto c : d_consts)
  {
    d_terms.add(c, 1);
  }

  // Enumerate terms of size 2+
  for (cur_level = 2; !max_level || cur_level < max_level; cur_level++)
  {
    /* initialize current level */
    report_stats(d_bzla, start, cur_level, d_stats.num_checks, d_terms);

    size_t num_added = d_terms.size();
    for (i = 0; i < nops; i++)
    {
      // Apply unary operators to terms from previous level.
      if (ops[i].arity == 1)
      {
        auto &term_map = d_terms.get(cur_level - 1);
        for (auto &[sid, terms] : term_map)
        {
          for (BzlaNode *t : terms)
          {
            exp = ops[i].un(d_bzla, t);
            CHECK_DONE(exp);
          }
        }
      }
      else if (ops[i].arity == 2)
      {
        // partition generator: generates level partitions
        bzla_init_part_gen(&pg, cur_level, 2, !ops[i].assoc);
        while (bzla_has_next_part_gen(&pg))
        {
          tuple           = bzla_next_part_gen(&pg);
          auto &term_map1 = d_terms.get(tuple[0]);
          auto &term_map2 = d_terms.get(tuple[1]);

          for (auto [sid, terms1] : term_map1)
          {
            auto it2 = term_map2.find(sid);
            if (it2 == term_map2.end())
            {
              // continue; // this is what should be done TODO: increase levels
              break;  // this is what cart_prod implementation does
            }

            for (auto t1 : terms1)
            {
              for (auto t2 : it2->second)
              {
                exp = ops[i].bin(d_bzla, t1, t2);
                CHECK_DONE(exp);
              }
            }
          }
        }
      }
      else if (cur_level > 2)
      {
        // Note: ITE only right now
        assert(ops[i].arity == 3);
        assert(ops[i].ter == bzla_exp_cond);

        bzla_init_part_gen(&pg, cur_level, 3, true);
        while (bzla_has_next_part_gen(&pg))
        {
          tuple   = bzla_next_part_gen(&pg);
          auto &term_map1 = d_terms.get(tuple[0]);
          auto &term_map2 = d_terms.get(tuple[1]);
          auto &term_map3 = d_terms.get(tuple[2]);

          // No Boolean term in level `tuple[0]`.
          auto it1 = term_map1.find(bool_sort);
          if (it1 == term_map1.end())
          {
            continue;
          }

          for (auto [sid, terms2] : term_map2)
          {
            auto it3 = term_map3.find(sid);
            if (it3 == term_map3.end())
            {
              // continue; // this is what should be done TODO: increase levels
              break;  // this is what cart_prod implementation does
            }
            for (auto t2 : terms2)
            {
              for (auto t3 : it3->second)
              {
                for (auto t1 : it1->second)
                {
                  exp = ops[i].ter(d_bzla, t1, t2, t3);
                  CHECK_DONE(exp);
                }
              }
            }
          }
        }
      }
    }
    report_op_stats(d_bzla, ops, nops);
    // No new terms enumerated.
    if (num_added == d_terms.size()) break;
  }
DONE:
  report_stats(d_bzla, start, cur_level, d_stats.num_checks, d_terms);
  report_op_stats(d_bzla, ops, nops);

  if (found_candidate)
  {
    result = exp;
  }
  else
  {
    equal = true;
    for (size_t i = 1; i < d_values_out.size(); ++i)
    {
      if (bzla_bv_compare(d_values_out[i - 1], d_values_out[i]))
      {
        equal = false;
        break;
      }
    }
    if (equal)
    {
      found_candidate = true;
      result          = bzla_exp_bv_const(d_bzla, d_values_out[0]);
    }
  }

  if (found_candidate)
  {
    BZLA_MSG(d_bzla->msg,
             2,
             "found candidate after enumerating %u expressions",
             d_stats.num_checks);
  }
  else
  {
    BZLA_MSG(d_bzla->msg, 2, "no candidate found");
  }

  bzla_iter_hashptr_init(&it, sigs);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_bv_free_tuple(
        mm, static_cast<BzlaBitVectorTuple *>(bzla_iter_hashptr_next(&it)));

  bzla_hashptr_table_delete(sigs);

  bzla_sort_release(d_bzla, bool_sort);
  return result;
}

#define INIT_OP(ARITY, ASSOC, FPTR) \
  {                                 \
    ops[i].arity     = ARITY;       \
    ops[i].assoc     = ASSOC;       \
    ops[i].fun       = FPTR;        \
    ops[i].num_added = 0;           \
    ops[i].name      = #FPTR;       \
    i += 1;                         \
  }

#define INIT_OP_UN(ARITY, ASSOC, FPTR) \
  {                                    \
    ops[i].arity     = ARITY;          \
    ops[i].assoc     = ASSOC;          \
    ops[i].un        = FPTR;           \
    ops[i].num_added = 0;              \
    ops[i].name      = #FPTR;          \
    i += 1;                            \
  }

#define INIT_OP_BIN(ARITY, ASSOC, FPTR) \
  {                                     \
    ops[i].arity     = ARITY;           \
    ops[i].assoc     = ASSOC;           \
    ops[i].bin       = FPTR;            \
    ops[i].num_added = 0;               \
    ops[i].name      = #FPTR;           \
    i += 1;                             \
  }

#define INIT_OP_TER(ARITY, ASSOC, FPTR) \
  {                                     \
    ops[i].arity     = ARITY;           \
    ops[i].assoc     = ASSOC;           \
    ops[i].ter       = FPTR;            \
    ops[i].num_added = 0;               \
    ops[i].name      = #FPTR;           \
    i += 1;                             \
  }

static uint32_t
init_ops(Bzla *bzla, Op *ops)
{
  uint32_t i = 0;

  INIT_OP_UN(1, false, bzla_exp_bv_not);
  //  INIT_OP (1, false, bzla_neg_exp);
  //  INIT_OP (1, false, bzla_redor_exp);
  //  INIT_OP (1, false, bzla_redxor_exp);
  //  INIT_OP (1, false, bzla_redand_exp);
  //  INIT_OP (1, false, bzla_inc_exp);
  //  INIT_OP (1, false, bzla_dec_exp);

  /* boolean ops */
  INIT_OP_BIN(2, false, bzla_exp_bv_ult);
  INIT_OP_BIN(2, false, bzla_exp_bv_slt);
  INIT_OP_BIN(2, true, bzla_exp_eq);

  /* bv ops */
  if (bzla->ops[BZLA_BV_AND_NODE].cur > 0)
  {
    INIT_OP_BIN(2, true, bzla_exp_bv_and);
  }
  if (bzla->ops[BZLA_BV_ADD_NODE].cur > 0)
  {
    INIT_OP_BIN(2, true, bzla_exp_bv_add);
    INIT_OP_BIN(2, false, bzla_exp_bv_sub);
  }
  if (bzla->ops[BZLA_BV_MUL_NODE].cur > 0)
  {
    INIT_OP_BIN(2, true, bzla_exp_bv_mul);
  }
  if (bzla->ops[BZLA_BV_UDIV_NODE].cur > 0)
  {
    INIT_OP_BIN(2, false, bzla_exp_bv_udiv);
    INIT_OP_BIN(2, false, bzla_exp_bv_sdiv);
  }
  if (bzla->ops[BZLA_BV_UREM_NODE].cur > 0)
  {
    INIT_OP_BIN(2, false, bzla_exp_bv_urem);
    INIT_OP_BIN(2, false, bzla_exp_bv_srem);
    INIT_OP_BIN(2, false, bzla_exp_bv_smod);
  }

  INIT_OP_BIN(2, false, bzla_exp_bv_sll);
  INIT_OP_BIN(2, false, bzla_exp_bv_sra);
  INIT_OP_BIN(2, false, bzla_exp_bv_srl);
#if 0
  INIT_OP (2, true,  bzla_ne_exp);
  INIT_OP (2, true,  bzla_xor_exp);
  INIT_OP (2, true,  bzla_xnor_exp);
  INIT_OP (2, true,  bzla_nand_exp);
  INIT_OP (2, true,  bzla_or_exp);
  INIT_OP (2, true,  bzla_nor_exp);
  /* additonal operations */
  INIT_OP (2, true, bzla_uaddo_exp);
  INIT_OP (2, true, bzla_saddo_exp);
  INIT_OP (2, true, bzla_umulo_exp);
  INIT_OP (2, true, bzla_smulo_exp);
  INIT_OP (2, false, bzla_exp_bv_slt);
  INIT_OP (2, false, bzla_ugt_exp);
  INIT_OP (2, false, bzla_sgt_exp);
  INIT_OP (2, false, bzla_ugte_exp);
  INIT_OP (2, false, bzla_sgte_exp);
  INIT_OP (2, false, bzla_exp_bv_sub);
  INIT_OP (2, false, bzla_usubo_exp);
  INIT_OP (2, false, bzla_ssubo_exp);
  INIT_OP (2, false, bzla_exp_bv_udiv);
  INIT_OP (2, false, bzla_exp_bv_sdiv);
  INIT_OP (2, false, bzla_sdivo_exp);
  INIT_OP (2, false, bzla_exp_bv_urem);
  INIT_OP (2, false, bzla_exp_bv_srem);
  INIT_OP (2, false, bzla_exp_bv_smod);
  INIT_OP (2, false, bzla_concat_exp);
#endif
  INIT_OP_TER(3, false, bzla_exp_cond);
  return i;
}

BzlaNode *
bzla_synthesize_term(Bzla *bzla,
                     std::vector<BzlaNode *> &params,
                     std::vector<BzlaBitVectorTuple *> &value_in,
                     std::vector<BzlaBitVector *> &value_out,
                     std::vector<BzlaNode *> &consts,
                     uint32_t max_checks,
                     uint32_t max_level,
                     BzlaNode *prev_synth)
{
  assert(value_in.size() == value_out.size());

  uint32_t nops;
  Op ops[64];
  BzlaNode *result;

  nops = init_ops(bzla, ops);
  assert(nops);

  TermSynthesizer sy(bzla, params, value_in, value_out, consts);

  result = sy.synthesize_terms(ops, nops, max_checks, max_level, prev_synth);

  return result;
}

}  // namespace synth
}  // namespace bzla
