/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzladumpaig.h"

#include "bzlaaigvec.h"
#include "utils/bzlaabort.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

static uint32_t
aiger_encode_aig(BzlaPtrHashTable *table, BzlaAIG *aig)
{
  BzlaPtrHashBucket *b;
  BzlaAIG *real_aig;
  uint32_t res;

  if (aig == BZLA_AIG_FALSE) return 0;

  if (aig == BZLA_AIG_TRUE) return 1;

  real_aig = BZLA_REAL_ADDR_AIG(aig);

  b = bzla_hashptr_table_get(table, real_aig);
  assert(b);

  res = 2 * (uint32_t) b->data.as_int;

  if (BZLA_IS_INVERTED_AIG(aig)) res ^= 1;

  return res;
}

void
bzla_dumpaig_dump_aig(BzlaAIGMgr *amgr,
                      bool is_binary,
                      FILE *output,
                      BzlaAIG *aig)
{
  bzla_dumpaig_dump_seq(amgr, is_binary, output, 1, &aig, 0, 0, 0, 0);
}

static void
dumpaig_dump_aux(Bzla *bzla,
                 BzlaNode *nodes[],
                 size_t nnodes,
                 bool is_binary,
                 FILE *output,
                 bool merge_roots)
{
  assert(bzla->lambdas->count == 0);
  assert(bzla->ufs->count == 0);

  BzlaPtrHashTableIterator it;
  BzlaPtrHashTable *backannotation;
  BzlaAIGVec *av;
  BzlaAIG *tmp, *merged;
  BzlaAIGMgr *amgr;
  BzlaAIGVecMgr *avmgr;
  uint32_t lazy_synthesize;
  BzlaAIGPtrStack roots;

  BZLA_INIT_STACK(bzla->mm, roots);
  amgr           = bzla_get_aig_mgr(bzla);
  avmgr          = bzla->avmgr;
  backannotation = bzla_hashptr_table_new(bzla->mm, 0, 0);

  BZLA_ABORT(
      bzla->ops[BZLA_UF_NODE].cur > 0 || bzla->ops[BZLA_LAMBDA_NODE].cur > 0,
      "cannot dump to AIGER format if formula contains "
      "functions");

  /* do not encode AIGs to SAT */
  lazy_synthesize = bzla_opt_get(bzla, BZLA_OPT_FUN_LAZY_SYNTHESIZE);
  bzla_opt_set(bzla, BZLA_OPT_FUN_LAZY_SYNTHESIZE, 1);

  if (bzla->inconsistent)
  {
    BZLA_PUSH_STACK(roots, BZLA_AIG_FALSE);
  }
  else
  {
    merged = BZLA_AIG_TRUE;
    for (size_t i = 0; i < nnodes; i++)
    {
      av = bzla_exp_to_aigvec(
          bzla, bzla_simplify_exp(bzla, nodes[i]), backannotation);
      if (merge_roots)
      {
        assert(av->width == 1);
        tmp = bzla_aig_and(amgr, merged, av->aigs[0]);
        bzla_aig_release(amgr, merged);
        merged = tmp;
      }
      else
      {
        for (size_t j = 0; j < av->width; j++)
        {
          BZLA_PUSH_STACK(roots, bzla_aig_copy(amgr, av->aigs[j]));
        }
      }
      bzla_aigvec_release_delete(avmgr, av);
    }
    bzla_opt_set(bzla, BZLA_OPT_FUN_LAZY_SYNTHESIZE, lazy_synthesize);
    if (merge_roots) BZLA_PUSH_STACK(roots, merged);
  }

  BZLA_PUSH_STACK_IF(BZLA_EMPTY_STACK(roots), roots, BZLA_AIG_TRUE);

  bzla_dumpaig_dump_seq(amgr,
                        is_binary,
                        output,
                        BZLA_COUNT_STACK(roots),
                        roots.start,
                        0,
                        0,
                        0,
                        backannotation);

  while (!BZLA_EMPTY_STACK(roots))
    bzla_aig_release(amgr, BZLA_POP_STACK(roots));
  BZLA_RELEASE_STACK(roots);

  bzla_iter_hashptr_init(&it, backannotation);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bzla_mem_freestr(bzla->mm, it.bucket->data.as_str);
    (void) bzla_iter_hashptr_next(&it);
  }
  bzla_hashptr_table_delete(backannotation);
}

void
bzla_dumpaig_dump(Bzla *bzla, bool is_binary, FILE *output, bool merge_roots)
{
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack nodes;

  const char *fmt_header      = "%s AIG dump\nBitwuzla version %s\n";
  int comment_section_started = 0;

  BZLA_INIT_STACK(bzla->mm, nodes);
  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BZLA_PUSH_STACK(nodes, bzla_iter_hashptr_next(&it));
  }

  if (BZLA_COUNT_STACK(nodes))
  {
    dumpaig_dump_aux(bzla,
                     nodes.start,
                     BZLA_COUNT_STACK(nodes),
                     is_binary,
                     output,
                     merge_roots);
    fputs("c\n", output);
    comment_section_started = 1;
    fprintf(output, fmt_header, "Formula", bzla_version(bzla));
  }
  BZLA_RELEASE_STACK(nodes);

  if (BZLA_EMPTY_STACK(nodes))
  {
    if (bzla->inconsistent)
    {
      BZLA_PUSH_STACK(nodes, bzla_node_invert(bzla->true_exp));
    }
    else
    {
      BZLA_PUSH_STACK(nodes, bzla->true_exp);
    }
  }

  /* print nodes marked as outputs in BTOR2 */
  if (BZLA_COUNT_STACK(bzla->outputs))
  {
    dumpaig_dump_aux(bzla,
                     bzla->outputs.start,
                     BZLA_COUNT_STACK(bzla->outputs),
                     is_binary,
                     output,
                     false);
    if (!comment_section_started) fputs("c\n", output);
    fprintf(output, fmt_header, "BTOR2 outputs", bzla_version(bzla));
  }
  BZLA_RELEASE_STACK(nodes);
}

void
bzla_dumpaig_dump_seq(BzlaAIGMgr *amgr,
                      bool is_binary,
                      FILE *file,
                      int32_t naigs,
                      BzlaAIG **aigs,
                      int32_t nregs,
                      BzlaAIG **regs,
                      BzlaAIG **nexts,
                      BzlaPtrHashTable *backannotation)
{
  uint32_t aig_id, left_id, right_id, tmp, delta;
  BzlaPtrHashTable *table, *latches;
  BzlaAIG *aig, *left, *right;
  BzlaPtrHashBucket *p, *b;
  int32_t M, I, L, O, A, i, l;
  BzlaAIGPtrStack stack;
  unsigned char ch;
  BzlaMemMgr *mm;

  assert(naigs >= 0);

  mm = amgr->bzla->mm;

  table   = bzla_hashptr_table_new(mm, 0, 0);
  latches = bzla_hashptr_table_new(mm, 0, 0);

  /* First add latches and inputs to hash tables.
   */
  for (i = nregs - 1; i >= 0; i--)
  {
    aig = regs[i];
    assert(!bzla_aig_is_const(aig));
    assert(!bzla_hashptr_table_get(latches, aig));
    bzla_hashptr_table_add(latches, aig);
  }

  BZLA_INIT_STACK(mm, stack);
  for (i = naigs - 1; i >= 0; i--)
  {
    aig = aigs[i];
    if (!bzla_aig_is_const(aig)) BZLA_PUSH_STACK(stack, aig);
  }
  for (i = nregs - 1; i >= 0; i--)
  {
    aig = nexts[i];
    if (!bzla_aig_is_const(aig)) BZLA_PUSH_STACK(stack, aig);
  }

  M = 0;

  while (!BZLA_EMPTY_STACK(stack))
  {
    aig = BZLA_POP_STACK(stack);

  CONTINUE_WITHOUT_POP:

    assert(!bzla_aig_is_const(aig));
    aig = BZLA_REAL_ADDR_AIG(aig);

    if (aig->mark) continue;

    aig->mark = 1;

    if (bzla_aig_is_var(aig))
    {
      if (bzla_hashptr_table_get(latches, aig)) continue;

      p              = bzla_hashptr_table_add(table, aig);
      p->data.as_int = ++M;
      assert(M > 0);
    }
    else
    {
      assert(bzla_aig_is_and(aig));

      right = bzla_aig_get_right_child(amgr, aig);
      BZLA_PUSH_STACK(stack, right);

      aig = bzla_aig_get_left_child(amgr, aig);
      goto CONTINUE_WITHOUT_POP;
    }
  }

  for (i = 0; i < nregs; i++)
  {
    aig = regs[i];
    assert(!bzla_aig_is_const(aig));
    assert(bzla_hashptr_table_get(latches, aig));
    assert(!bzla_hashptr_table_get(table, aig));
    p              = bzla_hashptr_table_add(table, aig);
    p->data.as_int = ++M;
    assert(M > 0);
  }

  L = nregs;
  assert(L <= M);
  I = M - L;

  /* Then start adding AND gates in postfix order.
   */
  assert(BZLA_EMPTY_STACK(stack));
  for (i = nregs - 1; i >= 0; i--)
  {
    aig = nexts[i];
    if (!bzla_aig_is_const(aig)) BZLA_PUSH_STACK(stack, aig);
  }
  for (i = naigs - 1; i >= 0; i--)
  {
    aig = aigs[i];
    if (!bzla_aig_is_const(aig)) BZLA_PUSH_STACK(stack, aig);
  }

  while (!BZLA_EMPTY_STACK(stack))
  {
    aig = BZLA_POP_STACK(stack);

    if (aig)
    {
    CONTINUE_WITH_NON_ZERO_AIG:

      assert(!bzla_aig_is_const(aig));
      aig = BZLA_REAL_ADDR_AIG(aig);

      if (!aig->mark) continue;

      aig->mark = 0;

      if (bzla_aig_is_var(aig)) continue;

      BZLA_PUSH_STACK(stack, aig);
      BZLA_PUSH_STACK(stack, 0);

      right = bzla_aig_get_right_child(amgr, aig);
      BZLA_PUSH_STACK(stack, right);

      aig = bzla_aig_get_left_child(amgr, aig);
      goto CONTINUE_WITH_NON_ZERO_AIG;
    }
    else
    {
      assert(!BZLA_EMPTY_STACK(stack));

      aig = BZLA_POP_STACK(stack);
      assert(aig);
      assert(!aig->mark);

      assert(aig);
      assert(BZLA_REAL_ADDR_AIG(aig) == aig);
      assert(bzla_aig_is_and(aig));

      p              = bzla_hashptr_table_add(table, aig);
      p->data.as_int = ++M;
      assert(M > 0);
    }
  }

  A = M - I - L;

  BZLA_RELEASE_STACK(stack);

  O = naigs;

  fprintf(file, "a%cg %d %d %d %d %d\n", is_binary ? 'i' : 'a', M, I, L, O, A);

  /* Only need to print inputs in non binary mode.
   */
  i = 0;
  for (p = table->first; p; p = p->next)
  {
    aig = p->key;

    assert(aig);
    assert(!BZLA_IS_INVERTED_AIG(aig));

    if (!bzla_aig_is_var(aig)) break;

    if (bzla_hashptr_table_get(latches, aig)) continue;

    if (!is_binary) fprintf(file, "%d\n", 2 * p->data.as_int);

    i++;
  }

  /* Now the latches aka regs.
   */
  for (i = 0; i < nregs; i++)
  {
    if (!is_binary) fprintf(file, "%u ", aiger_encode_aig(table, regs[i]));

    fprintf(file, "%u\n", aiger_encode_aig(table, nexts[i]));
  }

  /* Then the outputs ...
   */
  for (i = 0; i < naigs; i++)
    fprintf(file, "%u\n", aiger_encode_aig(table, aigs[i]));

  /* And finally all the AND gates.
   */
  while (p)
  {
    aig = p->key;

    assert(aig);
    assert(!BZLA_IS_INVERTED_AIG(aig));
    assert(bzla_aig_is_and(aig));

    left  = bzla_aig_get_left_child(amgr, aig);
    right = bzla_aig_get_right_child(amgr, aig);

    aig_id   = 2 * (uint32_t) p->data.as_int;
    left_id  = aiger_encode_aig(table, left);
    right_id = aiger_encode_aig(table, right);

    if (left_id < right_id) BZLA_SWAP(int32_t, left_id, right_id);

    assert(aig_id > left_id);
    assert(left_id >= right_id); /* strict ? */

    if (is_binary)
    {
      for (i = 0; i < 2; i++)
      {
        delta = i ? left_id - right_id : aig_id - left_id;
        tmp   = delta;

        while (tmp & ~0x7f)
        {
          ch = tmp & 0x7f;
          ch |= 0x80;

          putc(ch, file);
          tmp >>= 7;
        }

        ch = tmp;
        putc(ch, file);
      }
    }
    else
      fprintf(file, "%u %u %u\n", aig_id, left_id, right_id);

    p = p->next;
  }

  /* If we have back annotation add a symbol table.
   */
  i = l = 0;
  if (backannotation)
  {
    for (p = table->first; p; p = p->next)
    {
      aig = p->key;
      if (!bzla_aig_is_var(aig)) break;

      b = bzla_hashptr_table_get(backannotation, aig);

      if (!b) continue;

      assert(b->key == aig);
      assert(b->data.as_str);
      //	  assert (p->data.as_int == i + l + 1);
      if (bzla_hashptr_table_get(latches, aig))
        fprintf(file, "l%d %s\n", l++, b->data.as_str);
      else
        fprintf(file, "i%d %s\n", i++, b->data.as_str);
    }
  }

  bzla_hashptr_table_delete(table);
  bzla_hashptr_table_delete(latches);
}
