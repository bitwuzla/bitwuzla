/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaprintmodel.h"

#include "bzlamodel.h"
#include "bzlarm.h"
#include "bzlatypes.h"
#include "dumper/bzladumpsmt.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/
/* print model                                                            */
/*------------------------------------------------------------------------*/

static void
print_fmt_bv_model_btor(Bzla *bzla,
                        uint32_t base,
                        const BzlaBitVector *assignment,
                        FILE *file)
{
  assert(bzla);
  assert(assignment);
  assert(file);

  char *ass;

  if (base == BZLA_OUTPUT_BASE_HEX)
    ass = bzla_bv_to_hex_char(bzla->mm, assignment);
  else if (base == BZLA_OUTPUT_BASE_DEC)
    ass = bzla_bv_to_dec_char(bzla->mm, assignment);
  else
    ass = bzla_bv_to_char(bzla->mm, assignment);
  fprintf(file, "%s", ass);
  bzla_mem_freestr(bzla->mm, ass);
}

static void
print_fmt_bv_model_tuple_btor(Bzla *bzla,
                              uint32_t base,
                              const BzlaBitVectorTuple *assignments,
                              FILE *file)
{
  assert(bzla);
  assert(assignments);
  assert(file);

  uint32_t i;

  if (assignments->arity > 1)
  {
    for (i = 0; i < assignments->arity; i++)
    {
      if (i > 0) fprintf(file, " ");
      print_fmt_bv_model_btor(bzla, base, assignments->bv[i], file);
    }
  }
  else
    print_fmt_bv_model_btor(bzla, base, assignments->bv[0], file);
}

/*------------------------------------------------------------------------*/

void
bzla_print_node_model(Bzla *bzla,
                      BzlaNode *input,
                      BzlaNode *value,
                      const char *format,
                      FILE *file)
{
  int32_t id;
  const char *symbol;
  uint32_t base;

  base   = bzla_opt_get(bzla, BZLA_OPT_OUTPUT_NUMBER_FORMAT);
  symbol = bzla_node_get_symbol(bzla, input);

  if (bzla_node_is_array(input))
  {
    // TODO
  }
  else if (bzla_node_param_is_exists_var(input)
           && !bzla_node_is_bv_const(value))
  {
    if (!strcmp(format, "btor"))
    {
      // TODO
    }
    else
    {
      if (symbol)
        fprintf(file, "%2c(define-fun %s () ", ' ', symbol);
      else
      {
        id = bzla_node_get_bzla_id(input);
        fprintf(file,
                "%2c(define-fun e%d () ",
                ' ',
                id ? id : bzla_node_get_id(input));
      }
      bzla_dumpsmt_dump_sort_node(input, file);
      fprintf(file, " ");
      bzla_dumpsmt_dump_node(bzla, file, value, 0);
      fprintf(file, ")\n");
    }
  }
  else
  {
    assert(bzla_node_is_bv_const(value));
    BzlaBitVector *bv_value = bzla_node_bv_const_get_bits(value);
    if (!strcmp(format, "btor"))
    {
      id = bzla_node_get_bzla_id(input);
      fprintf(file, "%d ", id ? id : bzla_node_get_id(input));
      print_fmt_bv_model_btor(bzla, base, bv_value, file);
      fprintf(file, "%s%s\n", symbol ? " " : "", symbol ? symbol : "");
    }
    else
    {
      if (symbol)
        fprintf(file, "%2c(define-fun %s () ", ' ', symbol);
      else
      {
        id = bzla_node_get_bzla_id(input);
        fprintf(file,
                "%2c(define-fun v%d () ",
                ' ',
                id ? id : bzla_node_get_id(input));
      }

      bzla_dumpsmt_dump_sort_node(input, file);
      fprintf(file, " ");
      bzla_dumpsmt_dump_const_bv_value(bzla, bv_value, base, file);
      fprintf(file, ")\n");
    }
  }
}

static void
dump_const_value(Bzla *bzla,
                 BzlaSortId sort,
                 const BzlaBitVector *assignment,
                 uint32_t base,
                 FILE *file)
{
  if (bzla_sort_is_rm(bzla, sort))
  {
    bzla_dumpsmt_dump_const_rm_value(bzla, assignment, file);
  }
  else if (bzla_sort_is_fp(bzla, sort))
  {
    bzla_dumpsmt_dump_const_fp_value(bzla,
                                     assignment,
                                     bzla_sort_fp_get_exp_width(bzla, sort),
                                     bzla_sort_fp_get_sig_width(bzla, sort),
                                     file);
  }
  else
  {
    assert(bzla_sort_is_bv(bzla, sort));
    bzla_dumpsmt_dump_const_bv_value(bzla, assignment, base, file);
  }
}

static void
print_bvfp_model(
    Bzla *bzla, BzlaNode *node, const char *format, uint32_t base, FILE *file)
{
  assert(bzla);
  assert(format);
  assert(node);
  assert(bzla_node_is_regular(node));

  int32_t id;
  char *symbol;
  const BzlaBitVector *ass;
  BzlaPtrHashBucket *b;

  ass    = bzla_model_get_bv(bzla, node);
  symbol = bzla_node_get_symbol(bzla, node);

  if (!strcmp(format, "btor"))
  {
    id = bzla_node_get_bzla_id(node);
    fprintf(file, "%d ", id ? id : bzla_node_get_id(node));
    print_fmt_bv_model_btor(bzla, base, ass, file);
    fprintf(file, "%s%s\n", symbol ? " " : "", symbol ? symbol : "");
  }
  else
  {
    if (symbol)
      fprintf(file, "%2c(define-fun %s () ", ' ', symbol);
    else
    {
      id = bzla_node_get_bzla_id(node);
      fprintf(file,
              "%2c(define-fun v%d () ",
              ' ',
              id ? id : bzla_node_get_id(node));
    }

    b = bzla_hashptr_table_get(bzla->inputs, node);
    if (b && b->data.flag)
    {
      fprintf(file, "Bool %s", bzla_bv_is_true(ass) ? "true" : "false");
    }
    else
    {
      bzla_dumpsmt_dump_sort_node(node, file);
      fprintf(file, " ");
      dump_const_value(bzla, bzla_node_get_sort_id(node), ass, base, file);
    }
    fprintf(file, ")\n");
  }
}

/*------------------------------------------------------------------------*/

static void
print_param_smt2(uint32_t param_index, BzlaSort *sort, FILE *file)
{
  assert(sort);
  assert(file);

  fprintf(file, "(@x%u ", param_index);
  bzla_dumpsmt_dump_sort(sort, file);
  fprintf(file, ")");
}

static void
print_fun_model_smt2(Bzla *bzla, BzlaNode *node, uint32_t base, FILE *file)
{
  assert(bzla);
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(file);

  char *s, *symbol;
  uint32_t i, x, nparens = 0;
  int32_t id;
  BzlaPtrHashTable *fun_model;
  BzlaPtrHashTableIterator it;
  BzlaBitVectorTuple *args;
  BzlaBitVector *assignment, *default_value;
  BzlaSortId codomain;
  BzlaTupleSortIterator iit;

  fun_model = (BzlaPtrHashTable *) bzla_model_get_fun(
      bzla, bzla_simplify_exp(bzla, node));
  if (!fun_model && !bzla_node_is_const_array(node)) return;

  if ((symbol = bzla_node_get_symbol(bzla, node)))
    s = symbol;
  else
  {
    BZLA_NEWN(bzla->mm, s, 40);
    id = bzla_node_get_bzla_id(node);
    sprintf(s,
            "%s%d",
            bzla_node_is_uf_array(node) ? "a" : "uf",
            id ? id : node->id);
  }

  fprintf(file, "%2c(define-fun %s (", ' ', s);

  /* fun param sorts */
  node = bzla_simplify_exp(bzla, node);
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_fun(node));

  BzlaSortId domain =
      bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(node));

  bzla_iter_tuple_sort_init(&iit, bzla, domain);
  x = 0;
  while (bzla_iter_tuple_sort_has_next(&iit))
  {
    codomain = bzla_iter_tuple_sort_next(&iit);
    if (x > 0)
    {
      fputc(' ', file);
    }
    print_param_smt2(x, bzla_sort_get_by_id(bzla, codomain), file);
    x++;
  }
  fprintf(file, ") ");
  codomain = bzla_sort_fun_get_codomain(bzla, bzla_node_get_sort_id(node));
  bzla_dumpsmt_dump_sort(bzla_sort_get_by_id(bzla, codomain), file);
  fprintf(file, "\n");

  if (bzla_node_is_const_array(node))
  {
    fprintf(file, "%6c", ' ');
    bzla_dumpsmt_dump_const_bv_value(
        bzla, bzla_model_get_bv(bzla, node->e[1]), base, file);
  }
  else
  {
    /* fun model as ite over args and assignments */
    assignment    = 0;
    default_value = 0;
    BzlaSort *domain_sort = bzla_sort_get_by_id(bzla, domain);
    bzla_iter_hashptr_init(&it, fun_model);
    while (bzla_iter_hashptr_has_next(&it))
    {
      assignment = it.bucket->data.as_ptr;
      args       = bzla_iter_hashptr_next(&it);
      x          = 0;
      if (args->arity > 0)
      {
        fprintf(file, "%4c(ite ", ' ');
        if (args->arity > 1) fprintf(file, "\n%6c(and", ' ');
        for (i = 0; i < args->arity; i++, x++)
        {
          if (args->arity > 1) fprintf(file, "\n%8c", ' ');
          fprintf(file, "(= @x%d ", x);
          dump_const_value(bzla,
                           domain_sort->tuple.elements[i]->id,
                           args->bv[i],
                           base,
                           file);
          fprintf(file, ")%s", i + 1 == args->arity ? "" : " ");
        }
        if (args->arity > 1)
        {
          fprintf(file, ")");
          fprintf(file, "\n%6c", ' ');
        }
      }
      else
      {
        /* found const array, use initial value as default value */
        default_value = bzla_bv_copy(bzla->mm, assignment);
        continue;
      }
      fprintf(file, " ");
      dump_const_value(bzla, codomain, assignment, base, file);
      fprintf(file, "\n");
      nparens += 1;
    }

    /* zero-initialized default value */
    if (!default_value)
    {
      uint32_t size;

      if (bzla_sort_is_fp(bzla, codomain))
      {
        size = bzla_sort_fp_get_bv_width(bzla, codomain);
      }
      else if (bzla_sort_is_rm(bzla, codomain))
      {
        size = BZLA_RM_BW;
      }
      else
      {
        assert(bzla_sort_is_bv(bzla, codomain));
        size = bzla_sort_bv_get_width(bzla, codomain);
      }
      default_value = bzla_bv_new(bzla->mm, size);
    }

    /* print default value */
    fprintf(file, "%6c", ' ');
    dump_const_value(bzla, codomain, default_value, base, file);
    bzla_bv_free(bzla->mm, default_value);
  }

  for (i = 0; i < nparens; i++) fprintf(file, ")");
  fprintf(file, ")\n");

  if (!symbol) BZLA_DELETEN(bzla->mm, s, 40);
}

static void
print_fun_model_btor(Bzla *bzla, BzlaNode *node, uint32_t base, FILE *file)
{
  assert(bzla);
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(file);

  char *symbol;
  int32_t id;
  BzlaBitVector *assignment;
  BzlaBitVectorTuple *args;
  BzlaPtrHashTable *fun_model;
  BzlaPtrHashTableIterator it;

  fun_model = (BzlaPtrHashTable *) bzla_model_get_fun(
      bzla, bzla_simplify_exp(bzla, node));
  if (!fun_model) return;

  symbol = bzla_node_get_symbol(bzla, node);
  id     = bzla_node_get_bzla_id(node);

  bzla_iter_hashptr_init(&it, fun_model);
  while (bzla_iter_hashptr_has_next(&it))
  {
    assignment = it.bucket->data.as_ptr;
    args       = bzla_iter_hashptr_next(&it);
    // TODO: distinguish between functions and arrays (ma)
    //       needs proper sort handling
    if (args->arity == 0)
    {
      fprintf(file, "%d[*] ", id ? id : node->id);
    }
    else
    {
      fprintf(file, "%d[", id ? id : node->id);
      print_fmt_bv_model_tuple_btor(bzla, base, args, file);
      fprintf(file, "] ");
    }
    print_fmt_bv_model_btor(bzla, base, assignment, file);
    fprintf(file, "%s%s\n", symbol ? " " : "", symbol ? symbol : "");
  }
}

static void
print_fun_model(
    Bzla *bzla, BzlaNode *node, const char *format, uint32_t base, FILE *file)
{
  assert(bzla);
  assert(node);
  assert(format);
  assert(file);
  assert(bzla_node_is_regular(node));

  if (!strcmp(format, "btor"))
    print_fun_model_btor(bzla, node, base, file);
  else
    print_fun_model_smt2(bzla, node, base, file);
}

/*------------------------------------------------------------------------*/

void
bzla_print_model_aufbvfp(Bzla *bzla, const char *format, FILE *file)
{
  assert(bzla);
  assert(bzla->last_sat_result == BZLA_RESULT_SAT);
  assert(format);
  assert(!strcmp(format, "btor") || !strcmp(format, "smt2"));
  assert(file);

  BzlaNode *cur;
  BzlaPtrHashTableIterator it;
  uint32_t base;

  base = bzla_opt_get(bzla, BZLA_OPT_OUTPUT_NUMBER_FORMAT);

  if (!strcmp(format, "smt2")) fprintf(file, "(\n");

  bzla_iter_hashptr_init(&it, bzla->inputs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    if (bzla_node_is_fun(bzla_simplify_exp(bzla, cur)))
    {
      print_fun_model(bzla, cur, format, base, file);
    }
    else
    {
      print_bvfp_model(bzla, cur, format, base, file);
    }
  }

  if (!strcmp(format, "smt2")) fprintf(file, ")\n");
}

void
bzla_print_model(Bzla *bzla, const char *format, FILE *file)
{
  bzla->slv->api.print_model(bzla->slv, format, file);
}

/*------------------------------------------------------------------------*/

void
bzla_print_value_smt2(Bzla *bzla, BzlaNode *exp, char *symbol_str, FILE *file)
{
  assert(bzla);
  assert(bzla->last_sat_result == BZLA_RESULT_SAT);
  assert(exp);
  assert(file);

  exp  = bzla_simplify_exp(bzla, exp);
  BzlaNode *value = bzla_model_get_value(bzla, exp);
  if (value)
  {
    fprintf(file, "(%s ", symbol_str);
    bzla_dumpsmt_dump_node(bzla, file, value, 0);
    bzla_node_release(bzla, value);
    fprintf(file, ")");
  }
}
