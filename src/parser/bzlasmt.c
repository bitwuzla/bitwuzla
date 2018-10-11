/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2014-2016 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlasmt.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdlib.h>

#include "bzlabv.h"
#include "bzlaopt.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlamem.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"

BZLA_DECLARE_STACK(BoolectorNodePtr, BoolectorNode *);

/*------------------------------------------------------------------------*/

typedef struct BzlaSMTParser BzlaSMTParser;
typedef struct BzlaSMTNode BzlaSMTNode;
typedef struct BzlaSMTNodes BzlaSMTNodes;
typedef struct BzlaSMTSymbol BzlaSMTSymbol;

enum BzlaSMTCharacterClass
{
  BZLA_SMTCC_IDENTIFIER_START    = 1,
  BZLA_SMTCC_IDENTIFIER_MIDDLE   = 2,
  BZLA_SMTCC_ARITHMETIC_OPERATOR = 4,
  BZLA_SMTCC_NUMERAL_START       = 8,
  BZLA_SMTCC_DIGIT               = 16,
  BZLA_SMTCC_SPACE               = 32,
  BZLA_SMTCC_IDENTIFIER_PREFIX   = 64,
};

enum BzlaSMTToken
{
  BZLA_SMTOK_ERR = 0,
  BZLA_SMTOK_EOF = EOF,

  BZLA_SMTOK_IDENTIFIER = 'a',
  BZLA_SMTOK_NUMERAL    = '0',
  BZLA_SMTOK_RATIONAL   = '.',
  BZLA_SMTOK_USERVAL    = '{',
  BZLA_SMTOK_LP         = '(',
  BZLA_SMTOK_RP         = ')',
  BZLA_SMTOK_STRING     = '"',
  BZLA_SMTOK_VAR        = '?',
  BZLA_SMTOK_FVAR       = '$',
  BZLA_SMTOK_ATTR       = ':',
  BZLA_SMTOK_ARITH      = '=',

  BZLA_SMTOK_KEYWORD      = 256, /* above ASCII codes */
  BZLA_SMTOK_AND          = 256,
  BZLA_SMTOK_ASSUMPTION   = 257,
  BZLA_SMTOK_BENCHMARK    = 258,
  BZLA_SMTOK_DISTINCT     = 259,
  BZLA_SMTOK_EXTRAFUNS    = 260,
  BZLA_SMTOK_EXTRAPREDS   = 261,
  BZLA_SMTOK_EXTRASORTS   = 262,
  BZLA_SMTOK_FALSE        = 263,
  BZLA_SMTOK_FLET         = 264,
  BZLA_SMTOK_FORMULA      = 265,
  BZLA_SMTOK_IFF          = 266,
  BZLA_SMTOK_IF_THEN_ELSE = 267,
  BZLA_SMTOK_IMPLIES      = 268,
  BZLA_SMTOK_ITE          = 269,
  BZLA_SMTOK_LET          = 270,
  BZLA_SMTOK_LOGICATTR    = 271,
  BZLA_SMTOK_NOT          = 272,
  BZLA_SMTOK_NOTES        = 273,
  BZLA_SMTOK_OR           = 274,
  BZLA_SMTOK_SAT          = 275,
  BZLA_SMTOK_STATUS       = 276,
  BZLA_SMTOK_TRUE         = 277,
  BZLA_SMTOK_UNKNOWN      = 278,
  BZLA_SMTOK_UNSAT        = 279,
  BZLA_SMTOK_XOR          = 280,

  BZLA_SMTOK_CONCAT  = 281, /* QF_BV specific symbols */
  BZLA_SMTOK_EQ      = 282,
  BZLA_SMTOK_EXTRACT = 283,
  BZLA_SMTOK_BIT0    = 284,
  BZLA_SMTOK_BIT1    = 285,
  BZLA_SMTOK_BVADD   = 286,
  BZLA_SMTOK_BVNOT   = 287,
  BZLA_SMTOK_BVMUL   = 288,
  BZLA_SMTOK_BVULE   = 289,
  BZLA_SMTOK_BVAND   = 290,
  BZLA_SMTOK_BVLSHR  = 291,
  BZLA_SMTOK_BVSLT   = 292,
  BZLA_SMTOK_BVULT   = 293,
  BZLA_SMTOK_BVNEG   = 294,
  BZLA_SMTOK_BVSLE   = 295,
  BZLA_SMTOK_BVSHL   = 296,
  BZLA_SMTOK_BVSUB   = 297,
  BZLA_SMTOK_BVSDIV  = 298,
  BZLA_SMTOK_BVASHR  = 299,
  BZLA_SMTOK_BVOR    = 300,
  BZLA_SMTOK_BVUDIV  = 301,
  BZLA_SMTOK_BVUREM  = 302,
  BZLA_SMTOK_BVNAND  = 303,
  BZLA_SMTOK_BVNOR   = 304,
  BZLA_SMTOK_BVUGT   = 305,
  BZLA_SMTOK_BVUGE   = 306,
  BZLA_SMTOK_BVSGT   = 307,
  BZLA_SMTOK_BVSGE   = 308,
  BZLA_SMTOK_BVCOMP  = 309,

  BZLA_SMTOK_REPEAT       = 310,
  BZLA_SMTOK_ZERO_EXTEND  = 311,
  BZLA_SMTOK_SIGN_EXTEND  = 312,
  BZLA_SMTOK_ROTATE_LEFT  = 313,
  BZLA_SMTOK_ROTATE_RIGHT = 314,

  BZLA_SMTOK_BVXOR  = 315,
  BZLA_SMTOK_BVSREM = 316,
  BZLA_SMTOK_BVSMOD = 317,
  BZLA_SMTOK_BVXNOR = 318,

  BZLA_SMTOK_SELECT = 319,
  BZLA_SMTOK_STORE  = 320,

  BZLA_SMTOK_UNSUPPORTED_KEYWORD = 512,
  BZLA_SMTOK_AXIOMS              = 512,
  BZLA_SMTOK_DEFINITIONS         = 513,
  BZLA_SMTOK_EXISTS              = 514,
  BZLA_SMTOK_EXTENSIONS          = 515,
  BZLA_SMTOK_FORALL              = 516,
  BZLA_SMTOK_FUNS                = 517,
  BZLA_SMTOK_LANGUAGE            = 518,
  BZLA_SMTOK_LOGIC               = 519,
  BZLA_SMTOK_PREDS               = 520,
  BZLA_SMTOK_SORTS               = 521,
  BZLA_SMTOK_THEORY              = 522,
  BZLA_SMTOK_THEORYATTR          = 523,

  BZLA_SMTOK_INTERNAL   = 1024,
  BZLA_SMTOK_BIND       = 1024,
  BZLA_SMTOK_TRANSLATED = 1025,  // TODO ...
};

typedef enum BzlaSMTToken BzlaSMTToken;

struct BzlaSMTNode
{
  void *head;
  void *tail;
  BoolectorNode *exp;  // TODO overlay with tail/head?
};

BZLA_DECLARE_STACK(BzlaSMTNodePtr, BzlaSMTNode *);

struct BzlaSMTSymbol
{
  char *name;
  BzlaSMTToken token;
  BzlaSMTSymbol *next;
  BzlaSMTNode *last;
  BoolectorNode *exp;
};

struct BzlaSMTParser
{
  BzlaMemMgr *mem;
  Bzla *bzla;
  bool parsed;

  uint32_t verbosity;
  uint32_t modelgen;
  uint32_t incremental;
  BzlaOptIncrementalSMT1 incremental_smt1;

  struct
  {
    uint32_t nparsed, handled;
  } assumptions;
  struct
  {
    uint32_t nparsed, handled, nchecked;
  } formulas;

  uint32_t nprefix;
  BzlaCharStack *prefix;
  FILE *infile;
  const char *infile_name;
  FILE *outfile;
  uint32_t lineno;
  bool saved;
  int32_t saved_char;

  uint_least64_t bytes;

  BzlaLogic required_logic;

  char *error;
  BzlaCharStack buffer;

  unsigned char types[256];

  BzlaSMTSymbol *symbol;
  BzlaSMTSymbol **symtab;
  uint32_t szsymtab;
  uint32_t symbols;

  uint32_t constants;

  BzlaSMTNode *bind;
  BzlaSMTNode *translated;

  BzlaPtrHashTable *nodes;
  BzlaSMTNodePtrStack stack;
  BzlaSMTNodePtrStack work;
  BzlaSMTNodePtrStack delete;
  BzlaIntStack heads;
};

/*------------------------------------------------------------------------*/

static uint32_t bzla_smt_primes[] = {1001311, 2517041, 3543763, 4026227};
#define BZLA_SMT_PRIMES ((sizeof bzla_smt_primes) / sizeof *bzla_smt_primes)

static void *
car(BzlaSMTNode *node)
{
  assert(node);
  return node->head;
}

static void *
cdr(BzlaSMTNode *node)
{
  assert(node);
  return node->tail;
}

#define isleaf(l) ((uintptr_t) 1 & (uintptr_t)(l))
#define leaf(l) ((void *) ((uintptr_t) 1 | (uintptr_t)(l)))
#define strip(l) ((BzlaSMTSymbol *) ((~(uintptr_t) 1) & (uintptr_t)(l)))

static BzlaSMTNode *
cons(BzlaSMTParser *parser, void *h, void *t)
{
  BzlaSMTNode *res;

  BZLA_NEW(parser->mem, res);
  BZLA_CLR(res);

  bzla_hashptr_table_add(parser->nodes, res);
  assert(parser->nodes->count > 0);

  res->head = h;
  res->tail = t;

  return res;
}

static uint32_t
hash_name(const char *name)
{
  uint32_t i, res;
  const char *p;
  char ch;

  i   = 0;
  res = 0;

  for (p = name; (ch = *p); p++)
  {
    res += bzla_smt_primes[i++] * (uint32_t) ch;

    if (i == BZLA_SMT_PRIMES) i = 0;

    res = (res << 4) | (res >> 28);
  }

  return res;
}

static BzlaSMTSymbol **
find_symbol_position(BzlaSMTParser *parser, const char *name)
{
  uint32_t h = hash_name(name) & (parser->szsymtab - 1);
  BzlaSMTSymbol **p, *s;

  for (p = parser->symtab + h; (s = *p) && strcmp(name, s->name); p = &s->next)
    ;

  return p;
}

static void
delete_symbol(BzlaSMTParser *parser, BzlaSMTSymbol *symbol)
{
  BoolectorNode *exp;

  assert(parser->symbols > 0);
  parser->symbols--;

  bzla_mem_freestr(parser->mem, symbol->name);

  if ((exp = symbol->exp)) boolector_release(parser->bzla, exp);

  BZLA_DELETE(parser->mem, symbol);
}

static void
remove_and_delete_symbol(BzlaSMTParser *parser, BzlaSMTSymbol *symbol)
{
  BzlaSMTSymbol **p;

  p = find_symbol_position(parser, symbol->name);
  assert(*p == symbol);

  *p = symbol->next;
  delete_symbol(parser, symbol);
}

static void
delete_smt_node(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  BzlaSMTSymbol *s;

  if (!node) return;

  assert(parser->nodes->count > 0);
  assert(bzla_hashptr_table_get(parser->nodes, node));
  bzla_hashptr_table_remove(parser->nodes, node, 0, 0);

  if (node->exp) boolector_release(parser->bzla, node->exp);

  if (!parser->modelgen && isleaf(car(node)))
  {
    s = strip(car(node));
    if (s->last == node) remove_and_delete_symbol(parser, s);
  }

  BZLA_DELETE(parser->mem, node);
}

static void
smt_message(BzlaSMTParser *parser, uint32_t level, const char *fmt, ...)
{
  va_list ap;

  if (parser->verbosity < level) return;

  fflush(stdout);
  fprintf(stdout, "[btorsmt] ");
  if (parser->incremental) printf("%d : ", parser->formulas.nchecked);
  va_start(ap, fmt);
  vfprintf(stdout, fmt, ap);
  va_end(ap);
  fprintf(stdout, " after %.2f seconds\n", bzla_util_time_stamp());
  fflush(stdout);
}

static void
recursively_delete_smt_node(BzlaSMTParser *parser, BzlaSMTNode *root)
{
  BzlaSMTNode *node;

  assert(BZLA_EMPTY_STACK(parser->delete));

  BZLA_PUSH_STACK(parser->delete, root);
  while (!BZLA_EMPTY_STACK(parser->delete))
  {
    node = BZLA_POP_STACK(parser->delete);

    if (!node) continue;

    if (isleaf(node)) continue;

    if (car(node) == parser->bind)
    {
      /* NOTE: assignment == cdr (node) shared, so do not delete here */
      assert(cdr(node));
    }
    else
    {
      BZLA_PUSH_STACK(parser->delete, cdr(node));
      BZLA_PUSH_STACK(parser->delete, car(node));
    }

    delete_smt_node(parser, node);
  }
}

static uint32_t
length(BzlaSMTNode *node)
{
  BzlaSMTNode *p;
  uint32_t res;

  assert(!isleaf(node));

  res = 0;
  for (p = node; p; p = cdr(p)) res++;

  return res;
}

static bool
is_list_of_length(BzlaSMTNode *node, uint32_t l)
{
  if (isleaf(node)) return false;

  return length(node) == l;
}

static void
release_smt_symbols(BzlaSMTParser *parser)
{
  BzlaSMTSymbol *p, *next;
  uint32_t i;

  for (i = 0; i < parser->szsymtab; i++)
  {
    for (p = parser->symtab[i]; p; p = next)
    {
      next = p->next;
      delete_symbol(parser, p);
    }
  }
  BZLA_DELETEN(parser->mem, parser->symtab, parser->szsymtab);
  parser->symtab   = 0;
  parser->szsymtab = 0;
}

static void
release_smt_nodes(BzlaSMTParser *parser)
{
  while (parser->nodes && parser->nodes->count)
    recursively_delete_smt_node(parser, parser->nodes->first->key);
}

static void
release_smt_internals(BzlaSMTParser *parser)
{
  release_smt_nodes(parser);
  release_smt_symbols(parser);

  if (parser->nodes)
  {
    bzla_hashptr_table_delete(parser->nodes);
    parser->nodes = 0;
  }
  BZLA_RELEASE_STACK(parser->stack);
  BZLA_RELEASE_STACK(parser->work);
  BZLA_RELEASE_STACK(parser->delete);
  BZLA_RELEASE_STACK(parser->heads);
  BZLA_RELEASE_STACK(parser->buffer);
}

static void
delete_smt_parser(BzlaSMTParser *parser)
{
  BzlaMemMgr *mm;

  mm = parser->mem;

  release_smt_internals(parser);

  bzla_mem_freestr(mm, parser->error);

  BZLA_DELETE(mm, parser);
  bzla_mem_mgr_delete(mm);
}

static char *
perr_smt(BzlaSMTParser *parser, const char *fmt, ...)
{
  size_t bytes;
  va_list ap;

  if (!parser->error)
  {
    va_start(ap, fmt);
    bytes = bzla_mem_parse_error_msg_length(parser->infile_name, fmt, ap);
    va_end(ap);

    va_start(ap, fmt);
    parser->error = bzla_mem_parse_error_msg(
        parser->mem, parser->infile_name, parser->lineno, -1, fmt, ap, bytes);
    va_end(ap);
  }

  return parser->error;
}

static void
enlarge_symtab(BzlaSMTParser *parser)
{
  BzlaSMTSymbol *p, *next, **old_symtab, **new_symtab;
  uint32_t h, i, old_size, new_size;

  old_symtab = parser->symtab;
  old_size   = parser->szsymtab;

  new_size = old_size ? 2 * old_size : 1;
  BZLA_NEWN(parser->mem, new_symtab, new_size);
  BZLA_CLRN(new_symtab, new_size);

  for (i = 0; i < old_size; i++)
  {
    for (p = old_symtab[i]; p; p = next)
    {
      next          = p->next;
      h             = hash_name(p->name) & (new_size - 1);
      p->next       = new_symtab[h];
      new_symtab[h] = p;
    }
  }

  BZLA_DELETEN(parser->mem, old_symtab, old_size);

  parser->symtab   = new_symtab;
  parser->szsymtab = new_size;
}

static BzlaSMTSymbol *
insert_symbol(BzlaSMTParser *parser, const char *name)
{
  BzlaSMTSymbol **p, *res;

  if (parser->szsymtab == parser->symbols) enlarge_symtab(parser);

  p = find_symbol_position(parser, name);
  if (!(res = *p))
  {
    BZLA_NEW(parser->mem, res);
    BZLA_CLR(res);

    res->token = BZLA_SMTOK_IDENTIFIER;
    res->name  = bzla_mem_strdup(parser->mem, name);

    parser->symbols++;
    *p = res;
  }

  return res;
}

static BzlaSMTParser *
new_smt_parser(Bzla *bzla)
{
  BzlaSMTSymbol *bind, *translated;
  BzlaMemMgr *mem;
  BzlaSMTParser *res;
  unsigned char type;
  int32_t ch;

  mem = bzla_mem_mgr_new();
  BZLA_NEW(mem, res);
  BZLA_CLR(res);

  res->verbosity        = boolector_get_opt(bzla, BZLA_OPT_VERBOSITY);
  res->modelgen         = boolector_get_opt(bzla, BZLA_OPT_MODEL_GEN);
  res->incremental      = boolector_get_opt(bzla, BZLA_OPT_INCREMENTAL);
  res->incremental_smt1 = boolector_get_opt(bzla, BZLA_OPT_INCREMENTAL_SMT1);

  smt_message(res, 2, "initializing SMT parser");
  if (res->incremental)
  {
    smt_message(res, 2, "incremental checking of SMT benchmark");
    if (res->incremental_smt1 == BZLA_INCREMENTAL_SMT1_BASIC)
      smt_message(res, 2, "stop after first satisfiable ':formula'");
    else if (res->incremental_smt1 == BZLA_INCREMENTAL_SMT1_CONTINUE)
      smt_message(res, 2, "check all ':formula' for satisfiability");
  }

  res->mem  = mem;
  res->bzla = bzla;

  res->nodes = bzla_hashptr_table_new(mem, 0, 0);
  BZLA_INIT_STACK(mem, res->stack);
  BZLA_INIT_STACK(mem, res->work);
  BZLA_INIT_STACK(mem, res->delete);
  BZLA_INIT_STACK(mem, res->heads);
  BZLA_INIT_STACK(mem, res->buffer);

  res->required_logic = BZLA_LOGIC_QF_BV;

  type = BZLA_SMTCC_IDENTIFIER_START | BZLA_SMTCC_IDENTIFIER_MIDDLE;

  for (ch = 'a'; ch <= 'z'; ch++) res->types[ch] |= type;
  for (ch = 'A'; ch <= 'Z'; ch++) res->types[ch] |= type;

  res->types['_'] |= type;
  res->types['.'] |= BZLA_SMTCC_IDENTIFIER_MIDDLE;
  res->types['\''] |= BZLA_SMTCC_IDENTIFIER_MIDDLE;

  type = BZLA_SMTCC_IDENTIFIER_MIDDLE;
  type |= BZLA_SMTCC_DIGIT;

  res->types['0'] |= type;

  type |= BZLA_SMTCC_NUMERAL_START;
  for (ch = '1'; ch <= '9'; ch++) res->types[ch] |= type;

  res->types['='] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['<'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['>'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['&'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['@'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['#'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['+'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['-'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['*'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['/'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['%'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['|'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;
  res->types['~'] |= BZLA_SMTCC_ARITHMETIC_OPERATOR;

  res->types[' '] |= BZLA_SMTCC_SPACE;
  res->types['\t'] |= BZLA_SMTCC_SPACE;
  res->types['\n'] |= BZLA_SMTCC_SPACE;
  res->types[0xd] |= BZLA_SMTCC_SPACE;

  res->types[':'] |= BZLA_SMTCC_IDENTIFIER_PREFIX;
  res->types['?'] |= BZLA_SMTCC_IDENTIFIER_PREFIX;
  res->types['$'] |= BZLA_SMTCC_IDENTIFIER_PREFIX;

  insert_symbol(res, "and")->token          = BZLA_SMTOK_AND;
  insert_symbol(res, ":assumption")->token  = BZLA_SMTOK_ASSUMPTION;
  insert_symbol(res, ":axioms")->token      = BZLA_SMTOK_AXIOMS;
  insert_symbol(res, "benchmark")->token    = BZLA_SMTOK_BENCHMARK;
  insert_symbol(res, ":definitions")->token = BZLA_SMTOK_DEFINITIONS;
  insert_symbol(res, "distinct")->token     = BZLA_SMTOK_DISTINCT;
  insert_symbol(res, "exists")->token       = BZLA_SMTOK_EXISTS;
  insert_symbol(res, ":extensions")->token  = BZLA_SMTOK_EXTENSIONS;
  insert_symbol(res, ":extrafuns")->token   = BZLA_SMTOK_EXTRAFUNS;
  insert_symbol(res, ":extrapreds")->token  = BZLA_SMTOK_EXTRAPREDS;
  insert_symbol(res, ":extrasorts")->token  = BZLA_SMTOK_EXTRASORTS;
  insert_symbol(res, "false")->token        = BZLA_SMTOK_FALSE;
  insert_symbol(res, "flet")->token         = BZLA_SMTOK_FLET;
  insert_symbol(res, "forall")->token       = BZLA_SMTOK_FORALL;
  insert_symbol(res, ":formula")->token     = BZLA_SMTOK_FORMULA;
  insert_symbol(res, ":funs")->token        = BZLA_SMTOK_FUNS;
  insert_symbol(res, "iff")->token          = BZLA_SMTOK_IFF;
  insert_symbol(res, "if_then_else")->token = BZLA_SMTOK_IF_THEN_ELSE;
  insert_symbol(res, "implies")->token      = BZLA_SMTOK_IMPLIES;
  insert_symbol(res, "ite")->token          = BZLA_SMTOK_ITE;
  insert_symbol(res, ":language")->token    = BZLA_SMTOK_LANGUAGE;
  insert_symbol(res, "let")->token          = BZLA_SMTOK_LET;
  insert_symbol(res, "logic")->token        = BZLA_SMTOK_LOGIC;
  insert_symbol(res, ":logic")->token       = BZLA_SMTOK_LOGICATTR;
  insert_symbol(res, ":notes")->token       = BZLA_SMTOK_NOTES;
  insert_symbol(res, "not")->token          = BZLA_SMTOK_NOT;
  insert_symbol(res, "or")->token           = BZLA_SMTOK_OR;
  insert_symbol(res, ":preds")->token       = BZLA_SMTOK_PREDS;
  insert_symbol(res, "sat")->token          = BZLA_SMTOK_SAT;
  insert_symbol(res, ":sorts")->token       = BZLA_SMTOK_SORTS;
  insert_symbol(res, ":status")->token      = BZLA_SMTOK_STATUS;
  insert_symbol(res, "theory")->token       = BZLA_SMTOK_THEORY;
  insert_symbol(res, ":theory")->token      = BZLA_SMTOK_THEORYATTR;
  insert_symbol(res, "true")->token         = BZLA_SMTOK_TRUE;
  insert_symbol(res, "unknown")->token      = BZLA_SMTOK_UNKNOWN;
  insert_symbol(res, "unsat")->token        = BZLA_SMTOK_UNSAT;
  insert_symbol(res, "xor")->token          = BZLA_SMTOK_XOR;

  bind        = insert_symbol(res, "<internal bind symbol>");
  bind->token = BZLA_SMTOK_BIND;
  res->bind   = leaf(bind);

  translated        = insert_symbol(res, "<internal translated symbol>");
  translated->token = BZLA_SMTOK_TRANSLATED;
  res->translated   = leaf(translated);

  insert_symbol(res, "=")->token      = BZLA_SMTOK_EQ;
  insert_symbol(res, "concat")->token = BZLA_SMTOK_CONCAT;
  insert_symbol(res, "bit0")->token   = BZLA_SMTOK_BIT0;
  insert_symbol(res, "bit1")->token   = BZLA_SMTOK_BIT1;
  insert_symbol(res, "bvadd")->token  = BZLA_SMTOK_BVADD;
  insert_symbol(res, "bvnot")->token  = BZLA_SMTOK_BVNOT;
  insert_symbol(res, "bvmul")->token  = BZLA_SMTOK_BVMUL;
  insert_symbol(res, "bvule")->token  = BZLA_SMTOK_BVULE;
  insert_symbol(res, "bvand")->token  = BZLA_SMTOK_BVAND;
  insert_symbol(res, "bvlshr")->token = BZLA_SMTOK_BVLSHR;
  insert_symbol(res, "bvslt")->token  = BZLA_SMTOK_BVSLT;
  insert_symbol(res, "bvult")->token  = BZLA_SMTOK_BVULT;
  insert_symbol(res, "bvneg")->token  = BZLA_SMTOK_BVNEG;
  insert_symbol(res, "bvsle")->token  = BZLA_SMTOK_BVSLE;
  insert_symbol(res, "bvshl")->token  = BZLA_SMTOK_BVSHL;
  insert_symbol(res, "bvsub")->token  = BZLA_SMTOK_BVSUB;
  insert_symbol(res, "bvsdiv")->token = BZLA_SMTOK_BVSDIV;
  insert_symbol(res, "bvashr")->token = BZLA_SMTOK_BVASHR;
  insert_symbol(res, "bvor")->token   = BZLA_SMTOK_BVOR;
  insert_symbol(res, "bvudiv")->token = BZLA_SMTOK_BVUDIV;
  insert_symbol(res, "bvurem")->token = BZLA_SMTOK_BVUREM;
  insert_symbol(res, "bvnor")->token  = BZLA_SMTOK_BVNOR;
  insert_symbol(res, "bvnand")->token = BZLA_SMTOK_BVNAND;
  insert_symbol(res, "bvugt")->token  = BZLA_SMTOK_BVUGT;
  insert_symbol(res, "bvuge")->token  = BZLA_SMTOK_BVUGE;
  insert_symbol(res, "bvsgt")->token  = BZLA_SMTOK_BVSGT;
  insert_symbol(res, "bvsge")->token  = BZLA_SMTOK_BVSGE;
  insert_symbol(res, "bvcomp")->token = BZLA_SMTOK_BVCOMP;
  insert_symbol(res, "bvxor")->token  = BZLA_SMTOK_BVXOR;
  insert_symbol(res, "bvsrem")->token = BZLA_SMTOK_BVSREM;
  insert_symbol(res, "bvsmod")->token = BZLA_SMTOK_BVSMOD;
  insert_symbol(res, "bvxnor")->token = BZLA_SMTOK_BVXNOR;
  insert_symbol(res, "select")->token = BZLA_SMTOK_SELECT;
  insert_symbol(res, "store")->token  = BZLA_SMTOK_STORE;

  return res;
}

static int32_t
nextch_smt(BzlaSMTParser *parser)
{
  int32_t res;

  if (parser->saved)
  {
    res           = parser->saved_char;
    parser->saved = false;
  }
  else if (parser->prefix
           && parser->nprefix < BZLA_COUNT_STACK(*parser->prefix))
  {
    parser->bytes++;
    res = parser->prefix->start[parser->nprefix++];
  }
  else
  {
    parser->bytes++;
    res = getc(parser->infile);
  }

  if (res == '\n') parser->lineno++;

  return res;
}

static void
savech_smt(BzlaSMTParser *parser, int32_t ch)
{
  assert(!parser->saved);

  parser->saved_char = ch;
  parser->saved      = true;

  if (ch == '\n')
  {
    assert(parser->lineno > 1);
    parser->lineno--;
  }
}

static unsigned char
int2type(BzlaSMTParser *parser, int32_t ch)
{
  if (0 > ch || ch >= 256) return 0;
  return parser->types[ch];
}

static bool
has_prefix(const char *str, const char *prefix)
{
  const char *p, *q;

  for (p = str, q = prefix; *q && *p == *q; p++, q++)
    ;
  return *q == 0;
}

static BzlaSMTToken
nextok(BzlaSMTParser *parser)
{
  unsigned char type;
  BzlaSMTToken res;
  int32_t ch;
  uint32_t count;

  parser->symbol = 0;
  BZLA_RESET_STACK(parser->buffer);

SKIP_WHITE_SPACE:

  ch = nextch_smt(parser);
  if (ch == EOF) return EOF;

  type = int2type(parser, ch);
  if (type & BZLA_SMTCC_SPACE) goto SKIP_WHITE_SPACE;

  if (type & BZLA_SMTCC_IDENTIFIER_START)
  {
    BZLA_PUSH_STACK(parser->buffer, ch);

    while (int2type(parser, (ch = nextch_smt(parser)))
           & BZLA_SMTCC_IDENTIFIER_MIDDLE)
      BZLA_PUSH_STACK(parser->buffer, ch);

    count = 0;

    if (ch == '[')
    {
      BZLA_PUSH_STACK(parser->buffer, ch);

      ch = nextch_smt(parser);

      for (;;)
      {
        if (int2type(parser, ch) & BZLA_SMTCC_NUMERAL_START)
        {
          BZLA_PUSH_STACK(parser->buffer, ch);

          while (int2type(parser, (ch = nextch_smt(parser))) & BZLA_SMTCC_DIGIT)
            BZLA_PUSH_STACK(parser->buffer, ch);

        COUNT_AND_CONTINUE_WITH_NEXT_INDEX:

          count++;

          if (ch == ']') break;

          if (ch != ':') goto UNEXPECTED_CHARACTER;

          BZLA_PUSH_STACK(parser->buffer, ':');
          ch = nextch_smt(parser);
        }
        else if (ch == '0')
        {
          BZLA_PUSH_STACK(parser->buffer, ch);
          ch = nextch_smt(parser);
          goto COUNT_AND_CONTINUE_WITH_NEXT_INDEX;
        }
        else
          goto UNEXPECTED_CHARACTER;
      }

      if (!count) return !perr_smt(parser, "empty index list");

      assert(ch == ']');
      BZLA_PUSH_STACK(parser->buffer, ch);
    }
    else
    {
      if (!ch) goto UNEXPECTED_CHARACTER;

      savech_smt(parser, ch);
    }

    BZLA_PUSH_STACK(parser->buffer, 0);

    parser->symbol = insert_symbol(parser, parser->buffer.start);

    if (count == 2 && has_prefix(parser->symbol->name, "extract["))
      parser->symbol->token = BZLA_SMTOK_EXTRACT;

    if (count == 1)
    {
      if (has_prefix(parser->symbol->name, "repeat["))
        parser->symbol->token = BZLA_SMTOK_REPEAT;

      if (has_prefix(parser->symbol->name, "zero_extend["))
        parser->symbol->token = BZLA_SMTOK_ZERO_EXTEND;

      if (has_prefix(parser->symbol->name, "sign_extend["))
        parser->symbol->token = BZLA_SMTOK_SIGN_EXTEND;

      if (has_prefix(parser->symbol->name, "rotate_left["))
        parser->symbol->token = BZLA_SMTOK_ROTATE_LEFT;

      if (has_prefix(parser->symbol->name, "rotate_right["))
        parser->symbol->token = BZLA_SMTOK_ROTATE_RIGHT;
    }

  CHECK_FOR_UNSUPPORTED_KEYWORD:

    if (parser->symbol->token >= BZLA_SMTOK_UNSUPPORTED_KEYWORD)
      return !perr_smt(
          parser, "unsupported keyword '%s'", parser->buffer.start);

    return parser->symbol->token;
  }

  if (ch == '(') return BZLA_SMTOK_LP;

  if (ch == ')') return BZLA_SMTOK_RP;

  if (type & BZLA_SMTCC_IDENTIFIER_PREFIX)
  {
    res = ch;

    assert(ch == '?' || ch == '$' || ch == ':');

    assert((ch == '?') == (res == BZLA_SMTOK_VAR));
    assert((ch == '$') == (res == BZLA_SMTOK_FVAR));
    assert((ch == ':') == (res == BZLA_SMTOK_ATTR));

    BZLA_PUSH_STACK(parser->buffer, ch);

    ch = nextch_smt(parser);
    if (!(int2type(parser, ch) & BZLA_SMTCC_IDENTIFIER_START))
      return !perr_smt(parser, "expected identifier after '%c'", res);

    BZLA_PUSH_STACK(parser->buffer, ch);

    while (int2type(parser, (ch = nextch_smt(parser)))
           & BZLA_SMTCC_IDENTIFIER_MIDDLE)
      BZLA_PUSH_STACK(parser->buffer, ch);

    if (!ch) goto UNEXPECTED_CHARACTER;

    savech_smt(parser, ch);
    BZLA_PUSH_STACK(parser->buffer, 0);

    parser->symbol = insert_symbol(parser, parser->buffer.start);

    if (res == BZLA_SMTOK_VAR || res == BZLA_SMTOK_FVAR)
      parser->symbol->token = res;

    goto CHECK_FOR_UNSUPPORTED_KEYWORD;
  }

  if (type & BZLA_SMTCC_NUMERAL_START)
  {
    BZLA_PUSH_STACK(parser->buffer, ch);

    while (int2type(parser, (ch = nextch_smt(parser))) & BZLA_SMTCC_DIGIT)
      BZLA_PUSH_STACK(parser->buffer, ch);

  CHECK_FOR_FRACTIONAL_PART:

    if (ch == '.')
    {
      res = BZLA_SMTOK_RATIONAL;

      BZLA_PUSH_STACK(parser->buffer, ch);
      ch = nextch_smt(parser);

      if (int2type(parser, ch) & BZLA_SMTCC_NUMERAL_START)
      {
        BZLA_PUSH_STACK(parser->buffer, ch);

        while (int2type(parser, (ch = nextch_smt(parser)))
               & BZLA_SMTCC_NUMERAL_START)
          BZLA_PUSH_STACK(parser->buffer, ch);
      }
      else if (ch == '0')
      {
        BZLA_PUSH_STACK(parser->buffer, ch);

        ch = nextch_smt(parser);
        if (int2type(parser, ch) & BZLA_SMTCC_DIGIT)
          goto UNEXPECTED_DIGIT_AFTER_ZERO;
      }
      else
        goto UNEXPECTED_CHARACTER;
    }
    else
      res = BZLA_SMTOK_NUMERAL;

    if (!ch) goto UNEXPECTED_CHARACTER;

    savech_smt(parser, ch);
    BZLA_PUSH_STACK(parser->buffer, 0);

    parser->symbol        = insert_symbol(parser, parser->buffer.start);
    parser->symbol->token = res;

    return res;
  }

  if (ch == '0')
  {
    BZLA_PUSH_STACK(parser->buffer, ch);

    ch = nextch_smt(parser);
    if (int2type(parser, ch) & BZLA_SMTCC_DIGIT)
    {
    UNEXPECTED_DIGIT_AFTER_ZERO:
      return !perr_smt(parser, "unexpected digit after '0'");
    }

    goto CHECK_FOR_FRACTIONAL_PART;
  }

  if (type & BZLA_SMTCC_ARITHMETIC_OPERATOR)
  {
    BZLA_PUSH_STACK(parser->buffer, ch);

    while (int2type(parser, (ch = nextch_smt(parser)))
           & BZLA_SMTCC_ARITHMETIC_OPERATOR)
      BZLA_PUSH_STACK(parser->buffer, ch);

    if (!ch) goto UNEXPECTED_CHARACTER;

    BZLA_PUSH_STACK(parser->buffer, 0);

    parser->symbol = insert_symbol(parser, parser->buffer.start);
    if (parser->symbol->token == BZLA_SMTOK_IDENTIFIER)
      parser->symbol->token = BZLA_SMTOK_ARITH;

    return parser->symbol->token;
  }

  if (ch == ';')
  {
    while ((ch = nextch_smt(parser)) != '\n')
      if (ch == EOF) return BZLA_SMTOK_EOF;

    goto SKIP_WHITE_SPACE;
  }

  if (ch == '{')
  {
    BZLA_PUSH_STACK(parser->buffer, ch);

    while ((ch = nextch_smt(parser)) != '}')
    {
      if (ch == '{') return !perr_smt(parser, "unescaped '{' after '{'");

      if (ch == '\\')
      {
        BZLA_PUSH_STACK(parser->buffer, ch);
        ch = nextch_smt(parser);
      }

      if (ch == EOF) return !perr_smt(parser, "unexpected EOF after '{'");

      BZLA_PUSH_STACK(parser->buffer, ch);
    }

    assert(ch == '}');
    BZLA_PUSH_STACK(parser->buffer, ch);
    BZLA_PUSH_STACK(parser->buffer, 0);

    parser->symbol        = insert_symbol(parser, parser->buffer.start);
    parser->symbol->token = BZLA_SMTOK_USERVAL;

    return BZLA_SMTOK_USERVAL;
  }

  if (ch == '"')
  {
    while ((ch = nextch_smt(parser)) != '"')
    {
      if (ch == '\\')
      {
        BZLA_PUSH_STACK(parser->buffer, ch);
        ch = nextch_smt(parser);
      }

      if (ch == EOF) return !perr_smt(parser, "unexpected EOF after '\"'");

      BZLA_PUSH_STACK(parser->buffer, ch);
    }

    BZLA_PUSH_STACK(parser->buffer, 0);

    parser->symbol        = insert_symbol(parser, parser->buffer.start);
    parser->symbol->token = BZLA_SMTOK_STRING;

    return BZLA_SMTOK_STRING;
  }

UNEXPECTED_CHARACTER:
  if (isprint(ch)) return !perr_smt(parser, "unexpected character '%c'", ch);

  return !perr_smt(parser, "unexpected character with ASCII code %d", ch);
}

static void
btorsmtppaux(FILE *file, BzlaSMTNode *node, uint32_t indent)
{
  uint32_t i;

  if (isleaf(node))
    fprintf(file, "%s", ((BzlaSMTSymbol *) strip(node))->name);
  else
  {
    fputc('(', file);

    for (;;)
    {
      btorsmtppaux(file, car(node), indent + 1);
      if (!(node = cdr(node))) break;

      fputc('\n', file);
      for (i = 0; i <= indent; i++) fputc(' ', file);
    }

    fputc(')', file);
  }
}

void
btorsmtpp(BzlaSMTNode *node)
{
  btorsmtppaux(stdout, node, 0);
  fputc('\n', stdout);
  fflush(stdout);
}

static const char *
next_numeral(const char *str)
{
  const char *p = str;
  int32_t ch;

  assert(str);

  if (isdigit((int32_t) *p++))
  {
    while (isdigit(ch = *p++))
      ;

    if (ch == ':')
    {
      assert(isdigit((int32_t) *p));
      return p;
    }

    assert(ch == ']');
  }
  else
  {
    while ((ch = *p++))
      if (ch == '[')
      {
        assert(isdigit((int32_t) *p));
        return p;
      }
  }

  return 0;
}

static int32_t
extrafun(BzlaSMTParser *parser, BzlaSMTNode *fdecl)
{
  BzlaSMTSymbol *symbol, *sortsymbol;
  BzlaSMTNode *node, *sort;
  int32_t addrlen, datalen;
  const char *p;
  BoolectorSort s, is, es;

  if (!fdecl || !cdr(fdecl) || isleaf(fdecl) || !isleaf(node = car(fdecl))
      || (symbol = strip(node))->token != BZLA_SMTOK_IDENTIFIER)
    return !perr_smt(parser, "invalid function declaration");

  if (cdr(cdr(fdecl)))
    return !perr_smt(parser,
                     "no support for function declaration "
                     "with more than one argument");

  sort = car(cdr(fdecl));
  if (!sort || !isleaf(sort)
      || (sortsymbol = strip(sort))->token != BZLA_SMTOK_IDENTIFIER)
  {
  INVALID_SORT:
    return !perr_smt(parser,
                     "invalid or unsupported sort "
                     "in function declaration");
  }

  if (symbol->exp)
    return !perr_smt(parser, "multiple definitions for '%s'", symbol->name);

  p = sortsymbol->name;

  if (!strcmp(p, "Bool"))
  {
    s           = boolector_bool_sort(parser->bzla);
    symbol->exp = boolector_var(parser->bzla, s, symbol->name);
    boolector_release_sort(parser->bzla, s);
  }
  else if (has_prefix(p, "BitVec"))
  {
    if (!(p = next_numeral(p)) || next_numeral(p)) goto INVALID_SORT;

    datalen = atoi(p); /* TODO Overflow? */
    if (!datalen) goto INVALID_SORT;

    s           = boolector_bv_sort(parser->bzla, datalen);
    symbol->exp = boolector_var(parser->bzla, s, symbol->name);
    boolector_release_sort(parser->bzla, s);
  }
  else if (has_prefix(p, "Array"))
  {
    if (!(p = next_numeral(p))) goto INVALID_SORT;

    addrlen = atoi(p); /* TODO Overflow? */
    if (!addrlen) goto INVALID_SORT;

    if (!(p = next_numeral(p)) || next_numeral(p)) goto INVALID_SORT;

    datalen = atoi(p); /* TODO Overflow? */
    if (!datalen) goto INVALID_SORT;

    es          = boolector_bv_sort(parser->bzla, datalen);
    is          = boolector_bv_sort(parser->bzla, addrlen);
    s           = boolector_array_sort(parser->bzla, is, es);
    symbol->exp = boolector_array(parser->bzla, s, symbol->name);
    boolector_release_sort(parser->bzla, is);
    boolector_release_sort(parser->bzla, es);
    boolector_release_sort(parser->bzla, s);

    if (parser->required_logic == BZLA_LOGIC_QF_BV)
    {
      smt_message(parser, 2, "requires QF_AUFBV");
      parser->required_logic = BZLA_LOGIC_QF_AUFBV;
    }

    /* TODO what about 'symbol->name' back annotation? */
  }
  else
    goto INVALID_SORT;

  return 1;
}

static bool
extrafuns(BzlaSMTParser *parser, BzlaSMTNode *list)
{
  BzlaSMTNode *p;

  if (!list || isleaf(list))
    return !perr_smt(parser,
                     "expected non empty list as argument to ':extrafuns'");

  for (p = list; p; p = cdr(p))
    if (!extrafun(parser, car(p))) return 0;

  return parser->error == 0;
}

static bool
extrapred(BzlaSMTParser *parser, BzlaSMTNode *pdecl)
{
  BzlaSMTSymbol *symbol;
  BzlaSMTNode *node;
  BoolectorSort s;

  if (!pdecl || isleaf(pdecl) || !isleaf(node = car(pdecl))
      || (symbol = strip(node))->token != BZLA_SMTOK_IDENTIFIER)
    return !perr_smt(parser, "invalid predicate declaration");

  if (cdr(pdecl))
    return !perr_smt(parser,
                     "no support for predicate declarations with arguments");

  if (symbol->exp)
    return !perr_smt(parser, "multiple definitions for '%s'", symbol->name);

  s           = boolector_bool_sort(parser->bzla);
  symbol->exp = boolector_var(parser->bzla, s, symbol->name);
  boolector_release_sort(parser->bzla, s);

  return true;
}

static bool
extrapreds(BzlaSMTParser *parser, BzlaSMTNode *list)
{
  BzlaSMTNode *p;

  if (!list || isleaf(list))
    return !perr_smt(parser,
                     "expected non empty list as argument to ':extrapreds'");

  for (p = list; p; p = cdr(p))
    if (!extrapred(parser, car(p))) return false;

  return !parser->error;
}

static BzlaSMTToken
node2token(BzlaSMTNode *node)
{
  return (node && isleaf(node)) ? strip(node)->token : BZLA_SMTOK_ERR;
}

static bool
is_let_or_flet(BzlaSMTNode *node)
{
  BzlaSMTToken token = node2token(node);
  return token == BZLA_SMTOK_LET || token == BZLA_SMTOK_FLET;
}

static BoolectorNode *
node2exp(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  const char *p, *start, *end;
  char *tmp, *ext, ch;
  BzlaBitVector *tmpbv, *extbv;
  BzlaSMTSymbol *symbol;
  int32_t len, tlen;
  BzlaSMTToken token;

  if (isleaf(node))
  {
    symbol = strip(node);
    if (symbol->exp) return symbol->exp;

    token = symbol->token;
    if (token == BZLA_SMTOK_TRUE || token == BZLA_SMTOK_BIT1)
      return symbol->exp = boolector_const(parser->bzla, "1");

    if (token == BZLA_SMTOK_FALSE || token == BZLA_SMTOK_BIT0)
      return symbol->exp = boolector_const(parser->bzla, "0");

    p = symbol->name;
    if (*p++ == 'b' && *p++ == 'v')
    {
      if (isdigit((int32_t) *p))
      {
        start = p++;
        for (end = p; isdigit((int32_t) *end); end++)
          ;

        if (*end == '[')
        {
          for (p = end + 1; isdigit((int32_t) *p); p++)
            ;

          if (*p == ']')
          {
            len = atoi(end + 1);
            if (len)
            {
              tmp = bzla_util_dec_to_bin_str_n(parser->mem, start, end - start);

              tlen = (int32_t) strlen(tmp);

              if (tlen <= len)
              {
                if (tlen < len)
                {
                  tmpbv = 0;
                  if (!strcmp(tmp, ""))
                    extbv = bzla_bv_new(parser->mem, len - tlen);
                  else
                  {
                    tmpbv = bzla_bv_char_to_bv(parser->mem, tmp);
                    extbv = bzla_bv_uext(parser->mem, tmpbv, len - tlen);
                  }
                  ext = bzla_bv_to_char(parser->mem, extbv);
                  bzla_mem_freestr(parser->mem, tmp);
                  bzla_bv_free(parser->mem, extbv);
                  if (tmpbv) bzla_bv_free(parser->mem, tmpbv);
                  tmp = ext;
                }

                symbol->exp = boolector_const(parser->bzla, tmp);
                parser->constants++;
              }

              bzla_mem_freestr(parser->mem, tmp);
            }
          }
        }
      }
      else if (*p == 'b')
      {
        if (*++p == 'i' && *++p == 'n')
        {
          for (start = ++p; (ch = *p) == '0' || ch == '1'; p++)
            ;

          if (start < p && !*p)
          {
            symbol->exp = boolector_const(parser->bzla, start);
            parser->constants++;
          }
        }
      }
      else if (*p++ == 'h' && *p++ == 'e' && *p++ == 'x')
      {
        for (start = p; isxdigit((int32_t) *p); p++)
          ;

        if (start < p && !*p)
        {
          len  = 4 * (p - start);
          tmp  = bzla_util_hex_to_bin_str(parser->mem, start);
          tlen = (int32_t) strlen(tmp);
          assert(tlen <= len);
          if (tlen < len)
          {
            tmpbv = 0;
            if (!strcmp(tmp, ""))
              extbv = bzla_bv_new(parser->mem, len - tlen);
            else
            {
              tmpbv = bzla_bv_char_to_bv(parser->mem, tmp);
              extbv = bzla_bv_uext(parser->mem, tmpbv, len - tlen);
            }
            ext = bzla_bv_to_char(parser->mem, extbv);
            bzla_mem_freestr(parser->mem, tmp);
            bzla_bv_free(parser->mem, extbv);
            if (tmpbv) bzla_bv_free(parser->mem, tmpbv);
            tmp = ext;
          }
          symbol->exp = boolector_const(parser->bzla, tmp);
          bzla_mem_freestr(parser->mem, tmp);
          parser->constants++;
        }
      }
      else
      {
        /* DO NOT ADD ANYTHING HERE BECAUSE 'p' CHANGED */
      }
    }

    if (symbol->exp) return symbol->exp;

    (void) perr_smt(parser, "'%s' undefined", strip(node)->name);
    return 0;
  }
  else
  {
    assert(node->exp);
    return node->exp;
  }

  return 0;
}

static BoolectorNode *
node2nonarrayexp(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  BoolectorNode *res;

  res = node2exp(parser, node);
  if (res && boolector_is_array(parser->bzla, res))
  {
    (void) perr_smt(parser, "unexpected array argument");
    res = 0;
  }

  return res;
}

static void
translate_node(BzlaSMTParser *parser, BzlaSMTNode *node, BoolectorNode *exp)
{
  (void) parser;
  assert(!isleaf(node));
  assert(!node->exp);
  node->exp = exp;
}

static void
translate_symbol(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  BzlaSMTNode *c;
  BoolectorNode *a;

  assert(!node->exp);
  if (!is_list_of_length(node, 1))
  {
    (void) perr_smt(parser, "symbolic head with argument");
    return;
  }

  c = car(node);
  if ((a = node2nonarrayexp(parser, c)))
    translate_node(parser, node, boolector_copy(parser->bzla, a));
}

static void
translate_unary(BzlaSMTParser *parser,
                BzlaSMTNode *node,
                const char *name,
                BoolectorNode *(*f)(Bzla *, BoolectorNode *) )
{
  BzlaSMTNode *c;
  BoolectorNode *a;

  assert(!node->exp);

  if (!is_list_of_length(node, 2))
  {
    (void) perr_smt(parser, "expected exactly one argument to '%s'", name);
    return;
  }

  c = car(cdr(node));
  if ((a = node2nonarrayexp(parser, c)))
    translate_node(parser, node, f(parser->bzla, a));
}

static void
translate_binary(BzlaSMTParser *parser,
                 BzlaSMTNode *node,
                 const char *name,
                 BoolectorNode *(*f)(Bzla *, BoolectorNode *, BoolectorNode *) )
{
  BzlaSMTNode *c0, *c1;
  BoolectorNode *a0, *a1;

  assert(!node->exp);

  if (!is_list_of_length(node, 3))
  {
    (void) perr_smt(parser, "expected exactly two arguments to '%s'", name);
    return;
  }

  c0 = car(cdr(node));
  c1 = car(cdr(cdr(node)));

  if ((a0 = node2nonarrayexp(parser, c0)))
    if ((a1 = node2nonarrayexp(parser, c1)))
    {
      if (boolector_bv_get_width(parser->bzla, a0)
          != boolector_bv_get_width(parser->bzla, a1))
        (void) perr_smt(parser, "expression width mismatch");
      else
        translate_node(parser, node, f(parser->bzla, a0, a1));
    }
}

static void
translate_eq(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  bool isarray0, isarray1;
  uint32_t len0, len1;
  BzlaSMTNode *c0, *c1;
  BoolectorNode *a0, *a1;

  assert(!node->exp);

  if (!is_list_of_length(node, 3))
  {
    (void) perr_smt(parser, "expected exactly two arguments to '='");
    return;
  }

  c0 = car(cdr(node));
  a0 = node2exp(parser, c0);
  if (!a0) return;

  c1 = car(cdr(cdr(node)));
  a1 = node2exp(parser, c1);
  if (!a1) return;

  len0 = boolector_bv_get_width(parser->bzla, a0);
  len1 = boolector_bv_get_width(parser->bzla, a1);

  if (len0 != len1)
  {
    (void) perr_smt(parser, "expression width mismatch in '='");
    return;
  }

  isarray0 = boolector_is_array(parser->bzla, a0);
  isarray1 = boolector_is_array(parser->bzla, a1);

  if (isarray0 != isarray1)
  {
    (void) perr_smt(parser, "'=' between array and non array expression");
    return;
  }

  if (isarray0 && isarray1)
  {
    len0 = boolector_array_get_index_width(parser->bzla, a0);
    len1 = boolector_array_get_index_width(parser->bzla, a1);

    if (len0 != len1)
    {
      (void) perr_smt(parser, "index width mismatch in '='");
      return;
    }
  }

  assert(!parser->error);
  translate_node(parser, node, boolector_eq(parser->bzla, a0, a1));
}

static void
translate_associative_binary(BzlaSMTParser *parser,
                             BzlaSMTNode *node,
                             const char *name,
                             BoolectorNode *(*f)(Bzla *,
                                                 BoolectorNode *,
                                                 BoolectorNode *) )
{
  BoolectorNode *res, *tmp, *exp;
  BzlaSMTNode *child, *p;
  uint32_t width;

  assert(!node->exp);

  child = car(cdr(node));

  if (!(exp = node2nonarrayexp(parser, child)))
  {
  CHECK_FOR_PARSE_ERROR_AND_RETURN:
    assert(parser->error);
    return;
  }

  width = boolector_bv_get_width(parser->bzla, exp);
  res   = boolector_copy(parser->bzla, exp);

  for (p = cdr(cdr(node)); p; p = cdr(p))
  {
    child = car(p);
    if (!(exp = node2nonarrayexp(parser, child)))
    {
    RELEASE_RES_CHECK_FOR_PARSE_ERROR_AND_RETURN:
      boolector_release(parser->bzla, res);
      assert(parser->error);
      goto CHECK_FOR_PARSE_ERROR_AND_RETURN;
    }

    if (boolector_bv_get_width(parser->bzla, exp) != width)
    {
      perr_smt(parser, "mismatched width of arguments of '%s'", name);
      goto RELEASE_RES_CHECK_FOR_PARSE_ERROR_AND_RETURN;
    }

    tmp = f(parser->bzla, res, exp); /* left associative ? */
    boolector_release(parser->bzla, res);
    res = tmp;
  }

  translate_node(parser, node, res);
}

static void
translate_cond(BzlaSMTParser *parser, BzlaSMTNode *node, const char *name)
{
  bool isarray1, isarray2;
  uint32_t width1, width2;
  BzlaSMTNode *c0, *c1, *c2;
  BoolectorNode *a0, *a1, *a2;

  assert(!node->exp);

  if (!is_list_of_length(node, 4))
  {
    (void) perr_smt(parser, "expected exactly three arguments to '%s'", name);
    return;
  }

  c0 = car(cdr(node));
  c1 = car(cdr(cdr(node)));
  c2 = car(cdr(cdr(cdr(node))));

  a0 = node2nonarrayexp(parser, c0);
  if (!a0) return;

  if (boolector_bv_get_width(parser->bzla, a0) != 1)
  {
    (void) perr_smt(parser, "non boolean conditional");
    return;
  }

  a1 = node2exp(parser, c1);
  if (!a1) return;

  a2 = node2exp(parser, c2);
  if (!a2) return;

  width1 = boolector_bv_get_width(parser->bzla, a1);
  width2 = boolector_bv_get_width(parser->bzla, a2);

  if (width1 != width2)
  {
    (void) perr_smt(parser, "expression width mismatch in conditional");
    return;
  }

  isarray1 = boolector_is_array(parser->bzla, a1);
  isarray2 = boolector_is_array(parser->bzla, a2);

  if (isarray1 != isarray2)
  {
    (void) perr_smt(parser,
                    "conditional between array and non array expression");
    return;
  }

  if (isarray1 && isarray2)
  {
    width1 = boolector_array_get_index_width(parser->bzla, a1);
    width2 = boolector_array_get_index_width(parser->bzla, a2);

    if (width1 != width2)
    {
      (void) perr_smt(parser, "index width mismatch in conditional");
      return;
    }
  }

  translate_node(parser, node, boolector_cond(parser->bzla, a0, a1, a2));
}

static void
translate_extract(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  BzlaSMTSymbol *symbol;
  uint32_t upper, lower, len;
  const char *p;
  BoolectorNode *exp;

  assert(!node->exp);

  symbol = strip(car(node));
  assert(symbol->token == BZLA_SMTOK_EXTRACT);
  p = symbol->name;

  if (!is_list_of_length(node, 2))
  {
    (void) perr_smt(parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp(parser, car(cdr(node)))))
  {
    assert(parser->error);
    return;
  }

  len = boolector_bv_get_width(parser->bzla, exp);

  p = next_numeral(p);
  assert(p);
  upper = (uint32_t) strtol(p, 0, 10); /* TODO Overflow? */
  p     = next_numeral(p);
  lower = (uint32_t) strtol(p, 0, 10); /* TODO Overflow? */
  assert(!next_numeral(p));

  if (len <= upper || upper < lower)
  {
    (void) perr_smt(parser, "invalid '%s' on expression of width %d", p, len);
    return;
  }

  translate_node(
      parser, node, boolector_bv_slice(parser->bzla, exp, upper, lower));
}

static void
translate_repeat(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  BoolectorNode *tmp, *exp, *res;
  BzlaSMTSymbol *symbol;
  const char *p;
  int32_t i, count;

  assert(!node->exp);

  symbol = strip(car(node));
  assert(symbol->token == BZLA_SMTOK_REPEAT);

  p = symbol->name;

  if (!is_list_of_length(node, 2))
  {
    (void) perr_smt(parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp(parser, car(cdr(node)))))
  {
    assert(parser->error);
    return;
  }

  p = next_numeral(p);
  assert(p);
  assert(!next_numeral(p));
  count = atoi(p); /* TODO Overflow? */

  if (!count)
  {
    (void) perr_smt(parser, "can not handle 'repeat[0]'");
    return;
  }

  res = boolector_copy(parser->bzla, exp);

  for (i = 1; i < count; i++)
  {
    tmp = boolector_concat(parser->bzla, exp, res);
    boolector_release(parser->bzla, res);
    res = tmp;
  }

  translate_node(parser, node, res);
}

static void
translate_extend(BzlaSMTParser *parser,
                 BzlaSMTNode *node,
                 BoolectorNode *(*f)(Bzla *, BoolectorNode *, uint32_t))
{
  BzlaSMTSymbol *symbol;
  const char *p;
  BoolectorNode *exp;
  int32_t pad;

  assert(!node->exp);

  symbol = strip(car(node));
  p      = symbol->name;

  if (!is_list_of_length(node, 2))
  {
    (void) perr_smt(parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp(parser, car(cdr(node)))))
  {
    assert(parser->error);
    return;
  }

  p = next_numeral(p);
  assert(p);
  assert(!next_numeral(p));
  pad = atoi(p); /* TODO Overflow? */

  translate_node(parser, node, f(parser->bzla, exp, pad));
}

static void
translate_rotate(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  BoolectorNode *exp, *l, *r;
  BzlaSMTSymbol *symbol;
  BzlaSMTToken token;
  uint32_t shift, width;
  const char *p;

  assert(!node->exp);

  symbol = strip(car(node));
  token  = symbol->token;
  assert(token == BZLA_SMTOK_ROTATE_LEFT || token == BZLA_SMTOK_ROTATE_RIGHT);

  p = symbol->name;

  if (!is_list_of_length(node, 2))
  {
    (void) perr_smt(parser, "expected exactly one argument to '%s'", p);
    return;
  }

  if (!(exp = node2nonarrayexp(parser, car(cdr(node)))))
  {
    assert(parser->error);
    return;
  }

  p = next_numeral(p);
  assert(p);
  assert(!next_numeral(p));
  shift = (uint32_t) strtol(p, 0, 10); /* TODO Overflow? */

  width = boolector_bv_get_width(parser->bzla, exp);
  assert(width > 0);
  shift %= width;

  if (shift)
  {
    if (token == BZLA_SMTOK_ROTATE_LEFT) shift = width - shift;

    assert(1 <= shift && shift < width);

    l = boolector_bv_slice(parser->bzla, exp, shift - 1, 0);
    r = boolector_bv_slice(parser->bzla, exp, width - 1, shift);

    translate_node(parser, node, boolector_concat(parser->bzla, l, r));
    assert(boolector_bv_get_width(parser->bzla, node->exp) == width);

    boolector_release(parser->bzla, l);
    boolector_release(parser->bzla, r);
  }
  else
    translate_node(parser, node, boolector_copy(parser->bzla, exp));
}

static void
translate_concat(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  BzlaSMTNode *c0, *c1;
  BoolectorNode *a0, *a1;

  assert(!node->exp);

  if (!is_list_of_length(node, 3))
  {
    (void) perr_smt(parser, "expected exactly two arguments to 'concat'");
    return;
  }

  c0 = car(cdr(node));
  c1 = car(cdr(cdr(node)));

  if ((a0 = node2nonarrayexp(parser, c0)))
    if ((a1 = node2nonarrayexp(parser, c1)))
      translate_node(parser, node, boolector_concat(parser->bzla, a0, a1));
}

static void
translate_shift(BzlaSMTParser *parser,
                BzlaSMTNode *node,
                const char *name,
                BoolectorNode *(*f)(Bzla *, BoolectorNode *, BoolectorNode *) )
{
  BoolectorNode *a0, *a1, *c, *e, *t, *e0, *u, *l, *tmp;
  uint32_t width, l0, l1, p0, p1;
  BzlaSMTNode *c0, *c1;
  BoolectorSort s;

  assert(!node->exp);

  if (!is_list_of_length(node, 3))
  {
    (void) perr_smt(parser, "expected exactly two arguments to '%s'", name);
    return;
  }

  c0 = car(cdr(node));
  c1 = car(cdr(cdr(node)));

  if (!(a0 = node2nonarrayexp(parser, c0)))
  {
    assert(parser->error);
    return;
  }

  if (!(a1 = node2nonarrayexp(parser, c1)))
  {
    assert(parser->error);
    return;
  }

  width = boolector_bv_get_width(parser->bzla, a0);

  if (width != boolector_bv_get_width(parser->bzla, a1))
  {
    (void) perr_smt(parser, "expression width mismatch");
    return;
  }

  l1 = 0;
  for (l0 = 1; l0 < width; l0 *= 2) l1++;

  assert(l0 == (1u << l1));

  if (width == 1)
  {
    assert(l0 == 1);
    assert(l1 == 0);

    if (f == boolector_sra)
      translate_node(parser, node, boolector_copy(parser->bzla, a0));
    else
    {
      tmp = boolector_bv_not(parser->bzla, a1);
      translate_node(parser, node, boolector_bv_and(parser->bzla, a0, tmp));
      boolector_release(parser->bzla, tmp);
    }
  }
  else
  {
    assert(width >= 1);
    assert(width <= l0);

    p0 = l0 - width;
    p1 = width - l1;

    assert(p1 > 0);

    u = boolector_bv_slice(parser->bzla, a1, width - 1, width - p1);
    l = boolector_bv_slice(parser->bzla, a1, l1 - 1, 0);

    assert(boolector_bv_get_width(parser->bzla, u) == p1);
    assert(boolector_bv_get_width(parser->bzla, l) == l1);

    if (p1 > 1)
      c = boolector_bv_redor(parser->bzla, u);
    else
      c = boolector_copy(parser->bzla, u);

    boolector_release(parser->bzla, u);

    if (f == boolector_sra)
    {
      tmp = boolector_bv_slice(parser->bzla, a0, width - 1, width - 1);
      t   = boolector_bv_sext(parser->bzla, tmp, width - 1);
      boolector_release(parser->bzla, tmp);
    }
    else
    {
      s = boolector_bv_sort(parser->bzla, width);
      t = boolector_zero(parser->bzla, s);
      boolector_release_sort(parser->bzla, s);
    }

    if (!p0)
      e0 = boolector_copy(parser->bzla, a0);
    else if (f == boolector_sra)
      e0 = boolector_bv_sext(parser->bzla, a0, p0);
    else
      e0 = boolector_bv_uext(parser->bzla, a0, p0);

    assert(boolector_bv_get_width(parser->bzla, e0) == l0);

    e = f(parser->bzla, e0, l);
    boolector_release(parser->bzla, e0);
    boolector_release(parser->bzla, l);

    if (p0 > 0)
    {
      tmp = boolector_bv_slice(parser->bzla, e, width - 1, 0);
      boolector_release(parser->bzla, e);
      e = tmp;
    }

    translate_node(parser, node, boolector_cond(parser->bzla, c, t, e));

    boolector_release(parser->bzla, c);
    boolector_release(parser->bzla, t);
    boolector_release(parser->bzla, e);
  }
}

static void
translate_select(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  BzlaSMTNode *c0, *c1;
  BoolectorNode *a0, *a1;

  assert(!node->exp);

  if (!is_list_of_length(node, 3))
  {
    (void) perr_smt(parser, "expected exactly two arguments to 'select'");
    return;
  }

  c0 = car(cdr(node));
  c1 = car(cdr(cdr(node)));

  if (!(a0 = node2exp(parser, c0)))
  {
    assert(parser->error);
    return;
  }

  if (!boolector_is_array(parser->bzla, a0))
  {
    (void) perr_smt(parser, "invalid first argument to 'select'");
    return;
  }

  if (!(a1 = node2nonarrayexp(parser, c1)))
  {
    assert(parser->error);
    return;
  }

  if (boolector_array_get_index_width(parser->bzla, a0)
      != boolector_bv_get_width(parser->bzla, a1))
  {
    (void) perr_smt(parser, "mismatched bit width of 'select' index");
    return;
  }

  translate_node(parser, node, boolector_read(parser->bzla, a0, a1));
}

static void
translate_store(BzlaSMTParser *parser, BzlaSMTNode *node)
{
  BzlaSMTNode *c0, *c1, *c2;
  BoolectorNode *a0, *a1, *a2;

  assert(!node->exp);

  if (!is_list_of_length(node, 4))
  {
    (void) perr_smt(parser, "expected exactly three arguments to 'store'");
    return;
  }

  c0 = car(cdr(node));
  c1 = car(cdr(cdr(node)));
  c2 = car(cdr(cdr(cdr(node))));

  if (!(a0 = node2exp(parser, c0)))
  {
    assert(parser->error);
    return;
  }

  if (!boolector_is_array(parser->bzla, a0))
  {
    (void) perr_smt(parser, "invalid first argument to 'store'");
    return;
  }

  if (!(a1 = node2nonarrayexp(parser, c1)))
  {
    assert(parser->error);
    return;
  }

  if (boolector_array_get_index_width(parser->bzla, a0)
      != boolector_bv_get_width(parser->bzla, a1))
  {
    (void) perr_smt(parser, "mismatched bit width of 'store' index");
    return;
  }

  if (!(a2 = node2nonarrayexp(parser, c2)))
  {
    assert(parser->error);
    return;
  }

  if (boolector_bv_get_width(parser->bzla, a2)
      != boolector_bv_get_width(parser->bzla, a0))
  {
    (void) perr_smt(parser, "mismatched bit width of 'store' value");
    return;
  }

  translate_node(parser, node, boolector_write(parser->bzla, a0, a1, a2));
}

static BoolectorNode *
translate_formula(BzlaSMTParser *parser, BzlaSMTNode *root)
{
  BzlaSMTNode *node, *child, *p, **s, **t, *tmp;
  BzlaSMTNode *assignment, *body;
  BzlaSMTSymbol *symbol;
  BzlaSMTToken token;
  uint32_t start, end;
  BoolectorNode *exp;

  assert(BZLA_EMPTY_STACK(parser->work));
  assert(BZLA_EMPTY_STACK(parser->stack));

  assert(root);
  BZLA_PUSH_STACK(parser->stack, root);

  while (!BZLA_EMPTY_STACK(parser->stack))
  {
    node = BZLA_POP_STACK(parser->stack);

    if (node)
    {
      if (isleaf(node))
      {
        /* DO NOTHING HERE */
      }
      else if (car(node) == parser->bind)
      {
        BZLA_PUSH_STACK(parser->work, node);
      }
      else if (is_let_or_flet(car(node)))
      {
        /* node       == ([f]let assignment body)
         * assignment == (var term)
         */
        if (!cdr(node) || !(assignment = car(cdr(node))) || isleaf(assignment)
            || !(token = node2token(car(assignment)))
            || (token != BZLA_SMTOK_FVAR && token != BZLA_SMTOK_VAR)
            || !cdr(assignment) || cdr(cdr(assignment)) || !cdr(cdr(node))
            || cdr(cdr(cdr(node))))
          return perr_smt(parser, "illformed 'let' or 'flet'"),
                 (BoolectorNode *) 0;

        body = car(cdr(cdr(node)));

        BZLA_PUSH_STACK(parser->stack, node);
        BZLA_PUSH_STACK(parser->stack, 0);

        BZLA_PUSH_STACK(parser->stack, body);

        BZLA_PUSH_STACK(parser->stack, cons(parser, parser->bind, assignment));

        BZLA_PUSH_STACK(parser->stack, car(cdr(assignment)));
      }
      else
      {
        BZLA_PUSH_STACK(parser->stack, node);
        BZLA_PUSH_STACK(parser->stack, 0);

        start = BZLA_COUNT_STACK(parser->stack);

        for (p = node; p; p = cdr(p))
        {
          child = car(p);
          assert(child);
          BZLA_PUSH_STACK(parser->stack, child);
        }

        end = BZLA_COUNT_STACK(parser->stack);

        if (start < end)
        {
          s = parser->stack.start + start;
          t = parser->stack.start + end - 1;

          while (s < t)
          {
            tmp = *s;
            *s  = *t;
            *t  = tmp;

            s++;
            t--;
          }
        }
      }
    }
    else
    {
      assert(!BZLA_EMPTY_STACK(parser->stack));

      node = BZLA_POP_STACK(parser->stack);

      assert(node);
      assert(!isleaf(node));

      BZLA_PUSH_STACK(parser->work, node);
    }
  }

  node = 0;
  for (s = parser->work.start; s < parser->work.top; s++)
  {
    node = *s;

    assert(node);
    assert(!isleaf(node));

    child = car(node);

    if (!child) return perr_smt(parser, "empty list"), (BoolectorNode *) 0;

    if (isleaf(child))
    {
      symbol = strip(child);

      switch (symbol->token)
      {
        case BZLA_SMTOK_NOT:
          translate_unary(parser, node, "not", boolector_bv_not);
          break;
        case BZLA_SMTOK_AND:
          translate_associative_binary(parser, node, "and", boolector_bv_and);
          break;
        case BZLA_SMTOK_OR:
          translate_associative_binary(parser, node, "or", boolector_or);
          break;
        case BZLA_SMTOK_IMPLIES:
          translate_binary(parser, node, "implies", boolector_implies);
          break;
        case BZLA_SMTOK_XOR:
          translate_associative_binary(parser, node, "xor", boolector_bv_xor);
          break;
        case BZLA_SMTOK_IFF:
          translate_associative_binary(parser, node, "iff", boolector_bv_xnor);
          break;

        case BZLA_SMTOK_EQ: translate_eq(parser, node); break;

        case BZLA_SMTOK_DISTINCT:
          translate_binary(parser, node, "distinct", boolector_ne);
          break;
        case BZLA_SMTOK_ITE: translate_cond(parser, node, "ite"); break;
        case BZLA_SMTOK_IF_THEN_ELSE:
          translate_cond(parser, node, "if_then_else");
          break;
        case BZLA_SMTOK_BIND:
          assert(cdr(node));
          assert(cdr(cdr(node)));
          assert(!cdr(cdr(cdr(node))));
          assert(isleaf(car(cdr(node))));
          symbol = strip(car(cdr(node)));
          if (symbol->exp)
            return perr_smt(parser, "unsupported nested '[f]let'"),
                   (BoolectorNode *) 0;
          body = car(cdr(cdr(node)));
          if ((exp = node2exp(parser, body)))
          {
            if (symbol->token == BZLA_SMTOK_FVAR)
            {
              if (boolector_bv_get_width(parser->bzla, exp) != 1)
              {
                return perr_smt(parser, "flet assignment width not one"),
                       (BoolectorNode *) 0;
              }
            }
            else
              assert(symbol->token == BZLA_SMTOK_VAR);

            assert(!symbol->exp);
            symbol->exp = boolector_copy(parser->bzla, exp);
          }
          /* Prevent leaking of 'bind' nodes.  */
          *s = 0;
          delete_smt_node(parser, node);
          break;
        case BZLA_SMTOK_LET:
        case BZLA_SMTOK_FLET:
          symbol = strip(car(car(cdr(node))));
          assert(symbol->token == BZLA_SMTOK_FVAR
                 || symbol->token == BZLA_SMTOK_VAR);
          assert(symbol->exp);
          body = car(cdr(cdr(node)));
          if ((exp = node2exp(parser, body)))
            node->exp = boolector_copy(parser->bzla, exp);
          boolector_release(parser->bzla, symbol->exp);
          symbol->exp = 0;
          break;
        case BZLA_SMTOK_EXTRACT: translate_extract(parser, node); break;
        case BZLA_SMTOK_REPEAT: translate_repeat(parser, node); break;
        case BZLA_SMTOK_ZERO_EXTEND:
          translate_extend(parser, node, boolector_bv_uext);
          break;
        case BZLA_SMTOK_SIGN_EXTEND:
          translate_extend(parser, node, boolector_bv_sext);
          break;
        case BZLA_SMTOK_ROTATE_RIGHT:
        case BZLA_SMTOK_ROTATE_LEFT: translate_rotate(parser, node); break;
        case BZLA_SMTOK_CONCAT: translate_concat(parser, node); break;
        case BZLA_SMTOK_BVNOT:
          translate_unary(parser, node, "bvnot", boolector_bv_not);
          break;
        case BZLA_SMTOK_BVNEG:
          translate_unary(parser, node, "bvneg", boolector_bv_neg);
          break;
        case BZLA_SMTOK_BVADD:
          translate_associative_binary(parser, node, "bvadd", boolector_add);
          break;
        case BZLA_SMTOK_BVSUB:
          translate_binary(parser, node, "bvsub", boolector_sub);
          break;
        case BZLA_SMTOK_BVSDIV:
          translate_binary(parser, node, "bvsdiv", boolector_sdiv);
          break;
        case BZLA_SMTOK_BVUDIV:
          translate_binary(parser, node, "bvudiv", boolector_udiv);
          break;
        case BZLA_SMTOK_BVUREM:
          translate_binary(parser, node, "bvurem", boolector_urem);
          break;
        case BZLA_SMTOK_BVSREM:
          translate_binary(parser, node, "bvsrem", boolector_srem);
          break;
        case BZLA_SMTOK_BVSMOD:
          translate_binary(parser, node, "bvsmod", boolector_smod);
          break;
        case BZLA_SMTOK_BVMUL:
          translate_associative_binary(parser, node, "bvmul", boolector_mul);
          break;
        case BZLA_SMTOK_BVULE:
          translate_binary(parser, node, "bvule", boolector_ulte);
          break;
        case BZLA_SMTOK_BVSLE:
          translate_binary(parser, node, "bvsle", boolector_slte);
          break;
        case BZLA_SMTOK_BVSGT:
          translate_binary(parser, node, "bvsgt", boolector_sgt);
          break;
        case BZLA_SMTOK_BVSGE:
          translate_binary(parser, node, "bvsge", boolector_sgte);
          break;
        case BZLA_SMTOK_BVCOMP:
          translate_binary(parser, node, "bvcomp", boolector_eq);
          break;
        case BZLA_SMTOK_BVULT:
          translate_binary(parser, node, "bvult", boolector_ult);
          break;
        case BZLA_SMTOK_BVUGT:
          translate_binary(parser, node, "bvugt", boolector_ugt);
          break;
        case BZLA_SMTOK_BVUGE:
          translate_binary(parser, node, "bvuge", boolector_ugte);
          break;
        case BZLA_SMTOK_BVSLT:
          translate_binary(parser, node, "bvslt", boolector_slt);
          break;
        case BZLA_SMTOK_BVAND:
          translate_binary(parser, node, "bvand", boolector_bv_and);
          break;
        case BZLA_SMTOK_BVOR:
          translate_binary(parser, node, "bvor", boolector_or);
          break;
        case BZLA_SMTOK_BVXOR:
          translate_binary(parser, node, "bvxor", boolector_bv_xor);
          break;
        case BZLA_SMTOK_BVXNOR:
          translate_binary(parser, node, "bvxnor", boolector_bv_xnor);
          break;
        case BZLA_SMTOK_BVNOR:
          translate_binary(parser, node, "bvnor", boolector_nor);
          break;
        case BZLA_SMTOK_BVNAND:
          translate_binary(parser, node, "bvnand", boolector_bv_nand);
          break;
        case BZLA_SMTOK_BVLSHR:
          translate_shift(parser, node, "bvlshr", boolector_srl);
          break;
        case BZLA_SMTOK_BVASHR:
          translate_shift(parser, node, "bvashr", boolector_sra);
          break;
        case BZLA_SMTOK_BVSHL:
          translate_shift(parser, node, "bvshl", boolector_sll);
          break;
        case BZLA_SMTOK_SELECT: translate_select(parser, node); break;
        case BZLA_SMTOK_STORE: translate_store(parser, node); break;
        default:
          assert(symbol->token != BZLA_SMTOK_TRANSLATED);
          translate_symbol(parser, node);
          break;
      }
    }
    else
    {
      if (is_list_of_length(node, 1))
      {
        if ((exp = node2exp(parser, child)))
          translate_node(parser, node, boolector_copy(parser->bzla, exp));
      }
      else
        (void) perr_smt(parser, "invalid list expression");
    }

    if (parser->error) return (BoolectorNode *) 0;
  }

  BZLA_RESET_STACK(parser->work);

  if (!(exp = node2exp(parser, root)))
  {
    assert(parser->error);
    return (BoolectorNode *) 0;
  }

  if (boolector_bv_get_width(parser->bzla, exp) != 1)
    return perr_smt(parser, "non boolean formula"), (BoolectorNode *) 0;

  assert(!parser->error);

  assert(exp);

  return boolector_copy(parser->bzla, exp);
}

static void
smt_parser_inc_add_release_sat(BzlaSMTParser *parser,
                               BzlaParseResult *res,
                               BoolectorNode *exp)
{
  char *prefix;
  int32_t satres, nchecked, ndigits;
  uint32_t formula;
  assert(parser->formulas.nchecked < parser->formulas.nparsed);
  formula  = parser->formulas.nchecked;
  nchecked = 1;

  if (parser->formulas.nchecked + 1 == parser->formulas.nparsed)
  {
    smt_message(parser, 3, "adding last ':formula' %d permanently", formula);
    boolector_assert(parser->bzla, exp);
  }
  else
  {
    smt_message(parser, 3, "adding ':formula' %d as assumption", formula);
    boolector_assume(parser->bzla, exp);
  }
  boolector_release(parser->bzla, exp);

  satres = boolector_sat(parser->bzla);
  res->nsatcalls += 1;
  if (satres == BOOLECTOR_SAT)
  {
    smt_message(parser, 1, "':formula' %d SAT", formula);
    res->result = BOOLECTOR_SAT;
    fprintf(parser->outfile, "sat\n");
  }
  else
  {
    assert(satres == BOOLECTOR_UNSAT);
    smt_message(parser, 1, "':formula' %d UNSAT", formula);
    if (res->result == BOOLECTOR_UNKNOWN) res->result = BOOLECTOR_UNSAT;
    fprintf(parser->outfile, "unsat\n");
  }
  if (parser->verbosity >= 2) boolector_print_stats(parser->bzla);

  parser->formulas.nchecked += nchecked;

  ndigits = bzla_util_num_digits(parser->formulas.nchecked) + 3;
  BZLA_NEWN(parser->mem, prefix, ndigits);
  sprintf(prefix, "%d:", parser->formulas.nchecked);
  boolector_set_msg_prefix(parser->bzla, prefix);
  BZLA_DELETEN(parser->mem, prefix, ndigits);

  if (parser->formulas.nchecked == parser->formulas.nparsed)
    boolector_set_msg_prefix(parser->bzla, 0);
}

static bool
continue_parsing(BzlaSMTParser *parser, BzlaParseResult *res)
{
  if (res->result != BOOLECTOR_SAT) return true;
  return parser->incremental
         && parser->incremental_smt1 == BZLA_INCREMENTAL_SMT1_CONTINUE;
}

static char *
translate_benchmark(BzlaSMTParser *parser,
                    BzlaSMTNode *top,
                    BzlaParseResult *res)
{
  BzlaSMTSymbol *symbol, *logic, *benchmark;
  BzlaSMTNode *p, *node, *q;
  BoolectorNode *exp;
  BzlaSMTToken status;

  smt_message(parser, 2, "extracting expressions");

  p = top;

  if (!p || !(node = car(p)) || !isleaf(node)
      || strip(node)->token != BZLA_SMTOK_BENCHMARK)
    return perr_smt(parser, "expected 'benchmark' keyword");

  p = cdr(p);

  if (!p || !(benchmark = car(p)) || !isleaf(benchmark)
      || strip(benchmark)->token != BZLA_SMTOK_IDENTIFIER)
    return perr_smt(parser, "expected benchmark name");

  benchmark = strip(benchmark);

  smt_message(parser, 2, "benchmark %s", benchmark->name);

  symbol = 0;

  for (p = top; p; p = cdr(p))
  {
    node = car(p);
    if (!isleaf(node)) continue;

    symbol = strip(node);

    if (symbol->token == BZLA_SMTOK_EXTRASORTS
        || symbol->token == BZLA_SMTOK_EXTRAFUNS
        || symbol->token == BZLA_SMTOK_EXTRAPREDS
        || symbol->token == BZLA_SMTOK_ASSUMPTION
        || symbol->token == BZLA_SMTOK_FORMULA)
      return perr_smt(parser, "'%s' before ':logic'", symbol->name);

    if (symbol->token == BZLA_SMTOK_LOGICATTR) break;
  }

  if (!p) return perr_smt(parser, "no ':logic' attribute found");

  p = cdr(p);
  if (!p) return perr_smt(parser, "argument to ':logic' missing");

  node = car(p);
  if (!isleaf(node)) return perr_smt(parser, "invalid argument to ':logic'");

  logic = strip(node);
  if (!strcmp(logic->name, "QF_BV"))
    res->logic = BZLA_LOGIC_QF_BV;
  else if (!strcmp(logic->name, "QF_AUFBV") || !strcmp(logic->name, "QF_ABV"))
    res->logic = BZLA_LOGIC_QF_AUFBV;
  else
    return perr_smt(parser, "unsupported logic '%s'", logic->name);

  for (p = top; p; p = cdr(p))
  {
    node = car(p);
    if (!isleaf(node)) continue;

    symbol = strip(node);
    if (symbol->token == BZLA_SMTOK_STATUS) break;
  }

  if (p)
  {
    p = cdr(p);
    if (!p) return perr_smt(parser, "argument to ':status' missing");

    node = car(p);
    if (!isleaf(node))
    {
    INVALID_STATUS_ARGUMENT:
      return perr_smt(parser, "invalid ':status' argument");
    }

    symbol = strip(node);
    status = symbol->token;

    if (status == BZLA_SMTOK_SAT)
      res->status = BOOLECTOR_SAT;
    else if (status == BZLA_SMTOK_UNSAT)
      res->status = BOOLECTOR_UNSAT;
    else if (status == BZLA_SMTOK_UNKNOWN)
      res->status = BOOLECTOR_UNKNOWN;
    else
      goto INVALID_STATUS_ARGUMENT;
  }

  for (p = top; p && continue_parsing(parser, res); p = cdr(p))
  {
    q    = p;
    node = car(p);
    if (!isleaf(node)) goto CONTINUE;

    symbol = strip(node);

    switch (symbol->token)
    {
      case BZLA_SMTOK_EXTRAFUNS:
        p = cdr(p);
        if (!p) return perr_smt(parser, "argument to ':extrafuns' missing");

        if (!extrafuns(parser, car(p)))
        {
          assert(parser->error);
          return parser->error;
        }

        break;

      case BZLA_SMTOK_EXTRAPREDS:

        p = cdr(p);
        if (!p) return perr_smt(parser, "argument to ':extrapreds' missing");

        if (!extrapreds(parser, car(p)))
        {
          assert(parser->error);
          return parser->error;
        }

        break;

      case BZLA_SMTOK_ASSUMPTION:

        p = cdr(p);
        if (!p) return perr_smt(parser, "argument to ':assumption' missing");

        exp = translate_formula(parser, car(p));
        if (!exp)
        {
          assert(parser->error);
          return parser->error;
        }

        recursively_delete_smt_node(parser, p->head);
        p->head = 0;

        if (parser->incremental)
        {
          smt_message(parser,
                      3,
                      "adding ':assumption' %d",
                      parser->assumptions.handled);
        }
        boolector_assert(parser->bzla, exp);
        boolector_release(parser->bzla, exp);

        parser->assumptions.handled++;

        break;

      case BZLA_SMTOK_FORMULA:

        p = cdr(p);
        if (!p) return perr_smt(parser, "argument to ':formula' missing");

        exp = translate_formula(parser, car(p));
        if (!exp)
        {
          assert(parser->error);
          return parser->error;
        }

        recursively_delete_smt_node(parser, p->head);
        p->head = 0;

        if (!parser->incremental)
        {
          boolector_assert(parser->bzla, exp);
          boolector_release(parser->bzla, exp);
        }
        else
          smt_parser_inc_add_release_sat(parser, res, exp);

        parser->formulas.handled++;

        break;

      case BZLA_SMTOK_EXTRASORTS:
        return perr_smt(parser, "':extrasorts' unsupported");

      default: break;
    }
  CONTINUE:
    for (;;)
    {
      node    = q->head;
      q->head = 0;
      recursively_delete_smt_node(parser, node);
      if (q == p) break;
      q = cdr(q);
    }
  }

  if (parser->required_logic == BZLA_LOGIC_QF_AUFBV
      && res->logic == BZLA_LOGIC_QF_BV)
  {
    if (parser->incremental)
    {
      smt_message(parser,
                  1,
                  "need QF_AUFBV but only QF_BV specified in incremental mode");
      res->logic = BZLA_LOGIC_QF_AUFBV;
    }
    else
      return perr_smt(
          parser,
          "need QF_AUFBV but only QF_BV specified in non-incremental mode");
  }

  if (parser->required_logic == BZLA_LOGIC_QF_BV
      && res->logic == BZLA_LOGIC_QF_AUFBV)
  {
    smt_message(
        parser,
        1,
        "no arrays found: only need QF_BV (even though QF_AUFBV specified)");
    res->logic = BZLA_LOGIC_QF_BV;
  }

  assert(!parser->error);

  return 0;
}

static void
count_assumptions_and_formulas(BzlaSMTParser *parser, BzlaSMTNode *top)
{
  BzlaSMTNode *p, *n;
  BzlaSMTSymbol *s;

  parser->formulas.nparsed = parser->assumptions.nparsed = 0;

  for (p = top; p; p = cdr(p))
  {
    n = car(p);

    if (!isleaf(n)) continue;

    s = strip(n);

    if (s->token == BZLA_SMTOK_FORMULA) parser->formulas.nparsed++;

    if (s->token == BZLA_SMTOK_ASSUMPTION) parser->assumptions.nparsed++;
  }
}

static void
set_last_occurrence_of_symbols(BzlaSMTParser *parser, BzlaSMTNode *top)
{
  BzlaSMTNode *n, *h, *t;
  BzlaSMTSymbol *s;
  uint32_t occs = 0;

  assert(BZLA_EMPTY_STACK(parser->stack));

  BZLA_PUSH_STACK(parser->stack, top);
  while (!BZLA_EMPTY_STACK(parser->stack))
  {
    n = BZLA_POP_STACK(parser->stack);
    if (isleaf(n)) continue;

    h = car(n);
    t = cdr(n);

    if (t)
    {
      assert(!isleaf(t));
      BZLA_PUSH_STACK(parser->stack, t);
    }

    assert(h);
    if (isleaf(h))
    {
      s = strip(h);
      if (s->token == BZLA_SMTOK_IDENTIFIER)
      {
        s->last = n;
        occs++;
      }
    }
    else
      BZLA_PUSH_STACK(parser->stack, h);
  }

  smt_message(parser, 1, "found %u occurrences of symbols", occs);
}

/* Note: we need prefix in case of stdin as input (also applies to compressed
 * input files). */
static const char *
parse(BzlaSMTParser *parser,
      BzlaCharStack *prefix,
      FILE *infile,
      const char *infile_name,
      FILE *outfile,
      BzlaParseResult *res)
{
  BzlaSMTNode *node, *top, **p, **first;
  BzlaSMTToken token;
  const char *err;
  int32_t head;

  assert(!parser->parsed);
  parser->parsed = true;

  smt_message(parser, 1, "parsing SMT file %s", infile_name);

  parser->infile_name = infile_name;
  parser->nprefix     = 0;
  parser->prefix      = prefix;
  parser->infile      = infile;
  parser->outfile     = outfile;
  parser->lineno      = 1;
  parser->saved       = false;

  BZLA_CLR(res);

  res->status = BOOLECTOR_UNKNOWN;
  res->result = BOOLECTOR_UNKNOWN;

  assert(BZLA_EMPTY_STACK(parser->stack));
  assert(BZLA_EMPTY_STACK(parser->heads));

NEXT_TOKEN:

  token = nextok(parser);

  if (token == BZLA_SMTOK_LP)
  {
    head = BZLA_COUNT_STACK(parser->stack);
    BZLA_PUSH_STACK(parser->heads, head);
    goto NEXT_TOKEN;
  }

  if (token == BZLA_SMTOK_RP)
  {
    if (BZLA_EMPTY_STACK(parser->heads))
      return perr_smt(parser, "too many closing ')'");

    node = 0;
    head = BZLA_POP_STACK(parser->heads);
    assert((size_t) head <= BZLA_COUNT_STACK(parser->stack));
    first = parser->stack.start + head;
    p     = parser->stack.top;
    while (first < p) node = cons(parser, *--p, node);

    parser->stack.top = first;
    BZLA_PUSH_STACK(parser->stack, node);

    if (!BZLA_EMPTY_STACK(parser->heads)) goto NEXT_TOKEN;

    token = nextok(parser);
    if (token != BZLA_SMTOK_EOF) return perr_smt(parser, "expected EOF");

    assert(BZLA_COUNT_STACK(parser->stack) == 1);
    top = parser->stack.start[0];
    BZLA_RESET_STACK(parser->stack);

    smt_message(parser, 2, "read %llu bytes", parser->bytes);
    smt_message(parser, 2, "found %u symbols", parser->symbols);
    smt_message(parser, 2, "generated %u nodes", parser->nodes->count);

    count_assumptions_and_formulas(parser, top);

    smt_message(parser, 1, "found %d assumptions", parser->assumptions.nparsed);

    smt_message(parser, 1, "found %d formulas", parser->formulas.nparsed);

    set_last_occurrence_of_symbols(parser, top);

    err = translate_benchmark(parser, top, res);
    recursively_delete_smt_node(parser, top);

    if (err)
    {
      assert(parser->error);
      return parser->error;
    }

    smt_message(parser, 2, "found %u constants", parser->constants);

    return 0; /* DONE */
  }

  if (token == BZLA_SMTOK_ERR)
  {
    assert(parser->error);
    return parser->error;
  }

  if (token == BZLA_SMTOK_EOF) return perr_smt(parser, "unexpected EOF");

  if (BZLA_EMPTY_STACK(parser->heads)) return perr_smt(parser, "expected '('");

  assert(parser->symbol);
  BZLA_PUSH_STACK(parser->stack, leaf(parser->symbol));

  goto NEXT_TOKEN;
}

static const char *
parse_smt_parser(BzlaSMTParser *parser,
                 BzlaCharStack *prefix,
                 FILE *infile,
                 const char *infile_name,
                 FILE *outfile,
                 BzlaParseResult *res)
{
  (void) parse(parser, prefix, infile, infile_name, outfile, res);
  release_smt_internals(parser);
  return parser->error;
}

static BzlaParserAPI parsesmt_parser_api = {
    (BzlaInitParser) new_smt_parser,
    (BzlaResetParser) delete_smt_parser,
    (BzlaParse) parse_smt_parser,
};

const BzlaParserAPI *
bzla_parsesmt_parser_api()
{
  return &parsesmt_parser_api;
}
