#include "gimsatul.h"

#include <stdint.h>

#include "build.h"
#include "catch.h"
#include "clone.h"
#include "config.h"
#include "cover.h"
#include "detach.h"
#include "message.h"
#include "parse.h"
#include "ruler.h"
#include "simplify.h"
#include "solve.h"
#include "statistics.h"
#include "system.h"
#include "types.h"
#include "witness.h"

struct gimsatul
{
  int32_t max_var;
  signed char *witness;
  struct ruler *ruler;
};

extern void initialize_options(struct options *options);

const char *
gimsatul_version()
{
  return VERSION;
}

struct gimsatul *
gimsatul_init(uint32_t threads, int32_t max_var)
{
  struct options options;
  initialize_options(&options);
  options.threads           = threads;
  struct gimsatul *gimsatul = allocate_and_clear_block(sizeof(struct gimsatul));
  gimsatul->ruler           = new_ruler(max_var, &options);
  return gimsatul;
}

void
gimsatul_release(struct gimsatul *gimsatul)
{
  if (gimsatul->witness)
  {
    free(gimsatul->witness);
  }
  if (gimsatul->ruler)
  {
    delete_ruler(gimsatul->ruler);
  }
  free(gimsatul);
}

void
gimsatul_add_clauses(struct gimsatul *gimsatul,
                     int32_t variables,
                     int32_t nliterals,
                     int32_t *literals,
                     int32_t expected_clauses)
{
  struct ruler *ruler = gimsatul->ruler;
  signed char *marked = allocate_and_clear_block(variables);
  struct unsigneds clause;
  INIT(clause);
  int signed_lit = 0, added = 0;

  bool trivial = false;
  for (int32_t i = 0; i < nliterals; ++i)
  {
    signed_lit = literals[i];
    if (signed_lit)
    {
      unsigned idx = abs(signed_lit) - 1;
      assert(idx < (unsigned) variables);
      signed char sign      = (signed_lit < 0) ? -1 : 1;
      signed char mark      = marked[idx];
      unsigned unsigned_lit = 2 * idx + (sign < 0);
      if (mark == -sign)
      {
        ROG("skipping trivial clause");
        trivial = true;
      }
      else if (!mark)
      {
        PUSH(clause, unsigned_lit);
        marked[idx] = sign;
      }
      else
        assert(mark == sign);
    }
    else
    {
      added++;
      unsigned *literals = clause.begin;
      if (!ruler->inconsistent && !trivial)
      {
        const size_t size = SIZE(clause);
        assert(size <= ruler->size);
        if (!size)
        {
          assert(!ruler->inconsistent);
          ruler->inconsistent = true;
        }
        else if (size == 1)
        {
          const unsigned unit     = *clause.begin;
          const signed char value = ruler->values[unit];
          if (value < 0)
          {
            assert(!ruler->inconsistent);
            ruler->inconsistent = true;
            trace_add_empty(&ruler->trace);
          }
          else if (!value)
            assign_ruler_unit(ruler, unit);
        }
        else if (size == 2)
          new_ruler_binary_clause(ruler, literals[0], literals[1]);
        else
        {
          struct clause *large_clause =
              new_large_clause(size, literals, false, 0);
          ROGCLAUSE(large_clause, "new");
          PUSH(ruler->clauses, large_clause);
        }
      }
      else
        trivial = false;
      for (all_elements_on_stack(unsigned, unsigned_lit, clause))
        marked[IDX(unsigned_lit)] = 0;
      CLEAR(clause);
    }
  }
  assert(expected_clauses == added);
  RELEASE(clause);
  free(marked);
}

int32_t
gimsatul_solve(struct gimsatul *gimsatul)
{
  struct ruler *ruler = gimsatul->ruler;
  simplify_ruler(ruler);
  clone_rings(ruler);
  struct ring *winner = solve_rings(ruler);
  int32_t res         = winner ? winner->status : 0;
  if (res == 10)
  {
    gimsatul->witness = extend_witness(winner);
  }
  detach_and_delete_rings(ruler);
  return res;
}

int32_t
gimsatul_value(struct gimsatul *gimsatul, int32_t literal)
{
  assert(gimsatul->witness);
  int32_t idx = LIT(abs(literal) - 1);
  return literal * gimsatul->witness[idx];
}
