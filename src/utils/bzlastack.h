/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLA_STACK_H_INCLUDED
#define BZLA_STACK_H_INCLUDED

#include <assert.h>
#include <stdlib.h>

#include "utils/bzlamem.h"

#define BZLA_DECLARE_STACK(name, type)    \
  typedef struct name##Stack name##Stack; \
  struct name##Stack                      \
  {                                       \
    BzlaMemMgr *mm;                       \
    type *start;                          \
    type *top;                            \
    type *end;                            \
  }

#define BZLA_INIT_STACK(mem, stack) \
  do                                \
  {                                 \
    (stack).mm    = mem;            \
    (stack).start = 0;              \
    (stack).top   = 0;              \
    (stack).end   = 0;              \
  } while (0)

#define BZLA_COUNT_STACK(stack) \
  (assert((stack).mm), (size_t)((stack).top - (stack).start))

#define BZLA_EMPTY_STACK(stack) \
  (assert((stack).mm), (stack).top == (stack).start)

#define BZLA_RESET_STACK(stack)                      \
  do                                                 \
  {                                                  \
    assert((stack).mm), (stack).top = (stack).start; \
  } while (0)

#define BZLA_SIZE_STACK(stack) \
  (assert((stack).mm), (size_t)((stack).end - (stack).start))

#define BZLA_FULL_STACK(stack) (assert((stack).mm), (stack).top == (stack).end)

#define BZLA_RELEASE_STACK(stack)                                      \
  do                                                                   \
  {                                                                    \
    assert((stack).mm);                                                \
    BZLA_DELETEN((stack).mm, (stack).start, BZLA_SIZE_STACK((stack))); \
    BZLA_INIT_STACK((stack).mm, (stack));                              \
  } while (0)

#define BZLA_ENLARGE_STACK(stack)                                \
  do                                                             \
  {                                                              \
    assert((stack).mm);                                          \
    size_t old_size  = BZLA_SIZE_STACK(stack), new_size;         \
    size_t old_count = BZLA_COUNT_STACK(stack);                  \
    BZLA_ENLARGE((stack).mm, (stack).start, old_size, new_size); \
    (stack).top = (stack).start + old_count;                     \
    (stack).end = (stack).start + new_size;                      \
  } while (0)

#define BZLA_ENLARGE_STACK_TO_SIZE(stack, new_size)              \
  do                                                             \
  {                                                              \
    assert((stack).mm);                                          \
    size_t old_size  = BZLA_SIZE_STACK(stack);                   \
    size_t old_count = BZLA_COUNT_STACK(stack);                  \
    BZLA_REALLOC((stack).mm, (stack).start, old_size, new_size); \
    (stack).top = (stack).start + old_count;                     \
    (stack).end = (stack).start + new_size;                      \
  } while (0)

/* adjust count and size of stack2 to count and size of stack1, new
 * stack elements in stack2 are cleared */
#define BZLA_ADJUST_STACK(stack1, stack2)                   \
  do                                                        \
  {                                                         \
    assert((stack1).mm);                                    \
    assert((stack2).mm);                                    \
    size_t stack1_size  = BZLA_SIZE_STACK(stack1);          \
    size_t stack2_size  = BZLA_SIZE_STACK(stack2);          \
    size_t stack1_count = BZLA_COUNT_STACK(stack1);         \
    size_t stack2_count = BZLA_COUNT_STACK(stack2);         \
    assert(stack1_size >= stack2_size);                     \
    assert(stack1_count >= stack2_count);                   \
    if (stack1_size > stack2_size)                          \
      BZLA_ENLARGE_STACK_TO_SIZE((stack2), (stack1_size));  \
    if (stack1_count > stack2_count)                        \
    {                                                       \
      memset((stack2).top, 0, stack1_count - stack2_count); \
      (stack2).top += stack1_count - stack2_count;          \
    }                                                       \
  } while (0)

#define BZLA_FIT_STACK(stack, idx)                                 \
  do                                                               \
  {                                                                \
    assert((stack).mm);                                            \
    size_t old_size = BZLA_SIZE_STACK(stack), old_count, new_size; \
    if (old_size > (size_t)(idx)) break;                           \
    old_count = BZLA_COUNT_STACK(stack);                           \
    new_size  = old_size ? 2 * old_size : 1;                       \
    while (new_size <= (size_t)(idx)) new_size *= 2;               \
    assert((new_size) > (size_t)(idx));                            \
    BZLA_REALLOC((stack).mm, (stack).start, old_size, new_size);   \
    (stack).top = (stack).start + old_count;                       \
    (stack).end = (stack).start + new_size;                        \
    BZLA_CLRN((stack).top + old_size, new_size - old_size);        \
  } while (0)

#define BZLA_PUSH_STACK(stack, elem)                           \
  do                                                           \
  {                                                            \
    assert((stack).mm);                                        \
    if (BZLA_FULL_STACK((stack))) BZLA_ENLARGE_STACK((stack)); \
    *((stack).top++) = (elem);                                 \
  } while (0)

#define BZLA_PUSH_STACK_IF(cond, stack, elem) \
  do                                          \
  {                                           \
    assert((stack).mm);                       \
    if (cond) BZLA_PUSH_STACK(stack, elem);   \
  } while (0)

#define BZLA_POP_STACK(stack) \
  (assert((stack).mm), assert(!BZLA_EMPTY_STACK(stack)), (*--(stack).top))

#define BZLA_DEQUEUE_STACK(stack, dequeued)   \
  do                                          \
  {                                           \
    typeof((stack).start[0]) *BZLA_DEQUEUE_P; \
    assert(!BZLA_EMPTY_STACK(stack));         \
  assert ((stack).mm));                       \
    (dequeued)     = (stack).start[0];        \
    BZLA_DEQUEUE_P = (stack).start;           \
    while (++BZLA_DEQUEUE_P < (stack).top)    \
      BZLA_DEQUEUE_P[-1] = BZLA_DEQUEUE_P[0]; \
    (stack).top--;                            \
  } while (0)

#define BZLA_TOP_STACK(stack) \
  (assert((stack).mm), assert(!BZLA_EMPTY_STACK(stack)), (stack).top[-1])

#define BZLA_PEEK_STACK(stack, idx)                 \
  (assert((stack).mm),                              \
   assert((size_t)(idx) < BZLA_COUNT_STACK(stack)), \
   (stack).start[idx])

#define BZLA_POKE_STACK(stack, idx, elem)            \
  do                                                 \
  {                                                  \
    assert((stack).mm);                              \
    assert((size_t)(idx) < BZLA_COUNT_STACK(stack)); \
    (stack).start[idx] = (elem);                     \
  } while (0)

BZLA_DECLARE_STACK(BzlaInt, int32_t);

BZLA_DECLARE_STACK(BzlaUInt, uint32_t);

BZLA_DECLARE_STACK(BzlaChar, char);

BZLA_DECLARE_STACK(BzlaCharPtr, char *);

BZLA_DECLARE_STACK(BzlaVoidPtr, void *);

#endif
