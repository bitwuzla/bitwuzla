/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLA_QUEUE_H_INCLUDED
#define BZLA_QUEUE_H_INCLUDED

#include <assert.h>

#include "utils/bzlamem.h"

#define BZLA_DECLARE_QUEUE(name, type)    \
  typedef struct name##Queue name##Queue; \
  struct name##Queue                      \
  {                                       \
    BzlaMemMgr* mm;                       \
    type* start;                          \
    type* head;                           \
    type* tail;                           \
    type* end;                            \
  }

#define BZLA_INIT_QUEUE(mem, queue) \
  do                                \
  {                                 \
    (queue).mm    = mem;            \
    (queue).start = 0;              \
    (queue).head  = 0;              \
    (queue).tail  = 0;              \
    (queue).end   = 0;              \
  } while (0)

#define BZLA_COUNT_QUEUE(queue) \
  (assert((queue).mm), (size_t)((queue).tail - (queue).head))
#define BZLA_EMPTY_QUEUE(queue) \
  (assert((queue).mm), (queue).tail == (queue).head)

#define BZLA_RESET_QUEUE(queue)                  \
  do                                             \
  {                                              \
    assert((queue).mm);                          \
    (queue).head = (queue).tail = (queue).start; \
  } while (0)

#define BZLA_SIZE_QUEUE(queue) \
  (assert((queue).mm), (size_t)((queue).end - (queue).start))
#define BZLA_FULL_QUEUE(queue) (assert((queue).mm), (queue).tail == (queue).end)

#define BZLA_RELEASE_QUEUE(queue)                                      \
  do                                                                   \
  {                                                                    \
    assert((queue).mm);                                                \
    BZLA_DELETEN((queue).mm, (queue).start, BZLA_SIZE_QUEUE((queue))); \
    BZLA_INIT_QUEUE((queue).mm, queue);                                \
  } while (0)

#define BZLA_ENLARGE_QUEUE(queue)                                \
  do                                                             \
  {                                                              \
    assert((queue).mm);                                          \
    uint32_t old_size     = BZLA_SIZE_QUEUE(queue), new_size;    \
    uint32_t old_tail_pos = (queue).tail - (queue).start;        \
    uint32_t old_head_pos = (queue).head - (queue).start;        \
    BZLA_ENLARGE((queue).mm, (queue).start, old_size, new_size); \
    (queue).tail = (queue).start + old_tail_pos;                 \
    (queue).head = (queue).start + old_head_pos;                 \
    (queue).end  = (queue).start + new_size;                     \
  } while (0)

#define BZLA_MOVE_QUEUE(queue)                                           \
  do                                                                     \
  {                                                                      \
    assert((queue).mm);                                                  \
    uint32_t offset = (queue).head - (queue).start;                      \
    uint32_t count  = BZLA_COUNT_QUEUE((queue));                         \
    memmove((queue).start, (queue).head, count * sizeof *(queue).start); \
    (queue).head = (queue).start;                                        \
    (queue).tail -= offset;                                              \
  } while (0)

#define BZLA_ENQUEUE(queue, elem)                               \
  do                                                            \
  {                                                             \
    assert((queue).mm);                                         \
    if (BZLA_FULL_QUEUE((queue)))                               \
    {                                                           \
      if (2 * BZLA_COUNT_QUEUE(queue) < BZLA_SIZE_QUEUE(queue)) \
        BZLA_MOVE_QUEUE((queue));                               \
      else                                                      \
        BZLA_ENLARGE_QUEUE((queue));                            \
    }                                                           \
    assert((queue).tail < (queue).end);                         \
    *(queue).tail++ = (elem);                                   \
  } while (0)

#define BZLA_DEQUEUE(queue) (assert((queue).mm), *(queue).head++)

BZLA_DECLARE_QUEUE(BzlaInt, int32_t);

#endif
