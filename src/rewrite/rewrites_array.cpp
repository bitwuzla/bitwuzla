/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node_manager.h"
#include "node/node_utils.h"
#include "rewrite/rewrite_utils.h"
#include "rewrite/rewrites_bool.h"

namespace bzla {

using namespace node;

/**
 * Propagate selects over store chains.
 */
template <>
Node
RewriteRule<RewriteRuleKind::ARRAY_PROP_SELECT>::_apply(Rewriter& rewriter,
                                                        const Node& node)
{
  if (!node[1].is_value())
  {
    return node;
  }

  ConstNodeRef array = node[0];
  while (true)
  {
    const Node& store = array;

    if (store.kind() != Kind::STORE || !store[1].is_value())
    {
      if (node[0] != store)
      {
        return rewriter.mk_node(Kind::SELECT, {store, node[1]});
      }
      break;
    }

    if (store[1] == node[1])
    {
      return store[2];
    }

    // Propagate down
    assert(store[1].is_value());
    array = store[0];
  }
  return node;
}

}  // namespace bzla
