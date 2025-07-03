/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "util/hash.h"

namespace bzla::util::hash {
uint64_t
fnv1a_64(uint64_t v, uint64_t hash)
{
  hash ^= v;
  // Compute (hash * 1099511628211)
  return hash + (hash << 1) + (hash << 4) + (hash << 5) + (hash << 7)
         + (hash << 8) + (hash << 40);
}
}  // namespace bzla::util::hash

size_t
std::hash<std::pair<uint64_t, uint64_t>>::operator()(
    const std::pair<uint64_t, uint64_t>& p) const
{
  uint64_t hash = bzla::util::hash::fnv1a_64(std::hash<uint64_t>()(p.first));
  return static_cast<size_t>(
      bzla::util::hash::fnv1a_64(std::hash<uint64_t>()(p.second), hash));
}
