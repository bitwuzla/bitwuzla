#include "util/hash_pair.h"

namespace {
/**
 * FNV-1a hash algorithm for 64-bit numbers.
 * See http://www.isthe.com/chongo/tech/comp/fnv/index.html
 */
uint64_t
fnv1a_64(uint64_t v, uint64_t hash = 14695981039346656037u)
{
  hash ^= v;
  // Compute (hash * 1099511628211)
  return hash + (hash << 1) + (hash << 4) + (hash << 5) + (hash << 7)
         + (hash << 8) + (hash << 40);
}
}  // namespace

size_t
std::hash<std::pair<uint64_t, uint64_t>>::operator()(
    const std::pair<uint64_t, uint64_t>& p) const
{
  uint64_t hash = fnv1a_64(std::hash<uint64_t>()(p.first));
  return static_cast<size_t>(fnv1a_64(std::hash<uint64_t>()(p.second), hash));
}
