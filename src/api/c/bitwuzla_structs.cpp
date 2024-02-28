#include "api/c/bitwuzla_structs.h"

#include <cassert>

const bitwuzla::Sort&
BitwuzlaTermManager::import_sort(BitwuzlaSort sort)
{
  return sort->d_sort;
}

const bitwuzla::Term&
BitwuzlaTermManager::import_term(BitwuzlaTerm term)
{
  return term->d_term;
}

BitwuzlaSort
BitwuzlaTermManager::export_sort(const bitwuzla::Sort& sort)
{
  assert(!sort.is_null());

  auto [it, inserted] = d_alloc_sorts.try_emplace(sort, sort, this);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

BitwuzlaTerm
BitwuzlaTermManager::export_term(const bitwuzla::Term& term)
{
  assert(!term.is_null());

  auto [it, inserted] = d_alloc_terms.try_emplace(term, term, this);
  if (!inserted)
  {
    copy(&it->second);
  }
  return &it->second;
}

void
BitwuzlaTermManager::release(bitwuzla_term_t* term)
{
  --term->d_refs;
  if (term->d_refs == 0)
  {
    assert(d_alloc_terms.find(term->d_term) != d_alloc_terms.end());
    d_alloc_terms.erase(term->d_term);
  }
}

bitwuzla_term_t*
BitwuzlaTermManager::copy(bitwuzla_term_t* term)
{
  ++term->d_refs;
  return term;
}

void
BitwuzlaTermManager::release(bitwuzla_sort_t* sort)
{
  --sort->d_refs;
  if (sort->d_refs == 0)
  {
    assert(d_alloc_sorts.find(sort->d_sort) != d_alloc_sorts.end());
    d_alloc_sorts.erase(sort->d_sort);
  }
}

bitwuzla_sort_t*
BitwuzlaTermManager::copy(bitwuzla_sort_t* sort)
{
  ++sort->d_refs;
  return sort;
}

void
BitwuzlaTermManager::release()
{
  d_alloc_sorts.clear();
  d_alloc_terms.clear();
}
