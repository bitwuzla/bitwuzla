#include "api/c/bitwuzla_structs.h"

#include <cassert>

const bitwuzla::Sort&
BitwuzlaTermManager::import_sort(BitwuzlaSort sort)
{
  return *sort->d_sort.get();
}

const bitwuzla::Term&
BitwuzlaTermManager::import_term(BitwuzlaTerm term)
{
  return *term->d_term.get();
}

BitwuzlaTermManager::BitwuzlaTermManager() : d_tm(new bitwuzla::TermManager())
{
  d_term_mgr_needs_delete = true;
}

BitwuzlaTermManager::BitwuzlaTermManager(bitwuzla::TermManager& tm) : d_tm(&tm)
{
}

BitwuzlaTermManager::~BitwuzlaTermManager()
{
  d_alloc_sorts.clear();
  d_alloc_terms.clear();
  if (d_term_mgr_needs_delete)
  {
    delete d_tm;
  }
}

BitwuzlaSort
BitwuzlaTermManager::export_sort(const bitwuzla::Sort& sort)
{
  assert(!sort.is_null());
  BitwuzlaSort s =
      new bitwuzla_sort_t{std::make_unique<bitwuzla::Sort>(sort), this};
  d_alloc_sorts.emplace_back(s);
  return s;
}

BitwuzlaTerm
BitwuzlaTermManager::export_term(const bitwuzla::Term& term)
{
  assert(!term.is_null());
  BitwuzlaTerm t =
      new bitwuzla_term_t{std::make_unique<bitwuzla::Term>(term), this};
  d_alloc_terms.emplace_back(t);
  return t;
}
