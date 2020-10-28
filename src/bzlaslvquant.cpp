/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

extern "C" {
#include "bzlaslvquant.h"

#include "bzlabeta.h"
#include "bzlabv.h"
#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlamodel.h"
#include "bzlaprintmodel.h"
#include "bzlaslvfun.h"
#include "bzlasynth.h"
#include "dumper/bzladumpsmt.h"
#include "utils/bzlaabort.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"
}

#include <cstdarg>
#include <memory>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

/*------------------------------------------------------------------------*/

template <typename T>
using NodeMap = std::unordered_map<BzlaNode *, T>;
using NodeSet = std::unordered_set<BzlaNode *>;

/*------------------------------------------------------------------------*/

#if 1

static void
qlog(const char *fmt, ...)
{
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stdout, fmt, ap);
  fflush(stdout);
  va_end(ap);
}

#else

#define qlog(...)        \
  while (false)          \
  {                      \
    printf(__VA_ARGS__); \
  }

#endif

/*------------------------------------------------------------------------*/
/* Solver State                                                           */
/*------------------------------------------------------------------------*/

class QuantSolverState
{
 public:
  QuantSolverState(Bzla *bzla) : d_bzla(bzla){};
  ~QuantSolverState();

  void get_active_quantifiers();
  bool is_forall(BzlaNode *q);
  bool is_exists(BzlaNode *q);
  bool check_active_quantifiers();
  BzlaSolverResult check_ground_formulas();

  void set_inactive(BzlaNode *q);
  bool is_inactive(BzlaNode *q);

  void add_instance(BzlaNode *q,
                    BzlaNode *qi,
                    const NodeMap<BzlaNode *> &substs);

  void compute_variable_dependencies_aux(BzlaNode *q,
                                         std::vector<BzlaNode *> &free_vars);
  void compute_variable_dependencies();

  BzlaNode *find_backref(BzlaNode *q);
  void add_backref(BzlaNode *qfrom, BzlaNode *qto);

  BzlaNode *get_skolem(BzlaNode *q);
  BzlaNode *mk_skolem(BzlaNode *q, const char *sym);

  BzlaNode *get_inst_constant(BzlaNode *q);
  BzlaNode *get_skolemization_lemma(BzlaNode *q);
  BzlaNode *get_ce_lemma(BzlaNode *q);
  BzlaNode *get_ce_literal(BzlaNode *q);

  BzlaNode *instantiate(BzlaNode *q, const NodeMap<BzlaNode *> &substs);

  void add_lemma(BzlaNode *lem);
  void add_value_instantiation_lemma(BzlaNode *q);

  bool added_new_lemmas() const;

  void reset_assumptions();
  void assume(BzlaNode *n);
  void save_assumptions();

 private:
  Bzla *d_bzla;

  /* Contains currently active quantifiers (populatd by
   * get_active_quantifiers). The mapped bool indicates the current polarity of
   * the quantifier. */
  NodeMap<bool> d_active_quantifiers;
  NodeSet d_inactive_quantifiers;

  NodeMap<std::vector<BzlaNode *>> d_deps;
  NodeMap<BzlaNode *> d_backrefs;

  /* Maps quantifier to introduced skolem. */
  NodeMap<BzlaNode *> d_skolems;
  /* Maps quantifier to instantiation constant. */
  NodeMap<BzlaNode *> d_instantiation_constants;
  /* Cache for added skolemization lemmas. */
  NodeMap<BzlaNode *> d_skolemization_lemmas;
  /* Cache for CE lemmas. */
  NodeMap<BzlaNode *> d_ce_lemmas;
  /* Cache for CE literals. */
  NodeMap<BzlaNode *> d_ce_literals;
  /* Cache of added lemmas. */
  NodeSet d_lemma_cache;

  bool d_added_lemma;

  std::vector<BzlaNode *> d_assumptions;
};

QuantSolverState::~QuantSolverState()
{
  for (BzlaNode *q : d_inactive_quantifiers)
  {
    bzla_node_release(d_bzla, q);
  }

  for (auto &p : d_deps)
  {
    bzla_node_release(d_bzla, p.first);
    for (BzlaNode *n : p.second)
    {
      bzla_node_release(d_bzla, n);
    }
  }

  for (auto [qi, q] : d_backrefs)
  {
    bzla_node_release(d_bzla, qi);
    bzla_node_release(d_bzla, q);
  }

  for (auto [q, s] : d_skolems)
  {
    bzla_node_release(d_bzla, q);
    bzla_node_release(d_bzla, s);
  }

  for (auto [q, c] : d_instantiation_constants)
  {
    bzla_node_release(d_bzla, q);
    bzla_node_release(d_bzla, c);
  }

  for (auto [q, l] : d_skolemization_lemmas)
  {
    bzla_node_release(d_bzla, q);
    bzla_node_release(d_bzla, l);
  }

  for (auto [q, l] : d_ce_lemmas)
  {
    bzla_node_release(d_bzla, q);
    bzla_node_release(d_bzla, l);
  }

  for (auto [q, l] : d_ce_literals)
  {
    bzla_node_release(d_bzla, q);
    bzla_node_release(d_bzla, l);
  }

  for (BzlaNode *l : d_lemma_cache)
  {
    bzla_node_release(d_bzla, l);
  }
}

/*------------------------------------------------------------------------*/

struct BzlaQuantSolver
{
  BZLA_SOLVER_STRUCT;

  std::unique_ptr<QuantSolverState> d_state;
};

/*------------------------------------------------------------------------*/

void
QuantSolverState::reset_assumptions()
{
  BzlaNode *simp;
  for (BzlaNode *n : d_assumptions)
  {
    // qlog("reset assume: %s\n", bzla_util_node2string(n));
    assert(bzla_hashptr_table_get(d_bzla->orig_assumptions, n));
    bzla_hashptr_table_remove(d_bzla->orig_assumptions, n, 0, 0);

    simp = bzla_simplify_exp(d_bzla, n);
    assert(bzla_hashptr_table_get(d_bzla->assumptions, simp));
    bzla_hashptr_table_remove(d_bzla->assumptions, simp, 0, 0);
    bzla_node_release(d_bzla, n);
    bzla_node_release(d_bzla, simp);
  }
  d_assumptions.clear();

  bzla_reset_functions_with_model(d_bzla);
}

void
QuantSolverState::assume(BzlaNode *n)
{
  // qlog("assume: %s\n", bzla_util_node2string(n));
  bzla_assume_exp(d_bzla, n);
  d_assumptions.push_back(n);
}

BzlaNode *
QuantSolverState::find_backref(BzlaNode *q)
{
  auto it = d_backrefs.find(q);
  while (it != d_backrefs.end())
  {
    q  = it->second;
    it = d_backrefs.find(q);
  }
  return q;
}

void
QuantSolverState::add_backref(BzlaNode *qfrom, BzlaNode *qto)
{
  BzlaNode *backref = find_backref(qto);

  auto it = d_backrefs.find(qfrom);
  if (it != d_backrefs.end())
  {
    assert(it->second == backref);
  }
  else
  {
    d_backrefs.emplace(bzla_node_copy(d_bzla, qfrom),
                       bzla_node_copy(d_bzla, backref));
    //    log ("::: %s -> %s\n", bzla_util_node2string(qfrom),
    //    bzla_util_node2string(qto));
  }
}

void
QuantSolverState::get_active_quantifiers()
{
  double start, delta;
  uint32_t i;
  BzlaBitVector *value;
  BzlaNode *cur;
  BzlaPtrHashTableIterator it;
  std::vector<BzlaNode *> visit;
  BzlaMemMgr *mm;
  NodeSet cache;

  start = bzla_util_time_stamp();
  mm    = d_bzla->mm;

  /* collect all reachable function equalities */
  bzla_iter_hashptr_init(&it, d_bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, d_bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    visit.push_back(static_cast<BzlaNode *>(bzla_iter_hashptr_next(&it)));
  }

  d_active_quantifiers.clear();

  qlog("Active quantifiers:\n");
  while (!visit.empty())
  {
    cur = bzla_node_real_addr(visit.back());
    visit.pop_back();

    if (cache.find(cur) != cache.end() || !cur->quantifier_below) continue;

    cache.emplace(cur);

    // TODO: check if this is required
    assert(bzla_node_is_synth(cur));

    if (bzla_node_is_quantifier(cur))
    {
      if (d_inactive_quantifiers.find(cur) == d_inactive_quantifiers.end())
      {
        assert(d_active_quantifiers.find(cur) == d_active_quantifiers.end());
        value = bzla_model_get_bv_assignment(d_bzla, cur);
        assert(value);
        bool phase = bzla_bv_is_true(value);
        bzla_bv_free(mm, value);
        d_active_quantifiers.emplace(cur, phase);
        qlog("  %s (%s) (instance: %s)\n",
             bzla_util_node2string(cur),
             phase ? "true" : "false",
             bzla_util_node2string(find_backref(cur)));
      }
    }
    else
    {
      for (i = 0; i < cur->arity; ++i)
      {
        visit.push_back(cur->e[i]);
      }
    }
  }
  delta = bzla_util_time_stamp() - start;
}

bool
QuantSolverState::is_forall(BzlaNode *q)
{
  q = bzla_node_real_addr(q);

  auto it = d_active_quantifiers.find(q);
  if (it == d_active_quantifiers.end())
  {
    return false;
  }
  return it->second;
}

bool
QuantSolverState::is_exists(BzlaNode *q)
{
  q = bzla_node_real_addr(q);

  auto it = d_active_quantifiers.find(q);
  if (it == d_active_quantifiers.end())
  {
    return false;
  }
  return !it->second;
}

static BzlaNode *
substitute(Bzla *bzla,
           BzlaNode *n,
           const NodeMap<BzlaNode *> &substs,
           NodeMap<BzlaNode *> &backref)
{
  assert(bzla);
  assert(n);

  uint32_t i;
  BzlaNode *cur, *real_cur, *subst, *result, *e[4], *c;
  std::vector<BzlaNode *> visit;
  NodeMap<BzlaNode *> cache;

  visit.push_back(n);
  while (!visit.empty())
  {
    cur      = visit.back();
    real_cur = bzla_node_real_addr(cur);
    visit.pop_back();

    auto it = cache.find(real_cur);
    if (it == cache.end())
    {
      auto itt = substs.find(real_cur);
      if (itt != substs.end())
      {
        subst = itt->second;
        cache.emplace(real_cur, bzla_node_copy(bzla, subst));

        /* Keep track of instantiated variables */
        if (bzla_node_is_param(real_cur)
            && bzla_node_param_is_forall_var(real_cur))
        {
          backref.emplace(real_cur, bzla_node_copy(bzla, subst));
          // printf ("backref: %s -> %s\n", bzla_util_node2string(real_cur),
          // bzla_util_node2string(subst));
        }
        continue;
      }
      cache.emplace(real_cur, nullptr);

      visit.push_back(cur);
      for (i = 0; i < real_cur->arity; ++i)
      {
        visit.push_back(real_cur->e[i]);
      }
    }
    else if (it->second == nullptr)
    {
      for (i = 0; i < real_cur->arity; ++i)
      {
        c = bzla_node_real_addr(real_cur->e[i]);
        assert(cache.find(c) != cache.end());
        e[i] = bzla_node_cond_invert(real_cur->e[i], cache.at(c));
      }

      if (real_cur->arity == 0)
      {
        if (bzla_node_is_param(real_cur))
        {
          result = bzla_node_mk_param_with_unique_symbol(bzla, real_cur);
        }
        else
        {
          result = bzla_node_copy(bzla, real_cur);
        }
      }
      else if (bzla_node_is_bv_slice(real_cur))
      {
        result = bzla_exp_bv_slice(bzla,
                                   e[0],
                                   bzla_node_bv_slice_get_upper(real_cur),
                                   bzla_node_bv_slice_get_lower(real_cur));
      }
      else if (bzla_node_is_fp_to_sbv(real_cur))
      {
        result = bzla_exp_fp_to_sbv(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_ubv(real_cur))
      {
        result = bzla_exp_fp_to_ubv(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_bv(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_bv(
            bzla, e[0], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_fp(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_fp(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_int(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_int(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_uint(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_uint(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else
      {
        /* if the param of a quantifier gets subtituted by a non-param,
         * we do not create a quantifier, but return the body instead */
        if (bzla_node_is_quantifier(real_cur) && !bzla_node_is_param(e[0]))
        {
          result = bzla_node_copy(bzla, e[1]);
        }
        else
        {
          result = bzla_exp_create(bzla, real_cur->kind, e, real_cur->arity);

          if (bzla_node_is_quantifier(real_cur)
              && bzla_node_is_quantifier(result))
          {
            backref.emplace(real_cur, bzla_node_copy(bzla, result));
          }
        }
      }
      assert(bzla_node_get_sort_id(real_cur) == bzla_node_get_sort_id(result));

      if (bzla_node_is_param(real_cur)
          && bzla_node_param_is_forall_var(real_cur))
      {
        backref.emplace(real_cur, bzla_node_copy(bzla, result));
      }

      it->second = result;
    }
  }
  assert(cache.find(bzla_node_real_addr(n)) != cache.end());

  result = bzla_node_cond_invert(
      n, bzla_node_copy(bzla, cache.at(bzla_node_real_addr(n))));

  for (auto &p : cache)
  {
    bzla_node_release(bzla, p.second);
  }
  return result;
}

void
QuantSolverState::add_instance(BzlaNode *q,
                               BzlaNode *qi,
                               const NodeMap<BzlaNode *> &substs)
{
  if (q == qi)
  {
    return;
  }

  if (d_deps.find(qi) != d_deps.end())
  {
    // TODO: check if we need to do anything here
    // log("******* already added\n");
    return;
  }
  assert(d_deps.find(q) != d_deps.end());

  qlog("Add new instance: %s\n", bzla_util_node2string(qi));

  auto &qdeps = d_deps.at(q);
  std::vector<BzlaNode *> qideps;
  for (auto cur : qdeps)
  {
    auto it = substs.find(cur);
    if (it != substs.end())
    {
      qideps.push_back(bzla_node_copy(d_bzla, it->second));
      qlog("  dep: %s -> %s\n",
           bzla_util_node2string(cur),
           bzla_util_node2string(it->second));
    }
    else
    {
      qideps.push_back(bzla_node_copy(d_bzla, cur));
      qlog("  dep: %s\n", bzla_util_node2string(cur));
    }
  }
  d_deps.emplace(bzla_node_copy(d_bzla, qi), qideps);
}

BzlaNode *
QuantSolverState::instantiate(BzlaNode *q, const NodeMap<BzlaNode *> &substs)
{
  assert(bzla_node_is_quantifier(q));

  NodeMap<BzlaNode *> backref;
  BzlaNode *result;

  result = substitute(d_bzla, q, substs, backref);

  for (auto [q, qi] : backref)
  {
    if (bzla_node_is_quantifier(q))
    {
      add_backref(qi, q);
      add_instance(q, qi, backref);
    }
    bzla_node_release(d_bzla, qi);
  }

  return result;
}

BzlaNode *
QuantSolverState::get_inst_constant(BzlaNode *q)
{
  BzlaNode *sk;
  BzlaSortId sort;

  auto it = d_instantiation_constants.find(q);
  if (it != d_instantiation_constants.end())
  {
    return it->second;
  }

  std::stringstream ss;
  char *sym = bzla_node_get_symbol(d_bzla, q->e[0]);
  if (sym)
  {
    ss << "ic(" << sym << ")";
  }
  sort = bzla_node_get_sort_id(q->e[0]);
  sk   = bzla_node_create_var(d_bzla, sort, ss.str().c_str());
  qlog("inst contant %s for %s\n",
       bzla_util_node2string(sk),
       bzla_util_node2string(q));

  d_instantiation_constants.emplace(bzla_node_copy(d_bzla, q), sk);

  return sk;
}

BzlaNode *
QuantSolverState::mk_skolem(BzlaNode *q, const char *sym)
{
  BzlaNode *result = 0, *backref, *sk;
  BzlaSortId domain, codomain, sort;

  auto it = d_deps.find(q);
  if (it != d_deps.end())
  {
    std::vector<BzlaSortId> sorts;
    std::vector<BzlaNode *> args;
    std::vector<BzlaNode *> &deps = it->second;

    qlog("# SKOLEM UF: %s\n", bzla_util_node2string(q));

    /* Collect sorts of universal variable dependencies. */
    for (auto cur : deps)
    {
      if (bzla_node_is_param(cur))
      {
        assert(is_exists(bzla_node_param_get_binder(cur)));
      }
      else
      {
        qlog("  %s\n", bzla_util_node2string(cur));
        sorts.push_back(bzla_node_get_sort_id(cur));
        args.push_back(cur);
      }
    }

    if (!sorts.empty())
    {
      backref = find_backref(q);
      auto it = d_skolems.find(backref);
      if (it != d_skolems.end())
      {
        sk = it->second;
      }
      else
      {
        domain   = bzla_sort_tuple(d_bzla, sorts.data(), sorts.size());
        codomain = bzla_node_get_sort_id(q->e[0]);
        sort     = bzla_sort_fun(d_bzla, domain, codomain);
        sk       = bzla_exp_uf(d_bzla, sort, sym);
        bzla_sort_release(d_bzla, domain);
        bzla_sort_release(d_bzla, sort);
        d_skolems.emplace(bzla_node_copy(d_bzla, backref), sk);
      }
      assert(args.size() == bzla_node_fun_get_arity(d_bzla, sk));
      result = bzla_exp_apply_n(d_bzla, sk, args.data(), args.size());
    }
  }

  if (!result)
  {
    result = bzla_node_create_var(d_bzla, bzla_node_get_sort_id(q->e[0]), sym);
  }

  return result;
}

BzlaNode *
QuantSolverState::get_skolem(BzlaNode *q)
{
  BzlaNode *sk;

  auto it = d_skolems.find(q);
  if (it != d_skolems.end())
  {
    return it->second;
  }

  std::stringstream ss;

  char *sym = bzla_node_get_symbol(d_bzla, q->e[0]);
  if (sym)
  {
    ss << "sk(" << sym << ")";
  }
  sk = mk_skolem(q, ss.str().c_str());

  qlog("New skolem %s for %s\n",
       bzla_util_node2string(sk),
       bzla_util_node2string(q));
  d_skolems.emplace(bzla_node_copy(d_bzla, q), sk);

  return sk;
}

BzlaNode *
QuantSolverState::get_ce_literal(BzlaNode *q)
{
  BzlaNode *lit;
  BzlaSortId sort;

  auto it = d_ce_literals.find(q);
  if (it != d_ce_literals.end())
  {
    return it->second;
  }

  sort = bzla_sort_bool(d_bzla);

  std::stringstream ss;
  ss << "celit(" << bzla_node_get_id(q) << ")";
  lit = bzla_node_create_var(d_bzla, sort, ss.str().c_str());
  d_ce_literals.emplace(bzla_node_copy(d_bzla, q), lit);
  bzla_sort_release(d_bzla, sort);

  return lit;
}

BzlaNode *
QuantSolverState::get_skolemization_lemma(BzlaNode *q)
{
  assert(bzla_node_is_regular(q));
  assert(!q->parameterized);

  BzlaNode *cur, *sk, *inst, *lemma;
  BzlaNodeIterator it;
  NodeMap<BzlaNode *> map;

  auto itt = d_skolemization_lemmas.find(q);
  if (itt != d_skolemization_lemmas.end())
  {
    return itt->second;
  }
  qlog("Add skolemization lemma: %s\n", bzla_util_node2string(q));

  bzla_iter_binder_init(&it, q);
  while (bzla_iter_binder_has_next(&it))
  {
    cur = bzla_iter_binder_next(&it);
    sk  = get_skolem(cur);
    map.emplace(cur->e[0], sk);
    qlog("  %s -> %s\n",
         bzla_util_node2string(cur->e[0]),
         bzla_util_node2string(sk));
  }

  inst = instantiate(q, map);
  assert(!bzla_node_real_addr(inst)->parameterized);

  lemma = bzla_exp_implies(d_bzla, bzla_node_invert(q), bzla_node_invert(inst));
  bzla_node_release(d_bzla, inst);
  d_skolemization_lemmas.emplace(bzla_node_copy(d_bzla, q), lemma);
  return lemma;
}

BzlaNode *
QuantSolverState::get_ce_lemma(BzlaNode *q)
{
  assert(bzla_node_is_regular(q));
  assert(!q->parameterized);

  BzlaNode *cur, *ic, *inst, *lem;
  BzlaNodeIterator it;
  NodeMap<BzlaNode *> map;

  auto itt = d_ce_lemmas.find(q);
  if (itt != d_ce_lemmas.end())
  {
    return itt->second;
  }

  qlog("Add CE lemma: %s (%s)\n",
       bzla_util_node2string(q),
       bzla_util_node2string(find_backref(q)));

  /* Get instantiations constants for variables in q. */
  bzla_iter_binder_init(&it, q);
  while (bzla_iter_binder_has_next(&it))
  {
    cur = bzla_iter_binder_next(&it);
    ic  = get_inst_constant(cur);
    map.emplace(cur->e[0], ic);
    qlog("map inst contant %s for %s\n",
         bzla_util_node2string(ic),
         bzla_util_node2string(cur->e[0]));
  }

  inst = instantiate(q, map);
  assert(!bzla_node_real_addr(inst)->parameterized);
  lem = bzla_exp_implies(d_bzla, get_ce_literal(q), bzla_node_invert(inst));
  bzla_node_release(d_bzla, inst);
  d_ce_lemmas.emplace(bzla_node_copy(d_bzla, q), lem);

  return lem;
}

BzlaNode *
get_value(Bzla *bzla, BzlaNode *n)
{
  BzlaFloatingPoint *fp_value;
  BzlaBitVector *bv_value;
  BzlaNode *value = 0;

  bv_value = bzla_model_get_bv_assignment(bzla, n);
  if (bzla_node_is_bv(bzla, n))
  {
    value = bzla_exp_bv_const(bzla, bv_value);
  }
  else if (bzla_node_is_fp(bzla, n))
  {
    fp_value = bzla_fp_from_bv(bzla, bzla_node_get_sort_id(n), bv_value);
    value    = bzla_exp_fp_const_fp(bzla, fp_value);
    bzla_fp_free(bzla, fp_value);
  }
  assert(value);
  bzla_bv_free(bzla->mm, bv_value);
  return value;
}

void
QuantSolverState::add_lemma(BzlaNode *lem)
{
  auto it = d_lemma_cache.find(lem);
  if (it != d_lemma_cache.end())
  {
    // log ("Duplicate lemma: %s\n", bzla_util_node2string (lem));
    return;
  }
  // log ("Add lemma: %s\n", bzla_util_node2string(lem));
  bzla_assert_exp(d_bzla, lem);
  d_lemma_cache.insert(bzla_node_copy(d_bzla, lem));
  d_added_lemma = true;
}

void
QuantSolverState::add_value_instantiation_lemma(BzlaNode *q)
{
  assert(bzla_node_is_regular(q));
  assert(!q->parameterized);

  BzlaNode *cur, *ic, *inst, *lem, *value;
  BzlaNodeIterator it;
  NodeMap<BzlaNode *> map;

  qlog("Add value instantiation: %s\n", bzla_util_node2string(q));
  /* Collect model values for instantiation constants of q. */
  bzla_iter_binder_init(&it, q);
  while (bzla_iter_binder_has_next(&it))
  {
    cur   = bzla_iter_binder_next(&it);
    ic    = get_inst_constant(cur);
    value = get_value(d_bzla, ic);
    map.emplace(cur->e[0], value);
    qlog("  %s -> %s\n",
         bzla_util_node2string(cur->e[0]),
         bzla_util_node2string(value));
  }

  inst = instantiate(q, map);
  assert(!bzla_node_real_addr(inst)->parameterized);

  for (auto &p : map)
  {
    bzla_node_release(d_bzla, p.second);
  }

  lem = bzla_exp_implies(d_bzla, q, inst);
  bzla_node_release(d_bzla, inst);
  add_lemma(lem);
  bzla_node_release(d_bzla, lem);
}

bool
QuantSolverState::added_new_lemmas() const
{
  return d_added_lemma;
}

void
QuantSolverState::set_inactive(BzlaNode *q)
{
  assert(d_inactive_quantifiers.find(q) == d_inactive_quantifiers.end());
  d_inactive_quantifiers.emplace(bzla_node_copy(d_bzla, q));
  qlog("Set inactive: %s\n", bzla_util_node2string(q));
}

bool
QuantSolverState::is_inactive(BzlaNode *q)
{
  return d_inactive_quantifiers.find(q) != d_inactive_quantifiers.end();
}

void
get_model(QuantSolverState *state, BzlaNode *q)
{
  //  bzla              = state->bzla;
  //  BzlaNode *backref = state->find_backref (q);
  //  b                 = bzla_hashptr_table_get (state->skolems, backref);
  //  assert (b);
}

bool
QuantSolverState::check_active_quantifiers()
{
  bool done = false;
  BzlaNode *q, *lit;
  BzlaSolverResult res;
  std::vector<BzlaNode *> to_check, to_synth;

  d_added_lemma = false;
  get_active_quantifiers();
  for (auto &p : d_active_quantifiers)
  {
    q = p.first;
    if (is_forall(q))
    {
      if (!is_inactive(q))
      {
        add_lemma(get_ce_lemma(q));
        to_check.push_back(q);
      }
    }
    else
    {
      assert(is_exists(q));
      to_synth.push_back(q);
      add_lemma(get_skolemization_lemma(q));
    }
  }

#if 0
  for (size_t i = 0, size = BZLA_COUNT_STACK (to_synth); i < size; ++i)
  {
    q = BZLA_PEEK_STACK (to_synth, i);
    get_model (state, q);
  }
#endif

  size_t num_inactive = 0;
  for (BzlaNode *q : to_check)
  {
    lit = get_ce_literal(q);

    assume(lit);

    qlog("Check for counterexamples (%s): ", bzla_util_node2string(q));

    res = d_bzla->slv->api.sat(d_bzla->slv);

    if (res == BZLA_RESULT_SAT)
    {
      qlog("sat\n");
      add_value_instantiation_lemma(q);
    }
    else
    {
      qlog("unsat\n");
      d_bzla->last_sat_result = BZLA_RESULT_UNSAT;  // hack
      if (bzla_failed_exp(d_bzla, lit))
      {
        ++num_inactive;
        set_inactive(q);
      }
    }

    reset_assumptions();
  }
  done = num_inactive == to_check.size();

  return done;
}

void
QuantSolverState::compute_variable_dependencies_aux(
    BzlaNode *q, std::vector<BzlaNode *> &free_vars)
{
  BzlaNode *cur;
  std::vector<BzlaNode *> visit;
  NodeSet cache;

  visit.push_back(q);
  while (!visit.empty())
  {
    cur = bzla_node_real_addr(visit.back());
    visit.pop_back();

    if (!cur->parameterized || cache.find(cur) != cache.end())
    {
      continue;
    }
    cache.emplace(cur);

    if (bzla_node_is_quantifier(cur))
    {
      cache.emplace(cur->e[0]);
    }
    else if (bzla_node_is_param(cur) && bzla_node_param_is_forall_var(cur))
    {
      free_vars.push_back(bzla_node_copy(d_bzla, cur));
      qlog("  %s\n", bzla_util_node2string(cur));
    }

    for (uint32_t i = 0; i < cur->arity; ++i)
    {
      visit.push_back(cur->e[i]);
    }
  }
}

void
QuantSolverState::compute_variable_dependencies()
{
  BzlaNode *q;
  BzlaPtrHashTableIterator it;

  bzla_iter_hashptr_init(&it, d_bzla->quantifiers);
  while (bzla_iter_hashptr_has_next(&it))
  {
    q = static_cast<BzlaNode *>(bzla_iter_hashptr_next(&it));
    if (!q->parameterized)
    {
      qlog("skip: %s\n", bzla_util_node2string(q));
      continue;
    }
    if (d_deps.find(q) != d_deps.end()) continue;

    qlog("Dependencies for %s:\n", bzla_util_node2string(q));

    std::vector<BzlaNode *> free_vars;
    compute_variable_dependencies_aux(q, free_vars);
    assert(free_vars.size() > 0);
    d_deps.emplace(bzla_node_copy(d_bzla, q), free_vars);
  }
}

BzlaSolverResult
QuantSolverState::check_ground_formulas()
{
  BzlaSolverResult res;
  NodeMap<BzlaNode *> assumptions;
  BzlaNode *q, *lit;
  size_t i;

  if (d_bzla->inconsistent)
  {
    qlog("Ground formulas inconsistent\n");
    return BZLA_RESULT_UNSAT;
  }

  for (auto [q, lit] : d_ce_literals)
  {
    if (is_inactive(q)) continue;
    assumptions.emplace(lit, q);
  }

  i = 0;
  while (true)
  {
    ++i;
    qlog("\nGround check: %zu (%u assumptions): ", i, assumptions.size());

    for (auto &p : assumptions)
    {
      assume(p.first);
    }

    res = d_bzla->slv->api.sat(d_bzla->slv);

    if (res == BZLA_RESULT_SAT)
    {
      qlog("sat\n");
      reset_assumptions();
      break;
    }
    else
    {
      qlog("unsat\n");
      d_bzla->last_sat_result = BZLA_RESULT_UNSAT;  // hack

      bool failed = false;
      /* Remove failed assumptions. */
      for (auto it = assumptions.begin(); it != assumptions.end();)
      {
        lit = it->first;
        q   = it->second;
        if (bzla_failed_exp(d_bzla, lit))
        {
          qlog("  failed: %s (instance: %s)\n",
               bzla_util_node2string(q),
               bzla_util_node2string(find_backref(q)));
          failed = true;
          it     = assumptions.erase(it);
        }
        else
        {
          ++it;
        }
      }

      reset_assumptions();

      if (!failed)
      {
        break;
      }
    }
  }
  return res;
}

///////////////////////////////////////////////////////////////////////////////

static BzlaSolverResult
check_sat_quant_solver(BzlaQuantSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_QUANT_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->qslv == (BzlaSolver *) slv);

  bool done;
  BzlaSolverResult res;

  QuantSolverState &state = *slv->d_state.get();

  state.compute_variable_dependencies();

  while (true)
  {
    res = state.check_ground_formulas();
    if (res == BZLA_RESULT_SAT)
    {
      qlog("\n");
      done = state.check_active_quantifiers();
      if (!state.added_new_lemmas())
      {
        if (done)
        {
          qlog("** No new counterexamples found, all quantifiers inactive\n");
          res = BZLA_RESULT_SAT;
        }
        else
        {
          qlog("** No new lemmas added\n");
          res = BZLA_RESULT_UNKNOWN;
        }
        break;
      }
    }
    else
    {
      res = BZLA_RESULT_UNSAT;
      break;
    }
  }

  return res;
}

static BzlaQuantSolver *
clone_quant_solver(Bzla *clone, Bzla *bzla, BzlaNodeMap *exp_map)
{
  (void) clone;
  (void) bzla;
  (void) exp_map;
  return 0;
}

static void
delete_quant_solver(BzlaQuantSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_QUANT_SOLVER_KIND);
  assert(slv->bzla);

  Bzla *bzla;

  bzla = slv->bzla;
  delete slv;
  bzla->slv = 0;
}

static void
generate_model_quant_solver(BzlaQuantSolver *slv,
                            bool model_for_all_nodes,
                            bool reset)
{
  (void) slv;
  (void) model_for_all_nodes;
  (void) reset;
}

static void
print_stats_quant_solver(BzlaQuantSolver *slv)
{
  (void) slv;
}

static void
print_time_stats_quant_solver(BzlaQuantSolver *slv)
{
  (void) slv;
}

static void
print_model_quant_solver(BzlaQuantSolver *slv, const char *format, FILE *file)
{
  (void) slv;
  (void) format;
  (void) file;
}

BzlaSolver *
bzla_new_quantifier_solver(Bzla *bzla)
{
  assert(bzla);

  BzlaQuantSolver *slv = new BzlaQuantSolver();
  slv->d_state.reset(new QuantSolverState(bzla));

  slv->kind      = BZLA_QUANT_SOLVER_KIND;
  slv->bzla      = bzla;
  slv->api.clone = (BzlaSolverClone) clone_quant_solver;
  slv->api.delet = (BzlaSolverDelete) delete_quant_solver;
  slv->api.sat   = (BzlaSolverSat) check_sat_quant_solver;
  slv->api.generate_model =
      (BzlaSolverGenerateModel) generate_model_quant_solver;
  slv->api.print_stats = (BzlaSolverPrintStats) print_stats_quant_solver;
  slv->api.print_time_stats =
      (BzlaSolverPrintTimeStats) print_time_stats_quant_solver;
  slv->api.print_model = (BzlaSolverPrintModel) print_model_quant_solver;

  BZLA_MSG(bzla->msg, 1, "enabled quant engine");

  return (BzlaSolver *) slv;
}
