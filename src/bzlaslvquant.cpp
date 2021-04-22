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
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
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

//#define QLOG

#ifdef QLOG

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
  BzlaNode *skolemize(BzlaNode *q);
  BzlaNode *get_skolemization_lemma(BzlaNode *q);
  BzlaNode *get_ce_lemma(BzlaNode *q);
  BzlaNode *get_ce_literal(BzlaNode *q);

  BzlaNode *instantiate(BzlaNode *q, const NodeMap<BzlaNode *> &substs);

  void add_lemma(BzlaNode *lem);
  void add_value_instantiation_lemma(BzlaNode *q);

  bool added_new_lemmas() const;

  void reset_assumptions();
  void pop_assumption();
  void assume(BzlaNode *n);
  void save_assumptions();

  void get_fun_model(BzlaNode *sk_fun,
                     std::vector<BzlaBitVectorTuple *> &values_in,
                     std::vector<BzlaBitVector *> &values_out);
  void synthesize_terms();
  void store_synthesized_term(BzlaNode *sk, BzlaNode *term);

  void print_statistics() const;
  void print_time_statistics() const;

  struct
  {
    uint64_t num_ground_checks            = 0;
    uint64_t num_ground_checks_iterations = 0;
    uint64_t num_counterexample_checks    = 0;

    double time_check_sat             = 0;
    double time_check_ground          = 0;
    double time_synthesize_terms      = 0;
    double time_check_counterexamples = 0;
    double time_get_active            = 0;
  } d_statistics;

 private:
  Bzla *d_bzla;

  /* Contains currently active quantifiers (populatd by
   * get_active_quantifiers). The mapped bool indicates the current polarity of
   * the quantifier. */
  NodeSet d_active_quantifiers;

  NodeMap<bool> d_quantifiers;

  // TODO: check if reset is needed in case of incremental
  NodeSet d_inactive_quantifiers;

  NodeMap<std::vector<BzlaNode *>> d_deps;
  NodeMap<BzlaNode *> d_backrefs;

  /* Maps quantifier to introduced skolem. */
  NodeMap<BzlaNode *> d_skolems;

  /* Stores all Skolem UFs for which we can use synthesis.
   * Currently supported are bit-vector UFs, but not FP. */
  NodeSet d_use_synth;

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
  /* Maps Skolem constant/function to synthesized term. */
  NodeMap<BzlaNode *> d_synthesized_terms;

  bool d_added_lemma;

  /* Assumption stack */
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

  for (auto [sk, t] : d_synthesized_terms)
  {
    bzla_node_release(d_bzla, t);
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
    /* If simp is not in assumptions it already got removed in a previous
     * iteration. */
    if (bzla_hashptr_table_get(d_bzla->assumptions, simp))
    {
      bzla_hashptr_table_remove(d_bzla->assumptions, simp, 0, 0);
      bzla_node_release(d_bzla, simp);
    }
    bzla_node_release(d_bzla, n);
  }
  d_assumptions.clear();
}

void
QuantSolverState::pop_assumption()
{
  BzlaNode *n = d_assumptions.back();
  d_assumptions.pop_back();


  assert(bzla_hashptr_table_get(d_bzla->orig_assumptions, n));
  bzla_hashptr_table_remove(d_bzla->orig_assumptions, n, 0, 0);

  BzlaNode *simp = bzla_simplify_exp(d_bzla, n);
  assert(bzla_hashptr_table_get(d_bzla->assumptions, simp));
  bzla_hashptr_table_remove(d_bzla->assumptions, simp, 0, 0);
  bzla_node_release(d_bzla, n);
  bzla_node_release(d_bzla, simp);
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
  uint32_t i;
  BzlaBitVector *value;
  BzlaNode *cur;
  BzlaPtrHashTableIterator it;
  BzlaNodeIterator nit;
  std::vector<BzlaNode *> visit;
  BzlaMemMgr *mm;
  NodeSet cache;

  mm = d_bzla->mm;

  /* collect all reachable function equalities */
  bzla_iter_hashptr_init(&it, d_bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, d_bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    visit.push_back(static_cast<BzlaNode *>(bzla_iter_hashptr_next(&it)));
  }

  d_active_quantifiers.clear();
  d_quantifiers.clear();

  qlog("Active quantifiers:\n");
  while (!visit.empty())
  {
    cur = bzla_node_real_addr(visit.back());
    visit.pop_back();

    if (cache.find(cur) != cache.end() || !cur->quantifier_below) continue;

    cache.emplace(cur);

    if (bzla_node_is_quantifier(cur))
    {
      assert(d_active_quantifiers.find(cur) == d_active_quantifiers.end());
      value = bzla_model_get_bv_assignment(d_bzla, cur);
      assert(value);
      bool phase = bzla_bv_is_true(value);
      bzla_bv_free(mm, value);
      d_active_quantifiers.emplace(cur);
      qlog("  %s (%s) (instance: %s)\n",
           bzla_util_node2string(cur),
           phase ? "true" : "false",
           bzla_util_node2string(find_backref(cur)));

      /* Determine polarity of each active quantifier. */
      do
      {
        bzla_iter_binder_init(&nit, cur);
        while (bzla_iter_binder_has_next(&nit))
        {
          d_quantifiers.emplace(bzla_iter_binder_next(&nit), phase);
        }
        cur = bzla_node_binder_get_body(cur);
        if (bzla_node_is_inverted(cur) && bzla_node_is_forall(cur))
        {
          phase = !phase;
        }
        cur = bzla_node_real_addr(cur);
      } while (bzla_node_is_quantifier(cur));
    }
    else
    {
      for (i = 0; i < cur->arity; ++i)
      {
        visit.push_back(cur->e[i]);
      }
    }
  }
}

bool
QuantSolverState::is_forall(BzlaNode *q)
{
  q = bzla_node_real_addr(q);

  auto it = d_quantifiers.find(q);
  if (it == d_quantifiers.end())
  {
    return false;
  }
  return it->second;
}

bool
QuantSolverState::is_exists(BzlaNode *q)
{
  q = bzla_node_real_addr(q);

  auto it = d_quantifiers.find(q);
  if (it == d_quantifiers.end())
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
      else if (bzla_node_is_fp_to_fp_from_sbv(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_sbv(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_ubv(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_ubv(
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
  qlog("Inst constant %s for %s\n",
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

    /* Collect sorts of universal variable dependencies. */
    for (auto cur : deps)
    {
      if (bzla_node_is_param(cur))
      {
        assert(is_exists(find_backref(bzla_node_param_get_binder(cur))));
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

        qlog("Use skolem UF (%s): %s (%s)\n",
             bzla_util_node2string(sk),
             bzla_util_node2string(q),
             bzla_util_node2string(backref));
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

        qlog("New skolem UF (%s): %s (%s)\n",
             bzla_util_node2string(sk),
             bzla_util_node2string(q),
             bzla_util_node2string(backref));

        /* We currently only support synthesis for bit-vectors sorts, but not
         * FP sorts. Therefore, we have to check if the sorts for this function
         * are bit-vector only. */
        bool can_synth = bzla_sort_is_bv(d_bzla, codomain);
        if (can_synth)
        {
          for (BzlaSortId s : sorts)
          {
            if (!bzla_sort_is_bv(d_bzla, s))
            {
              can_synth = false;
              break;
            }
          }
        }

        if (can_synth)
        {
          d_use_synth.insert(sk);
        }
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
QuantSolverState::skolemize(BzlaNode *q)
{
  assert(bzla_node_is_regular(q));
  assert(bzla_node_is_forall(q));

  BzlaNode *cur, *sk, *inst;
  BzlaNodeIterator it;
  NodeMap<BzlaNode *> map;

  qlog("Skolemize %s\n", bzla_util_node2string(q));
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

  return inst;
}

BzlaNode *
QuantSolverState::get_skolemization_lemma(BzlaNode *q)
{
  assert(bzla_node_is_regular(q));
  assert(!q->parameterized);

  BzlaNode *inst, *lemma;

  auto it = d_skolemization_lemmas.find(q);
  if (it != d_skolemization_lemmas.end())
  {
    return it->second;
  }
  qlog("Add skolemization lemma: %s\n", bzla_util_node2string(q));

  inst  = skolemize(q);
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

  qlog("Add CE lemma: %s (%s)\n---\n",
       bzla_util_node2string(q),
       bzla_util_node2string(find_backref(q)));

  /* Get instantiations constants for variables in q. */
  bzla_iter_binder_init(&it, q);
  while (bzla_iter_binder_has_next(&it))
  {
    cur = bzla_iter_binder_next(&it);
    ic  = get_inst_constant(cur);
    map.emplace(cur->e[0], ic);
  }

  inst = instantiate(q, map);
  assert(!bzla_node_real_addr(inst)->parameterized);

  // TODO: add option to enable/disable skolemization in CE
  if (bzla_node_is_inverted(inst) && bzla_node_is_forall(inst))
  {
    BzlaNode *inst_skolemized = skolemize(bzla_node_real_addr(inst));
    bzla_node_release(d_bzla, inst);
    inst = bzla_node_invert(inst_skolemized);
  }

  lem = bzla_exp_implies(d_bzla, get_ce_literal(q), bzla_node_invert(inst));
  bzla_node_release(d_bzla, inst);
  d_ce_lemmas.emplace(bzla_node_copy(d_bzla, q), lem);

  qlog("---\n");

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

  // TODO: add option to enable/disable skolemization in CE
  if (bzla_node_is_inverted(inst) && bzla_node_is_forall(inst))
  {
    BzlaNode *inst_skolemized = skolemize(bzla_node_real_addr(inst));
    bzla_node_release(d_bzla, inst);
    inst = bzla_node_invert(inst_skolemized);
  }

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
QuantSolverState::get_fun_model(BzlaNode *sk_fun,
                                std::vector<BzlaBitVectorTuple *> &values_in,
                                std::vector<BzlaBitVector *> &values_out)
{
  size_t i;
  const BzlaBitVector *bv;
  BzlaArgsIterator it;
  BzlaBitVectorTuple *bvtup;
  BzlaNode *arg;

  /* Only collect model values relevant to synthesizing a term for sk_fun,
   * i.e., from Skolems introduced via value instantiation (from
   * counterexamples). */
  for (auto [q, sk] : d_skolems)
  {
    if (bzla_node_is_apply(sk) && sk->e[0] == sk_fun)
    {
      i = 0;

      bool relevant = true;
      bzla_iter_args_init(&it, sk->e[1]);
      while (bzla_iter_args_has_next(&it))
      {
        arg = bzla_iter_args_next(&it);
        if (!bzla_node_is_bv_const(arg))
        {
          relevant = false;
        }
      }
      if (!relevant) continue;

      bvtup = bzla_bv_new_tuple(d_bzla->mm,
                                bzla_node_fun_get_arity(d_bzla, sk_fun));
      bzla_iter_args_init(&it, sk->e[1]);
      qlog("  in:");
      while (bzla_iter_args_has_next(&it))
      {
        arg = bzla_iter_args_next(&it);
        bv  = bzla_model_get_bv(d_bzla, arg);
        bzla_bv_add_to_tuple(d_bzla->mm, bvtup, bv, i++);
#ifdef QLOG
        qlog(" ");
        bzla_bv_print_without_new_line(bv);
#endif
      }
      values_in.push_back(bvtup);

      bv = bzla_model_get_bv(d_bzla, sk);
      values_out.push_back(bzla_bv_copy(d_bzla->mm, bv));
#ifdef QLOG
      qlog("\n");
      qlog("  out: ");
      bzla_bv_print(bv);
#endif
    }
  }
}

void
QuantSolverState::synthesize_terms()
{
  std::vector<BzlaNode *> quantifiers;
  BzlaNode *prev_f;

  d_bzla->slv->api.generate_model(d_bzla->slv, false, false);
  for (auto [q, sk] : d_skolems)
  {
    BzlaNode *br = find_backref(q);

    /* We only need to synthesize for Skolem UFs / constants, but not for
     * applications on UFs. */
    if (q != br) continue;

    /* Synthesis not supported for this Skolem UF. */
    if (d_use_synth.find(sk) == d_use_synth.end())
    {
      continue;
    }

    prev_f       = nullptr;
    auto it_prev = d_synthesized_terms.find(sk);
    if (it_prev != d_synthesized_terms.end())
    {
      prev_f = it_prev->second;
    }

    /**
     * Synthesize Skolem function.
     *
     * Uses enumerative syntax-guided synthesis to synthesize a Skolem function
     * based on concrete input/output pairs. The input/output pairs are
     * constructed from the current model of the Skolem UF `sk`.
     */
    if (bzla_node_is_fun(sk))
    {
      qlog("Synthesize term for %s\n", bzla_util_node2string(sk));
      std::vector<BzlaBitVectorTuple *> values_in;
      std::vector<BzlaBitVector *> values_out;
      std::vector<BzlaNode *> params;

      get_fun_model(sk, values_in, values_out);

      // const BzlaPtrHashTable *m = bzla_model_get_fun(d_bzla, sk);
      if (values_in.empty())
      {
        qlog("  no model, skip\n");
        continue;
      }

      BzlaIntHashTable *value_in_map = bzla_hashint_map_new(d_bzla->mm);

      if (prev_f)
      {
        // TODO: add params of prev_f to value_in_map so that we can pass
        // prev_f to bzla_synthesize_term.
      }

      BzlaSortId domain =
          bzla_sort_fun_get_domain(d_bzla, bzla_node_get_sort_id(sk));
      BzlaNode *param;
      BzlaSortId sort;
      BzlaTupleSortIterator sit;
      bzla_iter_tuple_sort_init(&sit, d_bzla, domain);
      while (bzla_iter_tuple_sort_has_next(&sit))
      {
        sort  = bzla_iter_tuple_sort_next(&sit);
        param = bzla_node_create_param(d_bzla, sort, 0);
        bzla_hashint_map_add(value_in_map, param->id)->as_int = params.size();
        params.push_back(param);
      }

      BzlaNode *t = bzla_synthesize_term(d_bzla,
                                         params.data(),
                                         params.size(),
                                         values_in.data(),
                                         values_out.data(),
                                         values_in.size(),
                                         value_in_map,
                                         nullptr,
                                         0,
                                         nullptr,  // BzlaNode **consts,
                                         0,  // uint32_t nconsts,
                                         10000, // max checks
                                         5,     // max levels
                                         nullptr);  // BzlaNode *prev_synth)

      for (BzlaBitVectorTuple *bvtup : values_in)
      {
        bzla_bv_free_tuple(d_bzla->mm, bvtup);
      }
      for (BzlaBitVector *bv : values_out)
      {
        bzla_bv_free(d_bzla->mm, bv);
      }

      // Create new candidate function with synthesized term `t`.
      if (t)
      {
        BzlaNode *f = bzla_exp_fun(d_bzla, params.data(), params.size(), t);
        bzla_node_release(d_bzla, t);

#ifdef QLOG
        bzla_dumpsmt_dump_node(d_bzla, stdout, f, 0);
#endif

        store_synthesized_term(sk, f);
        bzla_node_release(d_bzla, f);
      }
      // Was not able to synthesize a candidate term for current input/output
      // pairs. Delete previously synthesized function since it does not have
      // the expected input/output behavior for Skolem UF `sk`.
      else if (prev_f)
      {
        store_synthesized_term(sk, nullptr);
      }

      for (BzlaNode *p : params)
      {
        bzla_node_release(d_bzla, p);
      }

      bzla_hashint_map_delete(value_in_map);
    }
    /* Use current model value for Skolem constants. */
    else
    {
      qlog("Use model value for %s\n", bzla_util_node2string(sk));
      const BzlaBitVector *bv = bzla_model_get_bv(d_bzla, sk);
      BzlaNode *value;
      if (bzla_node_is_fp(d_bzla, sk))
      {
        BzlaFloatingPoint *fp_value =
            bzla_fp_from_bv(d_bzla, bzla_node_get_sort_id(sk), bv);
        value = bzla_node_create_fp_const(d_bzla, fp_value);
        bzla_fp_free(d_bzla, fp_value);
      }
      // TODO: rounding mode values
      else
      {
        assert(bzla_node_is_bv(d_bzla, sk));
        value = bzla_exp_bv_const(d_bzla, bv);
      }

      store_synthesized_term(sk, value);
      bzla_node_release(d_bzla, value);
    }
  }
}

void
QuantSolverState::store_synthesized_term(BzlaNode *sk, BzlaNode *term)
{
  auto it = d_synthesized_terms.find(sk);

  if (it == d_synthesized_terms.end())
  {
    d_synthesized_terms.emplace(sk, bzla_node_copy(d_bzla, term));
  }
  else
  {
    /* Delete synthesized term for sk. */
    if (term == nullptr)
    {
      bzla_node_release(d_bzla, it->second);
      d_synthesized_terms.erase(it);
      return;
    }
    /* Term is the same, do nothing. */
    if (it->second == term)
    {
      return;
    }
    /* Otherwise, delete old term and store new one. */
    bzla_node_release(d_bzla, it->second);
    it->second = bzla_node_copy(d_bzla, term);
  }
}

bool
QuantSolverState::check_active_quantifiers()
{
  bool done = false;
  double start;
  BzlaNode *lit;
  BzlaSolverResult res;
  std::vector<BzlaNode *> to_check, to_synth, model_assumptions, lemmas;

  d_added_lemma = false;
  start         = bzla_util_time_stamp();
  get_active_quantifiers();
  for (BzlaNode *q : d_active_quantifiers)
  {
    if (is_forall(q))
    {
      if (!is_inactive(q))
      {
        // lemmas.push_back(get_ce_lemma(q));
        add_lemma(get_ce_lemma(q));
        to_check.push_back(q);
      }
    }
    else
    {
      assert(is_exists(q));
      // lemmas.push_back(get_skolemization_lemma(q));
      add_lemma(get_skolemization_lemma(q));
    }
  }
  d_statistics.time_get_active += bzla_util_time_stamp() - start;

  /* Synthesize functions for Skolem UFs and assume candidate model.  For
   * skolem constants the current model value is used. */
  start = bzla_util_time_stamp();
  synthesize_terms();
  d_statistics.time_synthesize_terms += bzla_util_time_stamp() - start;

  for (auto [sk, model_candidate] : d_synthesized_terms)
  {
    BzlaNode *eq = bzla_exp_eq(d_bzla, sk, model_candidate);
    assume(eq);
    model_assumptions.push_back(eq);
  }

#ifdef QLOG
  printf("\n");
  bzla_dumpsmt_dump(d_bzla, stdout);
#endif

  assert(d_bzla->slv->api.sat(d_bzla->slv) == BZLA_RESULT_SAT);

  /* Check for counterexamples under current candidate model. */
  start               = bzla_util_time_stamp();
  size_t num_inactive = 0;
  for (BzlaNode *q : to_check)
  {
    ++d_statistics.num_counterexample_checks;

    lit = get_ce_literal(q);

    assume(lit);

    // printf("\n");
    // bzla_dumpsmt_dump(d_bzla, stdout);
    qlog("Check for counterexamples (%s): ", bzla_util_node2string(q));

    res = d_bzla->slv->api.sat(d_bzla->slv);

    if (res == BZLA_RESULT_SAT)
    {
      qlog("sat\n");

      // d_bzla->slv->api.generate_model(d_bzla->slv, false, false);
      // d_bzla->slv->api.print_model(d_bzla->slv, "smt2", stdout);
      add_value_instantiation_lemma(q);
    }
    else
    {
      qlog("unsat\n");
      if (bzla_failed_exp(d_bzla, lit))
      {
        ++num_inactive;
        set_inactive(q);
      }
    }

    pop_assumption();
  }
  done = num_inactive == to_check.size();

  // TODO: can be removed if assumptions released via reset_assumptions
  for (BzlaNode *n : model_assumptions)
  {
    bzla_node_release(d_bzla, n);
  }
  reset_assumptions();

  for (BzlaNode *lem : lemmas)
  {
    add_lemma(lem);
  }

  d_statistics.time_check_counterexamples += bzla_util_time_stamp() - start;

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

    qlog("Dependencies for %s (%s):\n",
         bzla_util_node2string(q),
         bzla_util_node2string(q->e[0]));

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
  double start;

  if (d_bzla->inconsistent)
  {
    qlog("Ground formulas inconsistent\n");
    return BZLA_RESULT_UNSAT;
  }

  start = bzla_util_time_stamp();
  ++d_statistics.num_ground_checks;

  for (auto [q, lit] : d_ce_literals)
  {
    if (is_inactive(q)) continue;
    assumptions.emplace(lit, q);
  }

  i = 0;
  while (true)
  {
    ++d_statistics.num_ground_checks_iterations;
    ++i;
    qlog("\nGround check: %zu (%zu assumptions): ", i, assumptions.size());

    for (auto &p : assumptions)
    {
      assume(p.first);
    }

#ifdef QLOG
    printf("\n");
    bzla_dumpsmt_dump(d_bzla, stdout);
#endif

    res = d_bzla->slv->api.sat(d_bzla->slv);

    if (res == BZLA_RESULT_SAT)
    {
      qlog("sat\n");

#ifdef QLOG
      for (auto [q, sk] : d_skolems)
      {
        if (sk->arity == 0 && !bzla_hashptr_table_get(d_bzla->inputs, sk))
        {
          bzla_hashptr_table_add(d_bzla->inputs, bzla_node_copy(d_bzla, sk));
        }
      }
      for (auto [q, ic] : d_instantiation_constants)
      {
        if (!bzla_hashptr_table_get(d_bzla->inputs, ic))
        {
          bzla_hashptr_table_add(d_bzla->inputs, bzla_node_copy(d_bzla, ic));
        }
      }
      d_bzla->slv->api.generate_model(d_bzla->slv, false, false);
      d_bzla->slv->api.print_model(d_bzla->slv, "smt2", stdout);
#endif

      reset_assumptions();
      break;
    }
    else
    {
      qlog("unsat\n");

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
  d_statistics.time_check_ground += bzla_util_time_stamp() - start;
  return res;
}

void
QuantSolverState::print_statistics() const
{
  BZLA_MSG(d_bzla->msg, 1, "");
  BZLA_MSG(d_bzla->msg, 1, "quantifier statistics:");
  BZLA_MSG(
      d_bzla->msg, 1, "  %zu ground checks", d_statistics.num_ground_checks);
  BZLA_MSG(d_bzla->msg,
           1,
           "  %zu ground check iterations",
           d_statistics.num_ground_checks_iterations);
  BZLA_MSG(d_bzla->msg,
           1,
           "  %zu CE checks",
           d_statistics.num_counterexample_checks);
}

void
QuantSolverState::print_time_statistics() const
{
  BZLA_MSG(d_bzla->msg, 1, "");
  BZLA_MSG(d_bzla->msg, 1, "quantifier time statistics:");
  BZLA_MSG(
      d_bzla->msg, 1, "  %.1f seconds check-sat", d_statistics.time_check_sat);
  BZLA_MSG(d_bzla->msg,
           1,
           "    %.1f seconds ground checks",
           d_statistics.time_check_ground);
  BZLA_MSG(d_bzla->msg, 1, "    %.1f get active", d_statistics.time_get_active);
  BZLA_MSG(d_bzla->msg,
           1,
           "    %.1f seconds synthesize terms",
           d_statistics.time_synthesize_terms);
  BZLA_MSG(d_bzla->msg,
           1,
           "    %.1f seconds CE checks",
           d_statistics.time_check_counterexamples);
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
  double start;
  BzlaSolverResult res;

  // debug
  bzla_opt_set(slv->bzla, BZLA_OPT_PRETTY_PRINT, 0);

  start                   = bzla_util_time_stamp();
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

  state.d_statistics.time_check_sat += bzla_util_time_stamp() - start;

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
  slv->d_state->print_statistics();
}

static void
print_time_stats_quant_solver(BzlaQuantSolver *slv)
{
  slv->d_state->print_time_statistics();
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
