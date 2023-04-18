#ifndef BZLA_SOLVER_BV_ABSTRACTION_LEMMAS_H_INCLUDED
#define BZLA_SOLVER_BV_ABSTRACTION_LEMMAS_H_INCLUDED

#include <ostream>

#include "solver/solver_state.h"

namespace bzla::bv {

enum class LemmaKind
{
  MUL_ZERO,   // (=> (= s 0) (= t 0))
  MUL_ONE,    // (=> (= s 1) (= t x))
  MUL_IC,     // (= (bvand (bvor (bvneg s) s) t) t),
  MUL_VALUE,  // value instantiation lemma

  // Abstraction lemmas to add:
  //
  // (=> (= s (bvnot #b0000)) (= t (bvneg x))),
  // (not (distinct t (bvand t (bvor x (bvneg x))))),
  // (not (distinct t (bvor t (bvand x (bvand s #b0001))))),
  // (not (= s (bvnot (bvor t (bvand #b0001 (bvor x s)))))),
  // (not (= x (bvnot (bvor t (bvand #b0001 (bvor x s)))))),
  // (not (bvult s (bvand t (bvneg (bvor t (bvnot x)))))),
  // (not (= (bvand x t) (bvor s (bvnot t)))),
  // (not (bvult x (bvand t (bvneg (bvor t (bvnot s)))))),
  // (not (= #b0001 (bvnot (bvand x (bvand s t))))),
  // (not (= t (bvnot (bvor t (bvor #b0001 (bvand x s)))))),
  // (not (bvult s (bvshl (bvlshr t x) #b0001))),
  // (not (distinct x (bvshl x (bvand s (bvlshr #b0001 t)))))
  // (not (bvult x (bvlshr (bvneg t) (bvnot s)))),
  // (not (bvult x (bvshl x (bvnot (bvlshr s t))))),
  // (not (bvult x (bvlshr t (bvnot (bvneg s))))),
  // (not (= x (bvshl #b0001 (bvshl x (bvlshr s t))))),
  // (not (= x (bvnot (bvshl x (bvadd s t))))),
  // (not (= t (bvor #b0001 (bvadd x s)))),
  // (not (= t (bvor #b0001 (bvnot (bvxor x s))))),
  // (not (= t (bvor (bvnot #b0001) (bvxor x s)))),
  // (not (= x (bvadd #b0001 (bvshl x (bvsub t s))))),
  // (not (= x (bvadd #b0001 (bvshl x (bvsub s t))))),
  // (not (= x (bvsub #b0001 (bvshl x (bvsub s t)))))
};

std::ostream& operator<<(std::ostream& os, LemmaKind kind);

/* --- Abstraction Lemmas --------------------------------------------------- */

class AbstractionLemma
{
 public:
  AbstractionLemma(SolverState& state, LemmaKind kind);

  /** Return lemma kind. */
  LemmaKind kind() const { return d_kind; }

  /** Check if abstraction lemma is violated. */
  virtual bool check(const Node& x, const Node& s, const Node& t) const = 0;

  /** Get instance of abstraction lemma. */
  virtual Node instance(const Node& x, const Node& s, const Node& t) const = 0;

 protected:
  SolverState& d_solver_state;
  LemmaKind d_kind;
};

class LemmaMulZero : public AbstractionLemma
{
 public:
  LemmaMulZero(SolverState& state);
  bool check(const Node& x, const Node& s, const Node& t) const override;
  Node instance(const Node& x, const Node& s, const Node& t) const override;
};

class LemmaMulOne : public AbstractionLemma
{
 public:
  LemmaMulOne(SolverState& state);
  bool check(const Node& x, const Node& s, const Node& t) const override;
  Node instance(const Node& x, const Node& s, const Node& t) const override;
};

class LemmaMulIc : public AbstractionLemma
{
 public:
  LemmaMulIc(SolverState& state);
  bool check(const Node& x, const Node& s, const Node& t) const override;
  Node instance(const Node& x, const Node& s, const Node& t) const override;
};

class LemmaMulValue : public AbstractionLemma
{
 public:
  LemmaMulValue(SolverState& state);
  bool check(const Node& x, const Node& s, const Node& t) const override;
  Node instance(const Node& x, const Node& s, const Node& t) const override;
};

}  // namespace bzla::bv

#endif
