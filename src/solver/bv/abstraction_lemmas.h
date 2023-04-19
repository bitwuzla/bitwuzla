#ifndef BZLA_SOLVER_BV_ABSTRACTION_LEMMAS_H_INCLUDED
#define BZLA_SOLVER_BV_ABSTRACTION_LEMMAS_H_INCLUDED

#include <ostream>

#include "solver/solver_state.h"

namespace bzla::bv::abstraction {

enum class LemmaKind
{
  MUL_ZERO,   // (=> (= s #b0000) (= t #b0000))
  MUL_ONE,    // (=> (= s #b0001) (= t x))
  MUL_IC,     // (= (bvand (bvor (bvneg s) s) t) t),
  MUL_NEG,    // (=> (= s (bvnot #b0000)) (= t (bvneg x)))
  MUL_ODD,    // (= t (bvor t (bvand x (bvand s #b0001))))
  MUL_REF1,   // (not (= s (bvnot (bvor t (bvand #b0001 (bvor x s))))))
  MUL_REF2,   // (bvuge s (bvand t (bvneg (bvor t (bvnot x)))))
  MUL_REF3,   // (not (= (bvand x t) (bvor s (bvnot t))))
  MUL_REF4,   // (not (= #b0001 (bvnot (bvand x (bvand s t)))))
  MUL_REF5,   // (not (= t (bvnot (bvor t (bvor #b0001 (bvand x s))))))
  MUL_REF6,   // (bvuge s (bvshl (bvlshr t x) #b0001))
  MUL_REF7,   // (= x (bvshl x (bvand s (bvlshr #b0001 t))))
  MUL_REF8,   // (bvuge x (bvlshr (bvneg t) (bvnot s)))
  MUL_REF9,   // (bvuge x (bvshl x (bvnot (bvlshr s t))))
  MUL_REF10,  // (bvuge x (bvlshr t (bvnot (bvneg s))))
  MUL_REF11,  // (not (= x (bvshl #b0001 (bvshl x (bvlshr s t)))))
  MUL_REF12,  // (not (= x (bvnot (bvshl x (bvadd s t)))))
  MUL_REF13,  // (not (= t (bvor #b0001 (bvadd x s))))
  MUL_REF14,  // (not (= t (bvor #b0001 (bvnot (bvxor x s)))))
  MUL_REF15,  // (not (= t (bvor (bvnot #b0001) (bvxor x s))))
  MUL_REF16,  // (not (= x (bvadd #b0001 (bvshl x (bvsub t s)))))
  MUL_REF17,  // (not (= x (bvadd #b0001 (bvshl x (bvsub s t)))))
  MUL_REF18,  // (not (= x (bvsub #b0001 (bvshl x (bvsub s t)))))
  MUL_VALUE,  // value instantiation lemma
};

std::ostream& operator<<(std::ostream& os, LemmaKind kind);

/* --- Abstraction Lemmas --------------------------------------------------- */

class AbstractionLemma
{
 public:
  AbstractionLemma(LemmaKind kind, bool commutative = true)
      : d_kind(kind), d_commutative(commutative){};

  /** Return lemma kind. */
  LemmaKind kind() const { return d_kind; }

  bool commutative() const { return d_commutative; };

  /** Get instance of abstraction lemma. */
  virtual Node instance(const Node& x, const Node& s, const Node& t) const = 0;

 protected:
  LemmaKind d_kind;
  bool d_commutative;
};

template <enum LemmaKind K>
class Lemma : public AbstractionLemma
{
 public:
  Lemma<K>() : AbstractionLemma(K){};
  Node instance(const Node& x, const Node& s, const Node& t) const override;
};

template <>
Node Lemma<LemmaKind::MUL_ZERO>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::MUL_ONE>::instance(const Node& x,
                                         const Node& s,
                                         const Node& t) const;

template <>
Node Lemma<LemmaKind::MUL_IC>::instance(const Node& x,
                                        const Node& s,
                                        const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_NEG>::instance(const Node& x,
                                         const Node& s,
                                         const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_ODD>::instance(const Node& x,
                                         const Node& s,
                                         const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF1>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF2>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF3>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF4>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF5>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF6>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF7>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF8>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF9>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF10>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF11>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF12>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF13>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF14>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF15>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF16>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF17>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;
template <>
Node Lemma<LemmaKind::MUL_REF18>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

}  // namespace bzla::bv::abstraction

#endif
