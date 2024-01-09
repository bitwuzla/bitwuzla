#ifndef BZLA_SOLVER_BV_ABSTRACTION_LEMMAS_H_INCLUDED
#define BZLA_SOLVER_BV_ABSTRACTION_LEMMAS_H_INCLUDED

#include <ostream>

#include "solver/solver_state.h"

namespace bzla::abstract {

enum class LemmaKind : uint32_t
{
  MUL_ZERO,    // (=> (= s #b0000) (= t #b0000))
  MUL_ONE,     // (=> (= s #b0001) (= t x))
  MUL_IC,      // (= (bvand (bvor (bvneg s) s) t) t),
  MUL_NEG,     // (=> (= s (bvnot #b0000)) (= t (bvneg x)))
  MUL_ODD,     // (= t (bvor t (bvand x (bvand s #b0001))))
  MUL_SQUARE,  // (=> (= x s) (= t (bvmul x x))), uses special encoding

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
  MUL_POW2,
  MUL_NEG_POW2,
  MUL_VALUE,

  MUL_NOOVFL_REF1,   // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (not (bvult (bvneg x) (bvor (bvneg t) (bvand x s))))
  MUL_NOOVFL_REF2,   // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge t (bvneg (bvand (bvneg x) (bvneg s)))))
  MUL_NOOVFL_REF3,   // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (= t (bvand t (bvor x (bvneg x)))))
  MUL_NOOVFL_REF4,   // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (= t (bvor t (bvand x (bvand s #b0001)))))
  MUL_NOOVFL_REF5,   // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge (bvneg s) (bvor (bvneg t) (bvand x s))))
  MUL_NOOVFL_REF6,   // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge (bvneg s) (bvneg (bvand t (bvnot s)))))
  MUL_NOOVFL_REF7,   // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge (bvneg x) (bvneg (bvand t (bvnot x)))))
  MUL_NOOVFL_REF8,   // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge #b0001 (bvand x (bvand t (bvneg (bvor x s))))))
  MUL_NOOVFL_REF9,   // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct (bvor x (bvnot (bvor t (bvand s #b0001))))))
  MUL_NOOVFL_REF10,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge (bvand t (bvneg x)) (bvand x s)))
  MUL_NOOVFL_REF11,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct s (bvnot (bvor t (bvand #b0001 (bvor x
                     //  s))))))
  MUL_NOOVFL_REF12,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct t (bvor #b0001 (bvneg (bvnot (bvor x s))))))
  MUL_NOOVFL_REF13,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge (bvneg s) (bvand x t)))
  MUL_NOOVFL_REF14,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge (bvand t (bvneg x)) (bvand s t)))
  MUL_NOOVFL_REF15,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct x (bvnot (bvor t (bvand #b0001 (bvor x
                     //  s))))))
  MUL_NOOVFL_REF16,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct x (bvor s (bvnot (bvor x (bvor t #b0001))))))
  MUL_NOOVFL_REF17,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct x (bvor s (bvnot (bvor t (bvand x
                     //  #b0001))))))
  MUL_NOOVFL_REF18,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct #b0001 (bvnot (bvand (bvneg x) (bvor x s)))))
  MUL_NOOVFL_REF19,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct #b0001 (bvor x (bvnot (bvand t (bvneg s))))))
  MUL_NOOVFL_REF20,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct #b0001 (bvnot (bvand (bvneg s) (bvor x s)))))
  MUL_NOOVFL_REF21,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge s (bvlshr t (bvnot (bvneg x)))))
  MUL_NOOVFL_REF22,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge x (bvlshr t (bvnot (bvneg s)))))
  MUL_NOOVFL_REF23,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct x (bvshl (bvnot #b0001) (bvlshr x s))))
  MUL_NOOVFL_REF24,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct x (bvadd t (bvnot (bvshl x t)))))
  MUL_NOOVFL_REF25,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct x (bvnot (bvshl x (bvadd s t)))))
  MUL_NOOVFL_REF26,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (bvuge x (bvlshr t (bvadd t (bvnot s)))))
  MUL_NOOVFL_REF27,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct t (bvor #b0001 (bvadd x s))))
  MUL_NOOVFL_REF28,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     //  (distinct #b0001 (bvor (bvnot t) (bvxor x s))))
  MUL_NOOVFL_REF29,  // (=>
                     //  (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
                     // (distinct x (bvlshr (bvsub (bvlshr x s) #b0001)
                     // #b0001)))

  UDIV_REF1,  // (=> (= s #b0001) (= t x))
  UDIV_REF2,  // (=> (and (= s x) (distinct s #b0000)) (= t #b0001))
  UDIV_REF3,  // (=> (= s #b0000) (= t (bvnot #b0000)))
  UDIV_REF4,  // (=> (and (= x #b0000) (distinct s #b0000)) (= t #b0000))
  UDIV_REF5,  // (=> (distinct s #b0000) (bvule t x))
  UDIV_REF6,  // (let ((_let_1 (bvnot #b0000)))
              //  (=> (and (= s _let_1) (distinct x _let_1)) (= t #b0000)))

  UDIV_REF7,   // (not (bvult x (bvneg (bvand (bvneg s) (bvneg t)))))
  UDIV_REF8,   // (not (bvult (bvneg (bvor s #b0001)) t))
  UDIV_REF9,   // (not (= t (bvneg (bvand s (bvnot x)))))
  UDIV_REF10,  // (not (= (bvor s t) (bvand x (bvnot #b0001))))
  UDIV_REF11,  // (not (= (bvor s #b0001) (bvand x (bvnot t))))
  UDIV_REF12,  // (not (bvult (bvand x (bvneg t)) (bvand s t)))
  UDIV_REF13,  // (not (bvult s (bvlshr x t)))
  UDIV_REF14,  // (not (bvult x (bvshl (bvlshr s (bvshl s t)) #b0001)))
  UDIV_REF15,  // (not (bvult x (bvlshr (bvshl t #b0001) (bvshl t s))))
  UDIV_REF16,  // (not (bvult t (bvshl (bvlshr x s) #b0001)))
  UDIV_REF17,  // (not (bvult x (bvand (bvor x t) (bvshl s #b0001))))
  UDIV_REF18,  // (not (bvult x (bvand (bvor x s) (bvshl t #b0001))))
  UDIV_REF19,  // (not (= (bvlshr x t) (bvor s t)))
  UDIV_REF20,  // (not (= s (bvnot (bvlshr s (bvlshr t #b0001)))))
  UDIV_REF21,  // (not (= x (bvnot (bvand x (bvshl t #b0001)))))
  UDIV_REF22,  // (not (bvult x (bvshl x (bvlshr t (bvshl t #b0001)))))
  UDIV_REF23,  // (not (bvult t (bvlshr (bvshl x #b0001) s)))
  UDIV_REF24,  // (not (bvult x (bvshl s (bvnot (bvor x t)))))
  UDIV_REF25,  // (not (bvult x (bvshl t (bvnot (bvor x s)))))
  UDIV_REF26,  // (not (bvult x (bvxor t (bvlshr t (bvlshr s #b0001)))))
  UDIV_REF27,  // (not (bvult x (bvxor s (bvlshr s (bvlshr t #b0001)))))
  UDIV_REF28,  // (not (bvult x (bvshl s (bvnot (bvxor x t)))))
  UDIV_REF29,  // (not (bvult x (bvshl t (bvnot (bvxor x s)))))
  UDIV_REF30,  // (not (= x (bvadd t (bvor s (bvadd x s)))))
  UDIV_REF31,  // (not (= x (bvadd t (bvadd #b0001 (bvshl #b0001 x)))))
  UDIV_REF32,  // (not (bvult s (bvlshr (bvadd x t) t)))
  UDIV_REF33,  // (not (= x (bvadd t (bvadd t (bvor x s)))))
  UDIV_REF34,  // (not (bvult (bvxor s (bvor x t)) (bvxor t #b0001)))
  UDIV_REF35,  // (not (= x (bvsub #b0001 (bvshl x (bvadd x t)))))
  UDIV_REF36,  // (not (bvult t (bvlshr x (bvsub s #b0001))))
  UDIV_REF37,  // (not (bvult (bvsub s #b0001) (bvlshr x t)))
  UDIV_REF38,  // (not (= x (bvsub #b0001 (bvshl x (bvsub x t)))))
  UDIV_VALUE,

  UREM_REF1,  // (=> (distinct s #b0000) (bvule t s))
  UREM_REF2,  // (=> (= x #b0000) (= t #b0000))
  UREM_REF3,  // (=> (= s #b0000) (= t x))
  UREM_REF4,  // (=> (= s x) (= t #b0000))
  UREM_REF5,  // (=> (bvult x s) (= t x))
  UREM_REF6,  // (bvuge (bvnot (bvneg s)) t)

  UREM_REF7,   // (not (distinct x (bvand x (bvor s (bvor t (bvneg s))))))
  UREM_REF8,   // (not (bvult x (bvor t (bvand x s))))
  UREM_REF9,   // (not (= #b0001 (bvand t (bvnot (bvor x s)))))
  UREM_REF10,  // (not (= t (bvor (bvnot x) (bvneg s))))
  UREM_REF11,  // (not (bvult (bvand t (bvor x s)) (bvand t #b0001)))
  UREM_REF12,  // (not (= x (bvor (bvneg x) (bvneg (bvnot t)))))
  UREM_REF13,  // (not (bvult (bvadd x (bvneg s)) t))
  UREM_REF14,  // (not (bvult (bvxor (bvneg s) (bvor x s)) t))
  UREM_VALUE,

  ADD_ZERO,    // (=> (= s #b000) (= t x))
  ADD_SAME,    // (=> (= s x) (= ((_ extract 0 0) t) #b0))
  ADD_INV,     // (=> (= s (bvnot x)) (= t #b1111))
  ADD_OVFL,    // (=>
               //   (and (= (msb x) #b1) (= (msb s) #b1))
               //   (bvult t (bvand x s)))
  ADD_NOOFVL,  // (=>
               //   (and (= (msb x) #b0) (= (msb s) #b0))
               //   (bvuge t (bvor x s)))
  ADD_OR,      // (=> (= (bvand x s) #b000) (= t (bvor x s)))
               // (=> (= (bvadd x s) t) (=> (= s #b0000) (= t x)))
  ADD_REF1,    // (=> (= s x) (= ((_ extract 0 0) t) #b0)))
  ADD_REF2,    // (=> (= s (bvnot x)) (= t (bvnot #b0000))))
  ADD_REF3,    // (=> (= (bvand x s) #b0000) (= t (bvor x s))))
  ADD_REF4,    // (=>
               //   (and
               //     (= ((_ extract 3 3) x) #b0)
               //     (= ((_ extract 3 3) s) #b0)) (bvuge t (bvor x s))))
  ADD_REF5,    // (=>
               //   (and
               //     (= ((_ extract 3 3) x) #b1)
               //     (= ((_ extract 3 3) s) #b1)) (bvult t (bvand x s))))
  ADD_REF6,    // (not (distinct #b0000 (bvand x (bvand s (bvand t #b0001))))))
  ADD_REF7,    // (not (bvult (bvand #b0001 (bvor s t)) (bvand x #b0001))))
  ADD_REF8,    // (not (bvult (bvand #b0001 (bvor x t)) (bvand s #b0001))))
  ADD_REF9,    // (not (bvult (bvand #b0001 (bvor x s)) (bvand t #b0001))))
  ADD_REF10,   // (not (= #b0001 (bvor t (bvnot (bvand x s))))))
  ADD_REF11,   // (not (= t (bvnot (bvor t (bvand x s))))))
  ADD_REF12,   // (not (= #b0001 (bvor x (bvor s (bvnot t))))))
  ADD_VALUE,

  BITBLAST_FULL,
  BITBLAST_INC,
  ITE_EXPAND,
  ITE_REFINE,
  ASSERTION,
};

LemmaKind lemma_kind_value(node::Kind k);
bool is_lemma_kind_value(LemmaKind k);

std::ostream& operator<<(std::ostream& os, LemmaKind kind);

/* --- Abstraction Lemmas --------------------------------------------------- */

class AbstractionLemma
{
 public:
  AbstractionLemma(LemmaKind kind, bool commutative = true)
      : d_kind(kind), d_commutative(commutative){};
  virtual ~AbstractionLemma() {};

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
  ~Lemma<K>() {};
  Node instance(const Node& x, const Node& s, const Node& t) const override;
};

// Multiplication lemmas

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
Node Lemma<LemmaKind::MUL_SQUARE>::instance(const Node& x,
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

// Unsigned division lemmas

template <>
Node Lemma<LemmaKind::UDIV_REF1>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF2>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF3>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF4>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF5>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF6>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF7>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF8>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF9>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF10>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF11>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF12>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF13>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF14>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF15>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF16>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF17>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF18>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF19>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF20>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF21>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF22>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF23>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF24>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF25>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF26>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF27>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF28>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF29>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF30>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF31>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF32>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF33>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF34>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF35>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF36>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF37>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UDIV_REF38>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

// Unsigned remainder lemmas

template <>
Node Lemma<LemmaKind::UREM_REF1>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF2>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF3>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF4>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF5>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF6>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF7>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF8>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF9>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF10>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF11>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF12>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF13>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF14>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::UREM_REF11>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_ZERO>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_SAME>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_INV>::instance(const Node& x,
                                         const Node& s,
                                         const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_OVFL>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_NOOFVL>::instance(const Node& x,
                                            const Node& s,
                                            const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_OR>::instance(const Node& x,
                                        const Node& s,
                                        const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF1>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF2>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF3>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF4>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF5>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF6>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF7>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF8>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF9>::instance(const Node& x,
                                          const Node& s,
                                          const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF10>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF11>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;

template <>
Node Lemma<LemmaKind::ADD_REF12>::instance(const Node& x,
                                           const Node& s,
                                           const Node& t) const;
}  // namespace bzla::abstract

#endif
