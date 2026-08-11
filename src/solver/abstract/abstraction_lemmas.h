#ifndef BZLA_SOLVER_BV_ABSTRACTION_LEMMAS_H_INCLUDED
#define BZLA_SOLVER_BV_ABSTRACTION_LEMMAS_H_INCLUDED

#include <cstdint>
#include <ostream>

#include "node/node.h"
#include "node/node_manager.h"

namespace bzla::abstract {

enum class LemmaKind : uint32_t
{
  MUL1_POW2,      // 1*: (=> (= s 2^i) (= t (bvshl x i)))
  MUL2_NEG_POW2,  // 2*: (=> (= s -2^i) (= t (bvshl (bvneg x) i)))
  MUL3_IC,        // 3*: (= (bvand (bvor (bvneg s) s) t) t),
  MUL4_ODD,       // 4*: (= t (bvor t (bvand x (bvand s #b0001))))
  MUL5,           //  5: (not (= s (bvnot (bvor t (bvand #b0001 (bvor x s))))))
  MUL6,           //  6: (not (= (bvand x t) (bvor s (bvnot t))))
  MUL7,           //  7: (not (= t (bvshl (bvor s #b0001) (bvshl t x))))
  MUL8,           //  8: (= s (bvshl s (bvand x (bvlshr #b0001 t))))
  MUL9,           //  9: (bvuge t (bvand #b0001 (bvlshr (bvand x s) #b0001)))
  MUL10,          // 10: (not (= x (bvxor #b0001 (bvshl x (bvxor s t)))))
  MUL11,          // 11: (not (= t (bvor #b0001 (bvnot (bvxor x s)))))
  MUL12,          // 12: (not (= t (bvor (bvnot #b0001) (bvxor x s))))
  MUL13,          // 13: (not (= x (bvsub (bvshl x (bvadd s t)) #b0001)))
  MUL14,          // 14: (not (= x (bvsub #b0001 (bvshl x (bvsub s t)))))
  MUL15,          // 15: (not (= s (bvadd #b0001 (bvshl s (bvsub t x)))))
  MUL16,          // 16: (not (= s (bvsub #b0001 (bvshl s (bvsub t x)))))
  MUL17,          // 17: (not (= s (bvadd #b0001 (bvshl s (bvsub x t)))))
  MUL18,          // 18: (not (= t (bvor #b0001 (bvadd x s))))
  MUL19,          // 19: (not (= x (bvnot (bvshl x (bvadd s t)))))
  MUL_VALUE,

  UDIV1_POW2,  // 1*: (=> (= s 2^i) (= t (bvlshr x i)))
  UDIV37,      //  -: (=> (= s #b0001) (= t x))
  UDIV2,       // 2*: (=> (and (= s x) (distinct s #b0000)) (= t #b0001))
  UDIV3,       // 3*: (=> (= s #b0000) (= t (bvnot #b0000)))
  UDIV4,       // 4*: (=> (and (= x #b0000) (distinct s #b0000)) (= t #b0000))
  UDIV5,       // 5*: (=> (distinct s #b0000) (bvule t x))
  UDIV6,       // 6*: (let ((_let_1 (bvnot #b0000)))
               //     (=> (and (= s _let_1) (distinct x _let_1)) (= t #b0000)))
  UDIV7,       //  7: (not (bvult x (bvneg (bvand (bvneg s) (bvneg t)))))
  UDIV8,       //  8: (not (bvult (bvneg (bvor s #b0001)) t))
  UDIV9,       //  9: (not (= t (bvneg (bvand s (bvnot x)))))
  UDIV10,      // 10: (not (= (bvor s t) (bvand x (bvnot #b0001))))
  UDIV11,      // 11: (not (= (bvor s #b0001) (bvand x (bvnot t))))
  UDIV12,      // 12: (not (bvult (bvand x (bvneg t)) (bvand s t)))
  UDIV13,      // 13: (not (bvult s (bvlshr x t)))
  UDIV14,      // 14: (not (bvult x (bvshl (bvlshr s (bvshl s t)) #b0001)))
  UDIV15,      // 15: (not (bvult x (bvlshr (bvshl t #b0001) (bvshl t s))))
  UDIV16,      // 16: (not (bvult t (bvshl (bvlshr x s) #b0001)))
  UDIV17,      // 17: (not (bvult x (bvand (bvor x t) (bvshl s #b0001))))
  UDIV18,      // 18: (not (bvult x (bvand (bvor x s) (bvshl t #b0001))))
  UDIV19,      // 19: (not (= (bvlshr x t) (bvor s t)))
  UDIV20,      // 20: (not (= s (bvnot (bvlshr s (bvlshr t #b0001)))))
  UDIV21,      // 21: (not (= x (bvnot (bvand x (bvshl t #b0001)))))
  UDIV22,      // 22: (not (bvult t (bvlshr (bvshl x #b0001) s)))
  UDIV23,      // 23: (not (bvult x (bvshl s (bvnot (bvor x t)))))
  UDIV24,      // 24: (not (bvult x (bvshl t (bvnot (bvor x s)))))
  UDIV25,      // 25: (not (bvult x (bvxor t (bvlshr t (bvlshr s #b0001)))))
  UDIV26,      // 26: (not (bvult x (bvxor s (bvlshr s (bvlshr t #b0001)))))
  UDIV27,      // 27: (not (bvult x (bvshl s (bvnot (bvxor x t)))))
  UDIV28,      // 28: (not (bvult x (bvshl t (bvnot (bvxor x s)))))
  UDIV29,      // 29: (not (= x (bvadd t (bvor s (bvadd x s)))))
  UDIV30,      // 30: (not (= x (bvadd t (bvadd #b0001 (bvshl #b0001 x)))))
  UDIV31,      // 31: (not (bvult s (bvlshr (bvadd x t) t)))
  UDIV32,      // 32: (not (= x (bvadd t (bvadd t (bvor x s)))))
  UDIV33,      // 33: (not (bvult (bvxor s (bvor x t)) (bvxor t #b0001)))
  UDIV34,      // 34: (not (bvult t (bvlshr x (bvsub s #b0001))))
  UDIV35,      // 35: (not (bvult (bvsub s #b0001) (bvlshr x t)))
  UDIV36,      // 36: (not (= x (bvsub #b0001 (bvshl x (bvsub x t)))))
  UDIV_VALUE,

  UREM1_POW2,  // 1*: (=> (= s 2^i)
               //         (= t((_ zero_extend n-i) ((_ extract i-1 0) x))))
  UREM2,       // 2*: (=> (distinct s #b0000) (bvult t s))
  UREM3,       // 3*: (=> (= x #b0000) (= t #b0000))
  UREM4,       // 4*: (=> (= s #b0000) (= t x))
  UREM5,       // 5*: (=> (= s x) (= t #b0000))
  UREM6,       // 6*: (=> (bvult x s) (= t x))
  UREM7,       // 7*: (bvuge (bvnot (bvneg s)) t)
  UREM8,       //  8: (not (distinct x (bvand x (bvor s (bvor t (bvneg s))))))
  UREM9,       //  9: (not (bvult x (bvor t (bvand x s))))
  UREM10,      // 10: (not (= #b0001 (bvand t (bvnot (bvor x s)))))
  UREM11,      // 11: (not (= t (bvor (bvnot x) (bvneg s))))
  UREM12,      // 12: (not (bvult (bvand t (bvor x s)) (bvand t #b0001)))
  UREM13,      // 13: (not (= x (bvor (bvneg x) (bvneg (bvnot t)))))
  UREM14,      // 14: (not (bvult (bvadd x (bvneg s)) t))
  UREM15,      // 15: (not (bvult (bvxor (bvneg s) (bvor x s)) t))
  UREM_VALUE,

  ADD_ZERO,    // (=> (= s #b0000) (= t x))
  ADD_SAME,    // (=> (= s x) (= ((_ extract 0 0) t) #b0))
  ADD_INV,     // (=> (= s (bvnot x)) (= t #b1111))
  ADD_OVFL,    // (=>
               //   (and (= (msb x) #b1) (= (msb s) #b1))
               //   (bvult t (bvand x s)))
  ADD_NOOVFL,  // (=>
               //   (and (= (msb x) #b0) (= (msb s) #b0))
               //   (bvuge t (bvor x s)))
  ADD_OR,      // (=> (= (bvand x s) #b000) (= t (bvor x s)))
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
  BITBLAST_BV_MUL,
  BITBLAST_BV_MUL_SQUARE,  // (=> (= x s) (= t (bvmul x x))), uses special
                           // encoding
  BITBLAST_BV_UDIV,
  BITBLAST_BV_UREM,
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
  AbstractionLemma(NodeManager& nm, LemmaKind kind) : d_nm(nm), d_kind(kind) {}
  virtual ~AbstractionLemma() {}

  /** Return lemma kind. */
  LemmaKind kind() const { return d_kind; }

  /** Get instance of abstraction lemma. */
  virtual Node instance(const Node& x, const Node& s, const Node& t) const = 0;

  virtual Node instance(const Node& val_x,
                        const Node& val_s,
                        const Node& val_t,
                        const Node& x,
                        const Node& s,
                        const Node& t) const = 0;

 protected:
  NodeManager& d_nm;
  LemmaKind d_kind;
};

template <enum LemmaKind K>
class Lemma : public AbstractionLemma
{
 public:
  Lemma(NodeManager& nm) : AbstractionLemma(nm, K) {}
  ~Lemma() {}
  Node instance(const Node& x, const Node& s, const Node& t) const override
  {
    (void) x;
    (void) s;
    (void) t;
    return Node();
  }
  Node instance(const Node& val_x,
                const Node& val_s,
                const Node& val_t,
                const Node& x,
                const Node& s,
                const Node& t) const override
  {
    (void) val_x;
    (void) val_s;
    (void) val_t;
    (void) x;
    (void) s;
    (void) t;
    return Node();
  }
};

#define LEMMA(kind)                      \
  template <>                            \
  Node Lemma<LemmaKind::kind>::instance( \
      const Node& x, const Node& s, const Node& t) const

#define LEMMA_VAL(kind)                                    \
  template <>                                              \
  Node Lemma<LemmaKind::kind>::instance(const Node& val_x, \
                                        const Node& val_s, \
                                        const Node& val_t, \
                                        const Node& x,     \
                                        const Node& s,     \
                                        const Node& t) const

// Multiplication lemmas

LEMMA(MUL3_IC);
LEMMA(MUL4_ODD);
LEMMA_VAL(MUL1_POW2);
LEMMA_VAL(MUL2_NEG_POW2);
LEMMA(MUL5);
LEMMA(MUL6);
LEMMA(MUL7);
LEMMA(MUL8);
LEMMA(MUL9);
LEMMA(MUL10);
LEMMA(MUL11);
LEMMA(MUL12);
LEMMA(MUL13);
LEMMA(MUL14);
LEMMA(MUL15);
LEMMA(MUL16);
LEMMA(MUL17);
LEMMA(MUL18);
LEMMA(MUL19);

// Unsigned division lemmas

LEMMA_VAL(UDIV1_POW2);
LEMMA(UDIV37);
LEMMA(UDIV2);
LEMMA(UDIV3);
LEMMA(UDIV4);
LEMMA(UDIV5);
LEMMA(UDIV6);
LEMMA(UDIV7);
LEMMA(UDIV8);
LEMMA(UDIV9);
LEMMA(UDIV10);
LEMMA(UDIV11);
LEMMA(UDIV12);
LEMMA(UDIV13);
LEMMA(UDIV14);
LEMMA(UDIV15);
LEMMA(UDIV16);
LEMMA(UDIV17);
LEMMA(UDIV18);
LEMMA(UDIV19);
LEMMA(UDIV20);
LEMMA(UDIV21);
LEMMA(UDIV22);
LEMMA(UDIV23);
LEMMA(UDIV24);
LEMMA(UDIV25);
LEMMA(UDIV26);
LEMMA(UDIV27);
LEMMA(UDIV28);
LEMMA(UDIV29);
LEMMA(UDIV30);
LEMMA(UDIV31);
LEMMA(UDIV32);
LEMMA(UDIV33);
LEMMA(UDIV34);
LEMMA(UDIV35);
LEMMA(UDIV36);

// Unsigned remainder lemmas

LEMMA_VAL(UREM1_POW2);
LEMMA(UREM2);
LEMMA(UREM3);
LEMMA(UREM4);
LEMMA(UREM5);
LEMMA(UREM6);
LEMMA(UREM7);
LEMMA(UREM8);
LEMMA(UREM9);
LEMMA(UREM10);
LEMMA(UREM11);
LEMMA(UREM12);
LEMMA(UREM13);
LEMMA(UREM14);
LEMMA(UREM15);

// Addition lemmas

LEMMA(ADD_ZERO);
LEMMA(ADD_SAME);
LEMMA(ADD_INV);
LEMMA(ADD_OVFL);
LEMMA(ADD_NOOVFL);
LEMMA(ADD_OR);
LEMMA(ADD_REF6);
LEMMA(ADD_REF7);
LEMMA(ADD_REF8);
LEMMA(ADD_REF9);
LEMMA(ADD_REF10);
LEMMA(ADD_REF11);
LEMMA(ADD_REF12);

#undef LEMMA
#undef LEMMA_VAL

}  // namespace bzla::abstract

#endif
