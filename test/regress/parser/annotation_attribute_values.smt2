(set-logic UFBV)
(set-option :produce-models true)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-const a (_ BitVec 4))
(declare-const b Bool)
; values of unsupported attributes are arbitrary s-expressions, which may
; contain undefined symbols, keywords and reserved words
(assert (forall ((x (_ BitVec 4))) (! (= (f x) (bvadd x #x1)) :pattern ((f x)))))
(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4)))
  (! (=> (= x y) (= (f x) (f y))) :pattern ((f x) (f y)) :pattern ((f x)) :qid q1)))
(assert (! b :baz (bvadd x y)))
(assert (! b :foo ((undefined 1) :key (as let) "str" #b01 |q s|)))
; keyword attributes
(assert (! b :status sat :category "industrial"))
; attributes without value
(assert (! b :foo))
(assert (! b :foo :named n1))
(assert (! (= a (f #x0)) :bar :named n2 :baz (1 2)))
(check-sat)
(get-value (a n1 n2))
