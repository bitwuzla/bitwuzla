(declare-fun b () (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))
(declare-fun a () (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))
(declare-const c (Array (_ BitVec 1) (_ BitVec 1)))
(assert
 (=
  (store a (_ bv0 1) (store c (_ bv0 1) (_ bv1 1)))
  (store b (_ bv1 1) (store (select b (_ bv0 1)) (_ bv0 1) (_ bv0 1)))
))
(set-info :status sat)
(check-sat)
