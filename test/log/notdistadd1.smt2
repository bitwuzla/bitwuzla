(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (distinct
  (bvnot (bvadd x y))
  (bvadd (bvadd (bvnot x) (bvnot y)) (_ bv1 32))))
(check-sat)
(exit)
