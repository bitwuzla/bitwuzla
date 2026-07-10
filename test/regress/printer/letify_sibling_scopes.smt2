(set-logic BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
; term shared across sibling binder scopes: must not be printed in the second
; scope as a let symbol whose let is already closed
(assert (and
  (forall ((x (_ BitVec 8))) (distinct x (bvadd (bvmul a b) (bvmul a b))))
  (forall ((y (_ BitVec 8))) (distinct y (bvmul a b)))))
; term letified in the enclosing scope and shared again within a binder scope:
; must reuse the enclosing let symbol instead of re-letifying it (alias let)
(assert (and
  (= a (bvmul b b))
  (forall ((z (_ BitVec 8))) (distinct z (bvadd (bvmul b b) (bvmul b b))))))
