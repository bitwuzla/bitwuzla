; Store chains over two different constant arrays with uninterpreted index
; sort U. Whether the stores cover U depends on |U|, so the constant array
; equality lemma cannot be stated, but the conflict on the outermost store
; index i2 is independent of |U| and must still be found.
(set-logic ALL)
(set-info :status unsat)
(declare-sort U 0)
(declare-const i1 U)
(declare-const i2 U)
(declare-const v1 (_ BitVec 8))
(declare-const v2 (_ BitVec 8))
(declare-const w1 (_ BitVec 8))
(declare-const w2 (_ BitVec 8))
(assert (= (store (store ((as const (Array U (_ BitVec 8))) #x00) i1 v1) i2 v2)
           (store (store ((as const (Array U (_ BitVec 8))) #x01) i1 w1) i2 w2)))
(assert (distinct v2 w2))
(check-sat)
(exit)
