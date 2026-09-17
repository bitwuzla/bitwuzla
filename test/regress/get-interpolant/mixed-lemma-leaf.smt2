; Mixed lemmas, only visible at the term level: the UF congruence lemma
; (= accA accB) -> (= (f accA) (f accB)) consists of two equalities over
; array sort, which are BvSolver leafs. Each of them is bit-blasted into a
; single (opaque) AIG variable, thus the lemma does not mix A/B-labeled AIGs
; and the mixing is only detected when labeling the terms of the lemma.
(set-logic ALL)
(set-option :produce-interpolants true)
(declare-const z (Array (_ BitVec 2) (Array (_ BitVec 1) (_ BitVec 1))))
(declare-const i (_ BitVec 2))
(declare-const j (_ BitVec 2))
(declare-const p (Array (_ BitVec 1) (_ BitVec 1)))
(declare-const q (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun f ((Array (_ BitVec 1) (_ BitVec 1))) (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun g ((Array (_ BitVec 1) (_ BitVec 1))) (_ BitVec 1))
(assert (! (and (distinct i j) (= (g (f (select (store z i p) j))) #b0)) :named a1))
(assert (and (distinct i j) (= (g (f (select (store z i q) j))) #b1)))
(set-info :status unsat)
(check-sat)
(get-interpolant (a1))
