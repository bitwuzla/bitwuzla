; The distinct decision heuristic registered after the pop forces phases on
; the bits of the constant store index, which are root-fixed while not yet
; observed. It only observes its bits, so cb_decide() relies on CaDiCaL
; notifying their assignment on observe to never decide on them.
(set-logic QF_ABV)
(declare-const x (_ BitVec 4))
(declare-const d0 (_ BitVec 4))
(declare-const d1 (_ BitVec 4))
(push 1)
(assert (distinct d0 d1))
(assert (= (store ((as const (Array (_ BitVec 1) (_ BitVec 4))) d0) #b1 x) ((as const (Array (_ BitVec 1) (_ BitVec 4))) d1)))
(set-info :status unsat)
(check-sat)
(pop 1)
(assert (bvult (bvmul x d0) (bvadd x d1)))
(set-info :status sat)
(check-sat)
