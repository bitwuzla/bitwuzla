(set-logic QF_ABV)
(set-option :preprocess false)
(declare-const v (_ BitVec 2))
(declare-const a (_ BitVec 2))
(declare-const b (_ BitVec 2))
(declare-const K1 (Array (_ BitVec 1) (_ BitVec 2)))
(declare-const K2 (Array (_ BitVec 1) (_ BitVec 2)))
(declare-const P (Array (_ BitVec 1) (_ BitVec 2)))
; Regression guard for model construction over constant arrays. The default
; value's coverage must come from the recorded propagation coverage
; (d_dv_coverage = Updated Indices I(a,<v>), Def. 4), which the CowD/CowU gate
; keeps below the index cardinality, rather than recomputed from a shortest-hop
; path that may cross all stores and report full coverage -- which would
; mis-compute P's default value. The equality detour C = K1 = K2 = store-chain
; = P reaches P via a path distinct from the store-crossing one, so the
; shortest-hop recompute diverges from the propagation coverage. Needs
; preprocessing disabled, as default preprocessing collapses the detour.
(assert (= ((as const (Array (_ BitVec 1) (_ BitVec 2))) v) K1))
(assert (= K1 K2))
(assert (= K2 (store (store ((as const (Array (_ BitVec 1) (_ BitVec 2))) v) (_ bv0 1) a) (_ bv1 1) b)))
(assert (= (store (store ((as const (Array (_ BitVec 1) (_ BitVec 2))) v) (_ bv0 1) a) (_ bv1 1) b) P))
(assert (distinct v (_ bv0 2)))
(set-info :status sat)
(check-sat)
