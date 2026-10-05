; Equality between two store chains built over two *different* constant arrays
; (defaults #x00 vs #x01) with uninterpreted (sort U) store indices. Deciding
; this equality runs default-value propagation on both sides, which queries the
; cardinality of the uninterpreted index sort via type::cardinality_gt (formerly
; aborting: card() had no uninterpreted case). The formula is satisfiable iff
; {i1, i2} covers U (e.g., U = {i1, i2}, v1 = w1, v2 = w2), which depends on the
; size of U, hence the expected output of Bitwuzla is unknown.
(set-logic ALL)
(declare-sort U 0)
(declare-const i1 U)
(declare-const i2 U)
(declare-const v1 (_ BitVec 8))
(declare-const v2 (_ BitVec 8))
(declare-const w1 (_ BitVec 8))
(declare-const w2 (_ BitVec 8))
(assert (= (store (store ((as const (Array U (_ BitVec 8))) #x00) i1 v1) i2 v2)
           (store (store ((as const (Array U (_ BitVec 8))) #x01) i1 w1) i2 w2)))
(check-sat)
(exit)
