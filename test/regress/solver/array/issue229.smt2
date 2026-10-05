; Satisfiable with S = {s1, s2} (or with s1 = s2 and |S| = 1), unsatisfiable if
; S is infinite. Equality reasoning over uninterpreted sorts is not supported,
; hence the result is unknown rather than an unsound unsat.
(set-logic ALL)
(declare-sort S 0)
(declare-const s1 S)
(declare-const s2 S)
(assert (= (store (store ((as const (Array S (_ BitVec 8))) #x00) s1 #x01) s2 #x01)
           ((as const (Array S (_ BitVec 8))) #x01)))
(check-sat)
