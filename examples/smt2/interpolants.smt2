(set-logic QF_BV)

(set-option :produce-interpolants true)
(set-option :interpolants-simp true)

(declare-const x1 (_ BitVec 2))
(declare-const x2 (_ BitVec 2))
(declare-const x3 (_ BitVec 2))

(assert (! (bvslt #b0000 (bvsub ((_ zero_extend 2) x1) #b0001)) :named a1))
(assert (! (= x1 x2) :named a2))
(assert (! (= x3 ((_ extract 1 0) (bvneg ((_ zero_extend 2) x2)))) :named a3))
(assert (! (= x3 #b00) :named a4))

(check-sat)

; Query an interpolant for A /\ B with A = {a1, a2}.
(get-interpolants (a1 a2))

; Query an interpolation sequence for a sequence of A/B-partitions
;     {
;       ({a1},        {a2, a3, a4}),
;       ({a1, a2},    {a3, a4}),
;       ({a1, a2, a3, {a4})
;     }
; given as a list {{a1}, {a2}, {a3}} of increments of A.
(get-interpolants (a1) (a2) (a3))
