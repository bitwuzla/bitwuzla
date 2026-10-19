; The equality (= i i6) over an uninterpreted sort only appears in a constant
; array lemma. The second check-sat must answer unknown like the first one.
(declare-sort U 0)
(declare-const i U)
(declare-const i6 U)
(assert (select (store ((as const (Array U Bool)) false) i6 false) i))
(check-sat)
(check-sat)
