(set-logic ALL)
(set-info :status sat)
; Murxla-found (murxla-19dc2c08895d0731.min.trace). Note that this does not
; require a variable node bound by two binders (which is only reachable via the
; API), sharing a quantifier suffices, and define-fun shares nodes.
;
; `q` is shared between a nested and a non-nested position: it is the body of
; the existential quantifier over x5, and the right-hand side of the
; implication. If `q` is treated as part of the binder chain of the quantifier
; over x5, that chain includes the variable of `q`, and so does the chain of
; `q` itself.

; This test case is a witness for why we should not use a substitution map
; shared across chains: since the second chain would normalize its body with
; the canonical variable of the first chain, this would result in a normal form
; with a free canonical variable.
(define-fun q () Bool (exists ((x0 Bool)) (not (exists ((x1 Bool)) x0))))
(assert (=> (exists ((x5 Bool)) q) q))
(check-sat)
