(set-logic ALL)
(set-info :status unsat)
; Same as alpha-shared-quant-capture.smt2, but with a binder chain of length
; two around the shared quantifier `q`.
;
; Without capture-avoiding substitution (prior to 1d051e985), this input
; distinguished determining that a quantifier is shared from its number of
; parents from the cheaper-looking test whether it has already been visited
; (i.e., whether it is in the normalization cache).
(define-fun q () Bool (exists ((x0 Bool)) (not (exists ((x1 Bool)) x0))))
(assert (=> (exists ((x5 Bool) (x6 Bool)) q) q))
(assert (not (forall ((a Bool)) (not (forall ((b Bool)) (not b))))))
(check-sat)
