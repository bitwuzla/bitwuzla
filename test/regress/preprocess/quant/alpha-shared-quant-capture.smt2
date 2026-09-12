(set-logic ALL)
(set-info :status unsat)
; `q` is shared between a nested and a non-nested position (see
; alpha-shared-quant.smt2), and must be normalized as a chain of its own.
;
; If `q` were also normalized as part of the chain of the quantifier over x5,
; the first normalization releases canonical variables that are still bound in
; the cached normal form of the quantifier nested in `q`, and the second one may
; reuse them. Without capture-avoiding substitution (prior to 1d051e985), this
; resulted in variable capture: the normal form of `q` was also the normal form
; of the second assertion's quantifier, and the two were merged although they
; are not alpha-equivalent. With capture-avoiding substitution, it results in a
; non-canonical normal form and thus a missed merge, which this test does not
; detect (see alpha-shared-quant-merge.smt2).
(define-fun q () Bool (exists ((x0 Bool)) (not (exists ((x1 Bool)) x0))))
(assert (=> (exists ((x5 Bool)) q) q))
(assert (not (forall ((a Bool)) (not (forall ((b Bool)) (not b))))))
(check-sat)
