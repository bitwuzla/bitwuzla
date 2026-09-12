(set-option :pp-quant true)
(set-option :pp-quant-alpha true)
(set-logic ALL)
; `q` is shared between a nested and a non-nested position (see
; alpha-shared-quant.smt2), and the second assertion's quantifier is an
; alpha-equivalent copy of `q`. The two must be merged.
;
; If `q` were also normalized as part of the chain of the quantifier over x5,
; its second normalization may reuse a canonical variable that is still bound in
; the cached normal form of the quantifier nested in `q`. Substitution then
; renames the nested binder to a fresh variable, the normal form of `q` is not
; canonical, and the merge is missed.
(define-fun q () Bool (exists ((x0 Bool)) (not (exists ((x1 Bool)) x0))))
(assert (=> (exists ((x5 Bool)) q) q))
(assert (exists ((y0 Bool)) (not (exists ((y1 Bool)) y0))))
(check-sat)
