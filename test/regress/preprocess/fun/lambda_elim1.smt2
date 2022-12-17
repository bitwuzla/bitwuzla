(set-info :status unsat)
(define-fun a ((x (_ BitVec 11)) (y (_ BitVec 11))) Bool false)
(assert (and true (a (_ bv0 11) (_ bv0 11))))
(check-sat)
