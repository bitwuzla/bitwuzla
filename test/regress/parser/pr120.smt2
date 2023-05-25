(set-option :global-declaration true)
(set-option :produce-models true)
(set-info :status sat)
(declare-fun f (Bool) Bool)
(define-fun a ((x (_ BitVec 11)) (y (_ BitVec 11))) Bool false)
(assert (= (a (_ bv0 11) (_ bv0 11)) (a (_ bv0 11) (_ bv0 11))))
(assert (= f f))
(check-sat)
(get-value (f))
(get-value (f (a (_ bv0 11) (_ bv0 11))))
(get-value ((a (_ bv0 11) (_ bv0 11)) (a (_ bv0 11) (_ bv0 11))))
(declare-fun b () Bool)