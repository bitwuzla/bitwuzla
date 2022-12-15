(set-option :incremental false)
(set-logic QF_BV)
(declare-fun a () (_ BitVec 5))
(declare-fun b () (_ BitVec 5))
(declare-fun c () (_ BitVec 5))
(assert (not (= (bvmul a (bvmul b c)) (bvmul (bvmul a b) c))))
(check-sat)

