(set-logic BV)
(set-info :status unsat)
(set-option :pp-quant true)
(set-option :pp-quant-alpha true)
(assert (exists ((z (_ BitVec 2))) (= (bvmul z #b10) #b11)))
(assert (exists ((y (_ BitVec 2))) (= (bvmul y #b10) #b11)))
(check-sat)

