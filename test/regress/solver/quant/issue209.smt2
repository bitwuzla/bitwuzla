(set-logic BVFP)
(assert (forall ((any (_ BitVec 8))) (= any ((_ fp.to_ubv 8) RNE (fp #b0 #b11111111 #b00000000000000000000000)))))
(set-info :status unsat)
(check-sat)
