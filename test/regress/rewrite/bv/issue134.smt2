(set-logic QF_BV)
(set-info :status sat)
(declare-fun t () (_ BitVec 1))
(assert (= #b1 ((_ extract 0 0) (bvor (concat #b1 t) (concat (bvredor t) #b1)))))
(check-sat)
