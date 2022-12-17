(set-logic QF_BV)
(set-info :status sat)
(assert (= #b1 (ite (= (_ bv18446744073709551617 65) (bvmul (_ bv274177 65) (_ bv67280421310721 65))) #b1 #b0)))
(check-sat)
