(declare-fun P (Bool) Bool)
(declare-fun Q (Bool Bool Bool Bool) Bool)
(assert (forall ((x Bool)) (or false (exists ((y Bool)) (and (P false) (Q y false false false))))))
(check-sat)
