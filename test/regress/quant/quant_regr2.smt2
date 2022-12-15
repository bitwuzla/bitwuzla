(set-info :status sat)
(declare-fun Q (Bool Bool Bool Bool) Bool)
(assert (forall ((x Bool)) (or true (exists ((y Bool)) (Q x false false true)))))
(check-sat)
