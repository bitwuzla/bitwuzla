(declare-fun x (Bool Bool) Bool)
(declare-const x2 Bool)
(set-info :status sat)
(check-sat-assuming (x2 (distinct x2 (exists ((x6 Bool)) (x true (forall ((_x Bool)) (ite x6 _x (x false false))))))))
