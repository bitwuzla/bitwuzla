(set-info :status sat)
(assert (not (forall ((x Bool) (|x| (_ BitVec 1))) (= x #b0))))
(assert (exists ((|y| Bool) (y (_ BitVec 1))) (= y #b1)))
(check-sat)
