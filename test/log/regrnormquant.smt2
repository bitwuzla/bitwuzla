(set-logic BV)
(assert
 (exists ((x Bool) (y Bool)) (not (and x y))))
(assert
 (exists ((z (_ BitVec 2))) (= (bvmul z #b10) #b11)))
(check-sat)
