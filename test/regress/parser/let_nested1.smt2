(set-info :status sat)
(declare-const a (_ BitVec 1))
(assert (let ((x (let ((y a)) y)) (y a)) (= x y)))
(check-sat)
