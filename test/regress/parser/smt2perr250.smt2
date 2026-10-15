(declare-const a (_ BitVec 1))
(assert (let ((x (let ((y a)) y)) (x a)) (= x x)))
