(declare-const a (_ BitVec 1))
(assert (let ((x a) (z (let ((y a)) x))) (= x z)))
