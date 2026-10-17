(declare-const a (_ BitVec 4))
(assert (= a (let ((x a)) x x)))
