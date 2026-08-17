(set-logic ALL)
(declare-const x (_ FloatingPoint 5 11))
(assert (= x ((_ to_fp 5 11) RNE (/ 1 0))))
(check-sat)
