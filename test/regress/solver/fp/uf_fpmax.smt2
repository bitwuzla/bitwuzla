(set-info :status unsat)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (fp.isZero (fp.max x y)))
(assert (fp.isZero (fp.max y x)))
(assert (fp.isPositive y))
(assert (fp.isNegative x))

(assert
  (distinct (fp.max x y) (fp.max x (fp.add RTZ y (_ +zero 8 24))))
)
(check-sat)

