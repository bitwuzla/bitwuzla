(set-info :status unsat)
(declare-const y (_ FloatingPoint 8 24))
(assert
 (distinct
  ((_ fp.to_sbv 32) roundTowardZero y)
  ((_ fp.to_sbv 32) roundTowardZero (fp.add roundTowardPositive y (_ +zero 8 24)))
 )
)
(check-sat)
