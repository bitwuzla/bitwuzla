(set-logic QF_BV)
(assert
 (let
  (
   (x (_ bv0 6))
   (y x)
	)
  (not (= x y))
 )
)
