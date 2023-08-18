(set-logic QF_BV)
(set-info :status sat)

; variables get bound twice
(assert
	(let
		(
			(x (_ bv1 6) )
		)
		(let
			(
				(x (_ bv0 6))
				(y x)
			)
			(not (= x y))
		)
	)
)
(check-sat)
