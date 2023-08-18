(set-logic QF_BV)
(set-info :status sat)

; Let in the binding part of another let with shadowing.
(assert
	(let
		(
			(x (_ bv7 5))
		)
		(let
			(
				(x (bvadd x (_ bv10 5)))
			)
			(= (_ bv17 5) x)
		)
	)
)

(check-sat)
