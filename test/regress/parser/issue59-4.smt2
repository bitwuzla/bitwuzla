(set-logic QF_BV)
(set-info :status unsat)

; Let in the binding part of another let with shadowing.
(assert
	(let
		(
			(x (_ bv7 5))
		)
		(let
			(
				(x (let ((x (bvadd x (_ bv10 5)))) (let ((x (_ bv2 5))) x)))
			)
			(= (_ bv17 5) x)
		)
	)
)

(check-sat)
