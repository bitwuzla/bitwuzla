(assert (or false (forall ((q Bool)) (not (= q (forall ((q Bool)) false))))))
(set-info :status unsat)
(check-sat)
