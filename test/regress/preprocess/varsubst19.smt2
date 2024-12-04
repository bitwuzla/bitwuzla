(set-info :status unsat)
(declare-const x Bool)
(assert (forall ((x6 RoundingMode)) (distinct x (forall ((x7 Bool)) x))))
(check-sat)
