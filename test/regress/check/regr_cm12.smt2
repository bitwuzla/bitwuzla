(set-info :status sat)
(declare-const x1 (Array Bool Bool))
(assert (select (store x1 false (forall ((x Bool)) (select x1 x))) (select x1 (forall ((x Bool)) false))))
(check-sat)
