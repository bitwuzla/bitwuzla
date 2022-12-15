(set-info :status unsat)
(declare-fun W () Bool)
(assert (and true (forall ((M Bool)) (and M W))))
(check-sat)
