; ignore output
(declare-const __ (_ BitVec 1))
(set-option :produce-interpolants 1)
(set-option :abstraction-bv-size 3)
(assert (! (bvsmulo ((_ zero_extend 2) __) ((_ zero_extend 2) __)) :named a1))
(assert true)
(set-info :status unsat)
(check-sat)
(get-interpolant (a1))
