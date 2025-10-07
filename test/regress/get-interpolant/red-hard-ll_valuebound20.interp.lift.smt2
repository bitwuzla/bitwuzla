; ignore output
(set-option :produce-interpolants true)
(set-option :interpolants-lift false)
(set-option :abstraction-bv-size 3)
(declare-const s (_ BitVec 1))
(declare-const t (_ BitVec 1))
(assert (! (= (_ bv0 3) (bvmul ((_ zero_extend 2) t) ((_ zero_extend 2) s))) :named a1))
(assert (= (_ bv1 1) (ite (not (= ((_ zero_extend 2) s) (bvmul ((_ zero_extend 2) s) ((_ zero_extend 2) s)))) (_ bv1 1) (_ bv0 1))))

(set-info :status unsat)
(check-sat)
(get-interpolant (a1))
