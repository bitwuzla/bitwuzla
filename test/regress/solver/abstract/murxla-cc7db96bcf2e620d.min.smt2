(declare-const x (_ BitVec 1))
(set-option :abstraction-assert true)
(set-info :status unsat)
(check-sat-assuming ((bvsaddo (_ bv0 62) (bvrol (_ bv1 62) ((_ zero_extend 61) x)))))
