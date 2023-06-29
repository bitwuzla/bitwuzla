(set-info :status unsat)
(set-option :rewrite-level 0)
(assert (= (bvredxor (_ bv0 3)) (bvmul (bvnot (bvredxor (_ bv0 3))) (bvnot (bvredxor (_ bv0 3))))))
(check-sat)
