(set-info :status sat)
(declare-const x (Array (_ BitVec 3) (_ BitVec 3)))
(assert (bvult (_ bv0 3) (bvadd (bvmul (select x (_ bv0 3)) (select x (_ bv0 3))) (bvmul (select x (_ bv0 3)) (select x (_ bv0 3))))))
(check-sat)
