(set-info :status sat)
(declare-fun x () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun x1 () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (concat (select x1 (_ bv0 32)) (select x1 (_ bv0 32)) (select x1 (_ bv1 32)) (select x1 (_ bv0 32))) (bvmul (concat (select x1 (_ bv0 32)) (select x (_ bv0 32)) (select x1 (_ bv1 32)) (select x1 (_ bv0 32))) (concat (select x1 (_ bv0 32)) (select x1 (_ bv0 32)) (select x (_ bv1 32)) (select x1 (_ bv0 32))) (concat (select x1 (_ bv0 32)) (select x1 (_ bv0 32)) (select x1 (_ bv1 32)) (select x1 (_ bv0 32))) (concat (select x1 (_ bv0 32)) (select x1 (_ bv0 32)) (select x1 (_ bv1 32)) (select x1 (_ bv0 32))) (concat (select x1 (_ bv0 32)) (select x (_ bv0 32)) (select x1 (_ bv1 32)) (select x1 (_ bv0 32))) (concat (select x1 (_ bv0 32)) (select x1 (_ bv0 32)) (select x (_ bv1 32)) (select x1 (_ bv0 32))) (concat (select x1 (_ bv0 32)) (select x1 (_ bv0 32)) (select x1 (_ bv1 32)) (select x1 (_ bv0 32))))))
(check-sat)
