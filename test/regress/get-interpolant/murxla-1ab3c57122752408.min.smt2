; ignore output
(declare-const __ (_ BitVec 1))
(set-option :produce-interpolants true)
(assert (= ((_ zero_extend 1) __) (bvadd (_ bv3 2) (bvudiv ((_ zero_extend 1) __) (_ bv3 2)) (bvudiv ((_ zero_extend 1) __) (_ bv3 2)))))
(push 1)
(assert (! (= ((_ zero_extend 1) __) (bvadd (_ bv3 2) (bvudiv ((_ zero_extend 1) __) (_ bv3 2)) (bvudiv ((_ zero_extend 1) __) (_ bv3 2)))) :named a1))
(set-info :status unsat)
(check-sat)
(get-interpolants (a1))
