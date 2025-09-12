; ignore output
(set-option :produce-interpolants 1)
(declare-const _x0 (_ BitVec 77))
(assert (! (let ((_let0 (bvashr #b00000000000000000000000000000000000000000000000000000000000000000000000000001 _x0)))(let ((_let1 ((_ sign_extend 41) _x0)))(= (bvumulo _let1 _let1) (bvumulo _let0 _let0)))) :named a1))
(assert (let ((_let0 ((_ sign_extend 41) _x0)))(bvumulo _let0 _let0)))
(set-info :status unsat)
(check-sat)
(get-interpolant (a1))
