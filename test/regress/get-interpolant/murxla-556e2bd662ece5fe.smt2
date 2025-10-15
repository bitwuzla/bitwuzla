; ignore output
(set-option :produce-interpolants true)
(declare-const _x0 (_ BitVec 15))
(assert (! (let ((_let0 (bvadd #b001011010110110 _x0 _x0)))(bvugt (bvlshr _let0 _x0) _let0)) :named a0))
(push 1)
(assert (! (let ((_let0 (bvadd #b001011010110110 _x0 _x0)))(let ((_let1 (bvlshr _let0 _x0)))(let ((_let2 (bvsmulo _let1 _let1)))(ite _let2 (bvugt _let1 _let0) _let2)))) :named a1))
(set-info :status unsat)
(check-sat)
(get-interpolants (a0) (a1))
