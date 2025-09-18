; ignore output
(set-option :produce-interpolants 1)
(set-option :interpolants-lift true)
(declare-const _x0 (_ BitVec 84))
(assert (! (bvsmulo _x0 (bvashr _x0 _x0)) :named a1))
(assert (bvule (bvredxor (bvurem _x0 (bvadd (_ bv3871254126039278853526654 84) _x0))) (bvcomp (bvneg (bvashr _x0 _x0)) _x0)))
(set-info :status unsat)
(check-sat)
(get-interpolant (a1))
