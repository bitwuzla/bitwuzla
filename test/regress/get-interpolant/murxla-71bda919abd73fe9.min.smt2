; ignore output
(set-option :produce-interpolants 1)
(set-option :abstraction-assert true)
(declare-const _x0 (_ BitVec 25))
(assert (bvugt _x0 #b0111110001000111101010011))
(assert (! (not (bvugt _x0 #b0111110001000111101010011)) :named a1))
(set-info :status unsat)
(check-sat)
(get-interpolant (a1))
