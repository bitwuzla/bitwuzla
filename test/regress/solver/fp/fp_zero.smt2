(set-logic QF_FP)
(set-info :status unsat)
(define-fun x () Float64 (_ +zero 11 53))
(define-fun y () Float64 (_ -zero 11 53))
(assert (distinct x y))
(define-fun xz () Float64 (fp #b0 (_ bv0 11) (_ bv0 52)))
(assert (= x xz))
(define-fun yz () Float64 (fp #b1 (_ bv0 11) (_ bv0 52)))
(assert (= y yz))
(assert (distinct xz yz))
(declare-const a Float64);
(declare-const b Float64);
(assert (= a b));
(assert (= a x));
(assert (= b y));
(check-sat)
