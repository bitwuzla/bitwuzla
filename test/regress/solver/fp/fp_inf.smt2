(set-logic QF_FP)
(set-info :status unsat)
(define-fun x () Float64 (_ +oo 11 53))
(define-fun y () Float64 (_ -oo 11 53))
(assert (= x y))
(declare-const a Float64);
(declare-const b Float64);
(assert (= a b));
(assert (= a x));
(assert (= b y));
(check-sat)
