(set-option :abstraction true)
(set-option :abstraction-bv-size 3)
(set-info :status sat)
(declare-fun m () (_ BitVec 3))
(declare-fun x () (_ BitVec 2))
(declare-fun t () Bool)
(declare-fun _2 () Bool)
(declare-fun f ((Array (_ BitVec 3) (_ BitVec 3))) (Array (_ BitVec 3) (_ BitVec 3)))
(assert (not (and t _2)))
(assert (= t
 (= m
    (bvnot (bvand
            (concat x #b0)
            (select
             (f (store ((as const (Array (_ BitVec 3) (_ BitVec 3))) #b000) (bvurem #b001 m) #b000))
             #b001))))))
(check-sat)
