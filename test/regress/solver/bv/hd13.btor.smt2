(set-logic QF_BV)
(set-info :status unsat)
(declare-const v0 (_ BitVec 32))
(declare-const v1 (_ BitVec 32))
(assert
 (or
  (or
   (or
    (not (= (bvult v0 v1) (not (bvule v1 v0))))
    (not (= (bvugt v0 v1) (not (bvule v0 v1)))))
   (or
    (or
     (not
      (=
       (bvslt v0 v1)
       (not
        (bvule
         (bvadd v1 #b10000000000000000000000000000000)
         (bvadd v0 #b10000000000000000000000000000000)))))
     (not
      (=
       (bvsle v0 v1)
       (bvule
        (bvadd v0 #b10000000000000000000000000000000)
        (bvadd v1 #b10000000000000000000000000000000)))))
    (or
     (not
      (=
       (not
        (bvule
         (bvadd v0 #b10000000000000000000000000000000)
         (bvadd v1 #b10000000000000000000000000000000)))
       (bvsgt v0 v1)))
     (not
      (=
       (bvule
        (bvadd v1 #b10000000000000000000000000000000)
        (bvadd v0 #b10000000000000000000000000000000))
       (bvsge v0 v1))))))
  (not (= (bvuge v0 v1) (bvule v1 v0)))))
(check-sat)
