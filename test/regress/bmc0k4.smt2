(set-info :source "Armin Biere, FMV, JKU, June, 2011.

  Incremental example, assumptions are added eagerly.

  Formulas are only checked individually and not asserted permanently
  Start with all bits zero state.

  The input vectors i0, i1, ... have the same size as the state s0, s1, ...
  vectors and are simply added to them to get the next state.

  Toggle at most one bit per step using the Hacker Delight trick
  '(i & (i-1)) == 0' iff i has exactly one bit set.")
(set-logic QF_BV)
(declare-fun goal () (_ BitVec 4))
(declare-fun zero () (_ BitVec 4))
(declare-fun one () (_ BitVec 4))
(declare-fun s0 () (_ BitVec 4))
(declare-fun i0 () (_ BitVec 4))
(declare-fun s1 () (_ BitVec 4))
(declare-fun i1 () (_ BitVec 4))
(declare-fun s2 () (_ BitVec 4))
(declare-fun i2 () (_ BitVec 4))
(declare-fun s3 () (_ BitVec 4))
(declare-fun i3 () (_ BitVec 4))
(declare-fun s4 () (_ BitVec 4))
(declare-fun i4 () (_ BitVec 4))
(declare-fun s5 () (_ BitVec 4))
(assert (= goal (_ bv15 4)))
(assert (= zero (_ bv0 4)))
(assert (= one (_ bv1 4)))
(assert (= s0 zero))
(push 1)
(assert (= s0 goal))
(check-sat)
(pop 1)

(assert (= (bvand i0 (bvsub i0 one)) zero))
(assert (= s1 (bvadd s0 i0)))
(push 1)
(assert (= s1 goal))
(check-sat)
(pop 1)

(assert (= (bvand i1 (bvsub i1 one)) zero))
(assert (= s2 (bvadd s1 i1)))
(push 1)
(assert (= s2 goal))
(check-sat)
(pop 1)

(assert (= (bvand i2 (bvsub i2 one)) zero))
(assert (= s3 (bvadd s2 i2)))
(push 1)
(assert (= s3 goal))
(check-sat)
(pop 1)

(assert (= (bvand i3 (bvsub i3 one)) zero))
(assert (= s4 (bvadd s3 i3)))
(push 1)
(assert (= s4 goal))
(check-sat)
(pop 1)

(assert (= (bvand i4 (bvsub i4 one)) zero))
(assert (= s5 (bvadd s4 i4)))
(push 1)
(assert (= s5 goal))
(check-sat)
(pop 1)

