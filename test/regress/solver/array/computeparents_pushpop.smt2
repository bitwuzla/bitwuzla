(set-logic QF_AUFBV)
; Regression for duplicate/stale parent accumulation in the array solver.
;
; compute_parents() guards parent-edge insertion with the backtrackable set
; d_active_parents, but the parent map d_parents used to be a plain map that was
; never pruned on pop(). Re-asserting the same array equality after a pop() then
; appended duplicate parent entries, growing d_parents unboundedly across
; push/pop cycles and making the propagation in each check() do redundant work
; on parents from popped scopes. Here the same write-chain-permutation equality
; (which survives preprocessing and triggers up/down propagation through the
; store parents) is asserted in every cycle; the result must stay correct and
; the per-cycle work must not grow.
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i0 () (_ BitVec 8))
(declare-fun i1 () (_ BitVec 8))
(declare-fun i2 () (_ BitVec 8))
(declare-fun v0 () (_ BitVec 8))
(declare-fun v1 () (_ BitVec 8))
(declare-fun v2 () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))

(push 1)
(assert (= (store (store (store a i0 v0) i1 v1) i2 v2)
           (store (store (store a i2 v2) i1 v1) i0 v0)))
(assert (= (select a j) (_ bv7 8)))
(set-info :status sat)
(check-sat)
(pop 1)

(push 1)
(assert (= (store (store (store a i0 v0) i1 v1) i2 v2)
           (store (store (store a i2 v2) i1 v1) i0 v0)))
(assert (= (select a j) (_ bv7 8)))
(set-info :status sat)
(check-sat)
(pop 1)

(push 1)
(assert (= (store (store (store a i0 v0) i1 v1) i2 v2)
           (store (store (store a i2 v2) i1 v1) i0 v0)))
(assert (= (select a j) (_ bv7 8)))
(set-info :status sat)
(check-sat)
(pop 1)

(push 1)
(assert (= (store (store (store a i0 v0) i1 v1) i2 v2)
           (store (store (store a i2 v2) i1 v1) i0 v0)))
(assert (= (select a j) (_ bv7 8)))
(set-info :status sat)
(check-sat)
(pop 1)
