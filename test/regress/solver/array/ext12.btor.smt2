(set-logic QF_ABV)
(set-info :status sat)
(declare-const v0 (_ BitVec 2))
(declare-const v1 (_ BitVec 2))
(declare-const v2 (_ BitVec 2))
(declare-const v3 (_ BitVec 2))
(declare-const a0 (Array (_ BitVec 2) (_ BitVec 8) ))
(declare-const v4 (_ BitVec 2))
(declare-const v5 (_ BitVec 8))
(declare-const v6 (_ BitVec 2))
(declare-const v7 (_ BitVec 8))
(declare-const v8 (_ BitVec 2))
(declare-const v9 (_ BitVec 8))
(assert (= #b1 (bvand (ite (bvult (select (store (store (store a0 v4 v5) v6 v7) v8 v9) v2) (select (store (store (store a0 v4 v5) v6 v7) v8 v9) v3)) #b1 #b0) (bvand (ite (bvult (select (store (store (store a0 v4 v5) v6 v7) v8 v9) v0) (select (store (store (store a0 v4 v5) v6 v7) v8 v9) v1)) #b1 #b0) (ite (bvult (select (store (store (store a0 v4 v5) v6 v7) v8 v9) v1) (select (store (store (store a0 v4 v5) v6 v7) v8 v9) v2)) #b1 #b0)))))
(check-sat)