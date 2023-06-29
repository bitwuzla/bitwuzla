(set-info :status sat)
(declare-const x (_ BitVec 2))
(declare-const x2 (Array (_ BitVec 2) (_ BitVec 2)))
(check-sat-assuming ((bvslt (_ bv0 2) x) (bvslt (bvurem x (select x2 (_ bv0 2))) (_ bv1 2))))
