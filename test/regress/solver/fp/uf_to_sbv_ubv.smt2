(declare-const x Float16)
(assert (fp.isNaN x)) (assert (distinct ((_ fp.to_sbv 8) RNE x) ((_ fp.to_ubv 8) RNE x)))
(set-info :status sat)
(check-sat)
