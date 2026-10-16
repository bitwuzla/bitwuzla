(declare-const x Float32)
(assert (fp.eq x ((_ to_fp 8 24) (/ 1 3) RNE)))
