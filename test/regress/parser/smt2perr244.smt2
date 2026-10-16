(declare-const x Float32)
(assert (fp.eq x ((_ to_fp_unsigned 8 24) RNE 5)))
