(set-logic QF_BVFP)
(assert (= (fp.div RNA (fp #b1 #xe #b11111111111) (fp #b1 #xb #b01100000000)) (fp #b0 #xa #b01110100010)))
(set-info :status sat)
(check-sat)
