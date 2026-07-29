; Regression test for issue #216: use-after-free in FunSolver::check().
; Constructing Apply re-enters register_term(), which reallocates d_applies
; and invalidates the Node reference held by check() / the Apply constructor.
;
; Ground QF_BVFP witness reaching the same defect via check-sat-assuming.
; Segfaulted deterministically (exit 139, no output) before the fix.
(set-logic QF_BVFP)
(set-info :status sat)
(check-sat-assuming ((fp.isNormal ((_ to_fp 15 113) RTP ((_ fp.to_ubv 125) RTP (fp.div RTP (fp (_ bv0 1) (_ bv0 15) (_ bv0 112)) (fp.max (fp (_ bv0 1) (_ bv0 15) (_ bv0 112)) (fp (_ bv1 1) (_ bv0 15) (_ bv0 112)))))))))
