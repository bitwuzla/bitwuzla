;; This can arise from program analysis of programs checking for
;; integer overflow with constructs like:
;; void *calloc(size_t a, size_t b)
;; {
;;     if( ((size_t)-1) / a < b ){ errno = ENOMEM; return NULL; }
;;     return memset(malloc(a*b), 0, a*b);
;; }
;; The answer is unsat.
(set-logic QF_BV)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (not (=
              ((_ extract 63 32)
               (bvmul ((_ zero_extend 32) a)
                      ((_ zero_extend 32) b)))
              #x00000000)))
(assert (bvuge (bvudiv #xffffffff a) b))
(check-sat)
(exit)
