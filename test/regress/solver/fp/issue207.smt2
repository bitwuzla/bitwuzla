(set-info :smt-lib-version 2.6)
(set-info :license |https://www.gnu.org/licenses/gpl-3.0.html|)
(set-logic QF_FP)
(set-option :produce-models true)
(set-info :source |Florian Schanda|)
(set-info :category crafted)
(set-info :status sat)

;; they can all return the same thing

(declare-const x Float32)
(declare-const y Float32)
(assert (and (fp.isZero x)
             (fp.isZero y)))
(assert (distinct x y))

(assert (= (fp.min x y)
           (fp.min y x)
           (fp.max x y)
           (fp.max y x)))
(check-sat)
(exit)
