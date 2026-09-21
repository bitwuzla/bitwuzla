; ignore output
;
; Tripwire for combining the eq/distinct decision heuristics with interpolation.
; Unlike the ADC propagator, these are not disabled by Options::finalize(), and
; process_pending_{eq,distinct}_heuristics() only bails out for an unpatched
; CaDiCaL. They connect CaDiCaL's external propagator and mark the bits of their
; terms as observed.
;
; Observing a variable that was weakened by bounded variable elimination
; restores its clauses, and restored clauses reach add_original_clause()
; without a current AIG id and have to be skipped.
;
; Below, the const array equality lemma registers eq and distinct decision
; heuristics for the store elements and indices. The two weak clauses pull
; those into the CNF of the first SAT call and the multiplication gives CaDiCaL
; enough conflicts to run elimination there, so registering the heuristics in
; the lemma round restores clauses right away.
(set-logic QF_ABV)
(set-option :produce-interpolants true)
(declare-const c (Array (_ BitVec 2) (_ BitVec 4)))
(declare-const i0 (_ BitVec 2))
(declare-const i1 (_ BitVec 2))
(declare-const v0 (_ BitVec 4))
(declare-const v1 (_ BitVec 4))
(declare-const a (_ BitVec 14))
(declare-const b (_ BitVec 14))
(assert (! (= (store (store ((as const (Array (_ BitVec 2) (_ BitVec 4))) #b0000) i0 v0) i1 v1)
              c) :named A))
(assert (= c ((as const (Array (_ BitVec 2) (_ BitVec 4))) #b0001)))
(assert (or (= v0 #b1010) (= ((_ extract 12 12) a) #b1) (= ((_ extract 12 12) b) #b0)))
(assert (or (= i1 #b01) (= ((_ extract 2 2) a) #b1) (= ((_ extract 2 2) b) #b0)))
(assert (= (bvmul ((_ zero_extend 14) a) ((_ zero_extend 14) b)) (_ bv132822709 28)))
(set-info :status unsat)
(check-sat)
(get-interpolant (A))
