; ignore output
;
; Tripwire for combining the ADC SAT propagator with interpolation, which
; Options::finalize() disables. The DISTINCT_N propagator adds clauses via
; CaDiCaL's external propagator interface. These do not come through the CNF
; encoder, thus they are not associated with an AIG id and the proof tracer
; cannot label them. The const array equality lemma below introduces a
; DISTINCT_N over the two store indices, and the propagator clause derived
; from it ends up in the proof core.
;
; With the guard removed, add_original_clause() records that clause with AIG
; id 0 and 'assert (d_cur_aig_id)' fires. Without assertions, get_interpolant()
; then finds no label for AIG id 0 and dereferences the end iterator of the
; clause label map. Dropping the 'd_cur_aig_id = 0' reset instead lets the
; clause inherit the AIG id of the previously encoded clause, which silently
; mislabels it and yields an unsound interpolant (rejected by
; --check-interpolant).
(set-logic QF_ABV)
(set-option :produce-interpolants true)
(set-option :adc-sat-propagator true)
(declare-const c (Array (_ BitVec 1) (_ BitVec 4)))
(declare-const p (_ BitVec 4))
(declare-const v (_ BitVec 4))
(assert (! (= (store (store ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x0)
                            ((_ extract 0 0) (bvmul p p)) v)
                     ((_ extract 1 1) (bvmul p p)) v)
              c) :named A))
(assert (and (= c ((as const (Array (_ BitVec 1) (_ BitVec 4))) #x1))
             (= v #x1)
             (= (bvmul p p) #x4)))
(set-info :status unsat)
(check-sat)
(get-interpolant (A))
