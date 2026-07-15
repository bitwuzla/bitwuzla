; Constant array with an uninterpreted index sort in an equality. Default-value
; propagation (check_default_value -> propagate_dv) queries the cardinality of
; the index sort via type::cardinality_gt. Uninterpreted sorts must be treated
; as unbounded rather than aborting: card() previously had no case for them
; (assert(type.is_fun()) / std::bad_variant_access). The store overwrites index
; i with #x01, which cannot match the constant #x00 array, so this is unsat.
(set-logic ALL)
(set-info :status unsat)
(declare-sort U 0)
(declare-const a (Array U (_ BitVec 8)))
(declare-const i U)
(assert (= (store a i #x01) ((as const (Array U (_ BitVec 8))) #x00)))
(check-sat)
(exit)
