(set-option :produce-models true)
; unsupported options
(set-option :config "verbosity=0")
(set-option :foo "bar")
(set-option :bar 0)
; declarations
(declare-const a (_ BitVec 4))
(declare-const b Bool)
(assert (= a (! a :named x)))
(assert (= x #b1111))
(assert (! b :foobar asdf))
(check-sat)
(get-value (a x b))
