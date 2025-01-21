(set-option :rewrite-level 0)
(declare-const v1 Bool)
(assert v1)
(assert (ite v1 v1 (not v1)))
(set-info :status sat)
(check-sat)

