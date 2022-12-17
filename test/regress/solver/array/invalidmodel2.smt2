(set-logic QF_ABV)
(set-info :status sat)
(declare-fun _substvar_713_ () (_ BitVec 8))
(declare-fun _substvar_714_ () (_ BitVec 32))
(declare-fun _substvar_859_ () (_ BitVec 32))
(declare-fun _substvar_860_ () (_ BitVec 32))
(declare-fun _substvar_861_ () (_ BitVec 32))
(declare-fun _substvar_862_ () (_ BitVec 32))
(declare-fun mem_35_202 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun mem_35_196 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun mem_35_192 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun mem_35_188 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun mem_35_184 () (Array (_ BitVec 32) (_ BitVec 8)))
(assert
 (= (_ bv0 8)
  (select
   (store
    (store mem_35_192 (_ bv4 32) _substvar_713_) (_ bv1 32) (_ bv0 8)) (_ bv0 32))))
(assert (= _substvar_714_ (bvadd _substvar_859_ (_ bv4 32))))
 
(assert
 (= _substvar_713_
  (bvor
    (select mem_35_192 (bvadd _substvar_714_ (_ bv2 32)))
    (select mem_35_192 (bvadd _substvar_714_ (_ bv3 32))))
  )
)
(assert (= mem_35_196 (store mem_35_202 _substvar_861_ (_ bv0 8))))
(assert (= mem_35_192 (store mem_35_196 (_ bv0 32) (_ bv0 8))))
(assert
 (= _substvar_859_
    (bvor
     (concat (_ bv0 24) (select mem_35_196 (bvadd _substvar_860_ (_ bv0 32))))
     (bvshl
      (concat (_ bv0 24) (select mem_35_196 (bvadd _substvar_860_ (_ bv1 32))))
      (_ bv8 32))) )
)
(assert (= _substvar_860_ (bvadd _substvar_861_ (_ bv8 32))))
(assert (= _substvar_861_ (bvsub _substvar_862_ (_ bv4 32))))
(assert (= (_ bv0 8) (select mem_35_202 (bvadd _substvar_862_ (_ bv1 32)))))
(check-sat)
(exit)
