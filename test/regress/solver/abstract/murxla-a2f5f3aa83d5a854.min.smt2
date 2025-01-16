(set-option :abstraction-ite true)
(set-option :abstraction true)
(declare-const __ Bool)
(declare-const x (Array Bool Float64))
(set-info :status sat)
(check-sat-assuming
 ((fp.isNaN
   (select
    (store
     x
     false
     (fp.min
      (select x false)
      (_ +zero 11 53)
      ))
    __)))
)
