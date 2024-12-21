(declare-fun AA ((Array Bool Bool)) (Array Bool Bool))
(declare-fun bA (Bool) (Array Bool Bool))
(declare-fun Ab ((Array Bool Bool)) Bool)
(define-fun A () (Array Bool Bool) (bA false))
(assert (Ab (AA A)))
(assert
 (select
  (ite
   (select A (Ab A))
   (store
    (AA (store A (Ab A) (Ab A)))
    (Ab A)
    (Ab A)
   )
   (bA (Ab A))
  )
  (Ab A)))
(set-info :status sat)
(check-sat)
