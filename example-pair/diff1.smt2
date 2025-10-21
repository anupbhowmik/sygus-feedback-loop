(set-logic LIA)

(define-fun f ((x Int) (y Int)) Int
  (- x y))
(declare-fun x () Int)
(declare-fun y () Int)

(assert (
  not 
    (= (f x y) (f y x))
  )
)

(check-sat)

(get-model)