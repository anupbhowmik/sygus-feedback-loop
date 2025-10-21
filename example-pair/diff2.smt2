(set-logic LIA)

(define-fun f ((x Int) (y Int)) Int
  (- x y))
(declare-fun x () Int)
(declare-fun y () Int)

(assert (
  not 
    (or (= (- x y) (f x y)) (= (- y x) (f x y)))
  )
)

(check-sat)

(get-model)