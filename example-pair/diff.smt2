(set-logic LIA)

(define-fun f ((x Int) (y Int)) Int (ite (<= x y) (- y x) (- x y)))
(declare-fun x () Int)
(declare-fun y () Int)
(assert (not
    (and (= (f x y) (f y x))
         (or (= (- x y) (f x y)) (= (- y x) (f x y)))
    )
))
(check-sat)