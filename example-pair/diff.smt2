(set-logic LIA)

(define-fun f ((x Int) (y Int)) Int (ite (<= x y) (- y x) (+ x y)))

(declare-fun x () Int)
(declare-fun y () Int)

(assert (not
    (and (= (f x y) (f y x))
         (or (= (- x y) (f x y)) (= (- y x) (f x y)))
    )
))

(declare-fun c1 () Bool)
(declare-fun c2 () Bool)

(assert (= c1 (= (f x y) (f y x))))
(assert (= c2 (or (= (- x y) (f x y)) (= (- y x) (f x y)))))

(assert (not
    (and c1 c2
    )
))

(check-sat)
(get-model)