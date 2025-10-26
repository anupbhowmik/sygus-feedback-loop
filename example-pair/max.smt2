(set-logic LIA)

; Variable declarations
(declare-const x Int)
(declare-const y Int)

; Synthesized functions
(define-fun max2 ((x Int) (y Int)) Int (ite (>= (+ x (* (- 1) y)) 0) x y))

(check-sat)
(get-model)