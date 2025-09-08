(set-logic LIA)

; definition of max2 from sygus solver
(define-fun max2 ((x Int) (y Int)) Int (ite (>= (+ x (* (- 1) y)) 0) x y))

; variables from the original sygus problem.  SMT2 doesn't support declare-var,
; instead we represent variables as 0-arity functions.
(declare-fun x () Int)
(declare-fun y () Int)

; the conjunction of the constraints from the original sygus problems should be valid (true for all values).
; a formula is valid if its negation is unsatisfiable.
;
; Thus, we negate the conjunction of the constraints, and will either (1) get UNSAT, showing that the solution
; of max2 is correct or (2) get sat, in which case we know the solution is incorrect.
(assert (not
            (and (>= (max2 x y) x)
                 (>= (max2 x y) y)
                 (or (= x (max2 x y))
                     (= y (max2 x y)))
            )
        )
)

(check-sat)