from convert import convert_sygus_to_smt2_per_constraint

spec = """
(set-logic LIA)

(synth-fun eq_1 ( (x Int) (y Int)  ) Int)

(define-fun im (( b1 Bool ) (b2 Bool ) (b3 Bool )) Bool ( or ( and b1 b2 ) ( and (not b1 ) b3 ) ) )
(define-fun plus_2 ((b1 Int) (b2 Int)) Int ( + b1 b2))
(define-fun plus_3 ((b1 Int) (b2 Int) (b3 Int)) Int ( +  ( + b1 b2) b3))
(define-fun plus_4 ((b1 Int) (b2 Int) (b3 Int) (b4 Int)) Int ( +  ( plus_3  b1 b2 b3) b4))
(define-fun plus_5 ((b1 Int) (b2 Int) (b3 Int) (b4 Int) (b5 Int)) Int (+  ( plus_4 b1 b2 b3 b4) b5))
(define-fun plus_6 ((b1 Int) (b2 Int) (b3 Int) (b4 Int) (b5 Int) (b6 Int) ) Int (+  ( plus_5 b1 b2 b3 b4  b5) b6  ))
(define-fun plus_7 ((b1 Int) (b2 Int) (b3 Int) (b4 Int) (b5 Int) (b6 Int) (b7 Int)) Int (+  ( plus_6 b1 b2 b3 b4  b5 b6 ) b7  ))
(define-fun plus_8 ((b1 Int) (b2 Int) (b3 Int) (b4 Int) (b5 Int) (b6 Int) (b7 Int) (be Int)) Int (+  ( plus_7 b1 b2 b3 b4  b5 b6 b7) be  ))
(define-fun plus_9 ((b1 Int) (b2 Int) (b3 Int) (b4 Int) (b5 Int) (b6 Int) (b7 Int) (be Int) (bn Int)) Int (+  ( plus_8 b1 b2 b3 b4  b5 b6 b7 be) bn  ))

(define-fun or3 ((b1 Bool) (b2 Bool) (b3 Bool)) Bool ( or ( or b1 b2) b3))
(define-fun two_times  ((b1 Int )) Int ( plus_2 b1 b1))
(define-fun three_times  ((b1 Int )) Int ( plus_3 b1 b1 b1))
(define-fun four_times  ((b1 Int )) Int ( plus_4 b1 b1 b1 b1))
(define-fun five_times  ((b1 Int )) Int ( plus_5 b1 b1 b1 b1 b1 ))
(define-fun six_times  ((b1 Int )) Int ( plus_6 b1 b1 b1 b1 b1 b1 ))
(define-fun seven_times ((b1 Int )) Int ( plus_7 b1 b1 b1 b1 b1 b1 b1 ))
(define-fun nine_times  ((b1 Int )) Int ( plus_9 b1 b1 b1 b1 b1 b1 b1 b1 b1))
(define-fun ten_times  ((b1 Int )) Int ( plus_9 b1 b1 b1 b1 b1 b1 b1 b1 ( plus_2 b1 b1 )))
(define-fun minus ((b1 Int)) Int ( - 0  b1 ))

(declare-var x Int ) 
(declare-var y Int ) 
 

(constraint (ite ( <= (plus_2 x y ) 1 ) 
                  ( = ( eq_1 x y ) ( ten_times ( plus_3 x y 1)))
                  ( ite  (<= (plus_2 x y ) 2  )
                          ( = ( eq_1 x y ) ( ten_times ( two_times( plus_3 x y -1))))
                          ( ite  (<= (plus_2 x y ) 3  )
                                 ( = ( eq_1 x y ) ( ten_times ( three_times( plus_3 x y 1))))
                                 ( ite  (<= (plus_2 x y ) 4  )
                                        ( = ( eq_1 x y ) ( ten_times ( four_times( plus_3 x y -1 ))))
                                        ( ite  (<= (plus_2 x y ) 5  )
                                               ( = ( eq_1 x y ) ( ten_times ( five_times( plus_3 x y 1))))
                                               ( = ( eq_1 x y ) ( ten_times ( six_times( plus_3 x y -1))))
                                         )   
                                  )   
                          )   
                    ) 
              )
)


(check-synth)


"""

solution = """
(define-fun eq_1 ((x Int) (y Int)) Int (let ((_let_1 (* (- 1) y))) (let ((_let_2 (= x (+ 3 _let_1)))) (let ((_let_3 (= x (+ (- 1) _let_1)))) (let ((_let_4 (not _let_3))) (let ((_let_5 (+ x y))) (let ((_let_6 (>= _let_5 5))) (let ((_let_7 (not _let_6))) (let ((_let_8 (>= _let_5 6))) (let ((_let_9 (>= _let_5 4))) (let ((_let_10 (>= _let_5 3))) (let ((_let_11 (>= _let_5 2))) (let ((_let_12 (= x (+ 1 _let_1)))) (let ((_let_13 (= x (+ (- 9) _let_1)))) (let ((_let_14 (= x (+ 11 _let_1)))) (ite (and _let_11 (ite _let_10 (ite _let_9 (ite _let_6 (or _let_8 _let_14) _let_12) _let_2) _let_12)) (+ (- 60) (* 60 x) (* 60 y)) (ite (ite _let_11 (and _let_10 (ite _let_9 (ite _let_6 (or _let_14 (not _let_8)) _let_13) _let_3)) _let_3) (+ 50 (* 50 x) (* 50 y)) (ite (and _let_11 (ite _let_10 (ite _let_9 (or _let_7 (ite _let_8 _let_12 _let_13)) (= x (+ 7 _let_1))) _let_12)) (+ (- 40) (* 40 x) (* 40 y)) (ite (and _let_11 (ite _let_10 (ite _let_9 (or _let_8 _let_7 _let_4) _let_4) (not _let_2))) (+ (- 20) (* 20 x) (* 20 y)) (+ 10 (* 10 x) (* 10 y)))))))))))))))))))))
"""

converted = convert_sygus_to_smt2_per_constraint(spec, solution)
# save to file for inspection
for i, content in enumerate(converted):
    with open(f"converted_constraint_{i}.smt2", "w") as f:
        f.write(content)