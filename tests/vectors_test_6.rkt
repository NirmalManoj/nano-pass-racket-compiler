(let ([t (vector 1 (vector 10 #t 10 #f #f) 5 7 9 9 9 7 7 5 3 (vector #t 10 #f #f))])
    (+ (vector-length t) (vector-ref (vector-ref t 1) 2)) ; 12 + 10
)
