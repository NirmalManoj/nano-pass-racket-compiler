 (define
 (id [a : (Vector Integer)] [b : Integer]
  [c : Integer] [d : (Vector Integer Integer)] [e : Integer]
  [f : Integer] [g : Integer] [h : Integer]) : Integer
 (+ (+ (vector-ref a 0) (+ b (+ c (+ (vector-ref d 1) (+ e (+ f (+ g g)))))))
    7)
 )

;;;  (id (vector 1) 2 3 4 5 6 7 (vector 42 (vector 42 7)))
 (id (vector 1) 2 3 (vector 40 4) 5 6 7 (vector 42 7))