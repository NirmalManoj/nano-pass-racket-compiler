 (define
 (id [a : (Vector Integer)] [b : Integer]
  [c : Integer] [d : Integer] [e : Integer]
  [f : Integer] [g : Integer] [h : Integer]) : Integer
 (+ (vector-ref a 0) (+ b (+ c (+ d (+ e (+ f (+ g h))))))))

 (id 1 2 3 4 5 6 7 14)