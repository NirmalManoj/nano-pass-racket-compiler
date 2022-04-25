 (define
 (id [a : Integer] [b : Integer]
  [c : Integer] [d : Integer] [e : Integer]
  [f : Integer] [g : Integer] [h : Integer]) : Integer
 (+ a (+ b (+ c (+ d (+ e (+ f h)))))))

 (id 1 2 3 4 5 6 7 14)