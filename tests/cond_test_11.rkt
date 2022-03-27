(let ([x (if (and #t (or #f #t)) (+ 2 3) (- 17 7))])
  (let ([x (+ x x)])
    (+ x 18)))