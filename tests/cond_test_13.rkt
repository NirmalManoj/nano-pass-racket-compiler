(let ([x (if (or #f (or #f #t)) (+ 20 3) (- 17))])
  (let ([x (+ x x)])
    (+ x 31)))