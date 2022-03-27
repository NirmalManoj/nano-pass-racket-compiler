(let ([x (if (and #f (or #f #t)) (+ 2 3) (- 8))])
  (let ([x (+ x x)])
    (+ x 31)))