
(let ([sum 0])
    (let ([i 5])
        (begin
            (while (> i 0)
                (begin
                    (let ([j i])
                        (while (> j 0)
                            (begin
                                (set! sum (+ sum j))
                                (set! j (- j 1)))))
                    (set! i (- i 1))))
            sum)))