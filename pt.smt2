(declare-fun x () Real)
(assert (= (* x x) 2))
(assert (< x 200))
(assert (> x 100))
(check-sat)

