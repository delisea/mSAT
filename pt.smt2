(declare-fun A () Bool)
(assert (and A (not A)))
(check-sat)

