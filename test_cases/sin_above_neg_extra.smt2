(set-logic ALL)

(declare-const t Real)

(assert (<= t (- 0.6)))
(assert (>= t (- 0.61)))

(assert (<= (sin t) (- 0.5)))
(assert (>= (sin t) (- 0.51)))

(check-sat)
