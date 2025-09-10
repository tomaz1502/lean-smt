(set-logic ALL)

(declare-const t Real)

(assert (>= t (- 0.2)))
(assert (<= t (- 0.1)))

(assert (<= (sin t) (- 0.03)))
(assert (>= (sin t) (- 0.04)))

(check-sat)
