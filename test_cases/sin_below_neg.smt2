(set-logic ALL)

(declare-const t Real)

(assert (< t (- 0.299)))
(assert (> t (- 0.301)))

(assert (< (sin t) (- 0.297)))

; (assert (>= (sin t) (- 0.7)))
; (assert (<= (sin t) (- 0.6)))

; (assert (<= t (- 0.3)))
; (assert (>= t (- 0.4)))

; (assert (< (sin t) (- t (/ (* t t t) 6.0))))

(check-sat)
