; COMMAND-LINE: --nl-ext-tf-tplanes
; EXPECT: unsat
(set-logic QF_NRAT)
(set-info :status unsat)
(declare-fun x () Real)

(assert (< x 0.99))
(assert (> x 1.01))
(assert (< (exp x) 2.715))


(check-sat)
