;sat

(set-logic QF_S)

(declare-fun x1 () String)
(declare-fun x2 () String)
(declare-fun x3 () String)
(declare-fun x4 () String)

(assert (str.in.re x1 (re.* (str.to.re "a"))))
(assert (str.in.re x2 (re.* (str.to.re "b"))))
(assert (= x3 (str.++ x1 x2)))
(assert (= x4 (str.replace x3 "ab" "")))
(assert (= (str.len x1) (str.len x2)))
(assert (> (str.len x1) (str.len x4)))

(check-sat)

