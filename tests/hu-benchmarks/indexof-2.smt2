;unsat

(set-logic QF_S)

(declare-fun x () String)
(declare-const t Int)


(assert(str.in.re x (str.to.re "abcabc")))
(assert(= (str.indexof x "abc" 1) t))	
(assert (> t 3))

(check-sat)
