;(set-logic ALL_SUPPORTED)
;(set-option :strings-exp true)
;(set-option :produce-models true)
;(set-option :rewrite-divk true)

(declare-fun key1 () String)
(declare-fun value2 () String)
(declare-fun key2 () String)
(declare-fun value1 () String)

(assert
(and (and (and (and (and (and (and (and (and (not (not (not (= (ite (str.contains (str.substr (str.substr value1 0 (- (str.indexof value1 "=" 0) 0)) 0 (- (- (str.len (str.substr value1 0 (- (str.indexof value1 "=" 0) 0))) 1) 0)) "S") 1 0) 0)))) (not (not (= (ite (str.contains (str.substr (str.substr value1 0 (- (str.indexof value1 "=" 0) 0)) 0 (- (- (str.len (str.substr value1 0 (- (str.indexof value1 "=" 0) 0))) 1) 0)) "R") 1 0) 0)))) (not (not (= (ite (str.contains (str.substr (str.substr value1 0 (- (str.indexof value1 "=" 0) 0)) 0 (- (- (str.len (str.substr value1 0 (- (str.indexof value1 "=" 0) 0))) 1) 0)) "Q") 1 0) 0)))) (not (not (= (ite (str.contains (str.substr (str.substr value1 0 (- (str.indexof value1 "=" 0) 0)) 0 (- (- (str.len (str.substr value1 0 (- (str.indexof value1 "=" 0) 0))) 1) 0)) "P") 1 0) 0)))) (not (not (= (ite (str.contains (str.substr (str.substr value1 0 (- (str.indexof value1 "=" 0) 0)) 0 (- (- (str.len (str.substr value1 0 (- (str.indexof value1 "=" 0) 0))) 1) 0)) "O") 1 0) 0)))) (not (not (= (ite (str.contains (str.substr (str.substr value1 0 (- (str.indexof value1 "=" 0) 0)) 0 (- (- (str.len (str.substr value1 0 (- (str.indexof value1 "=" 0) 0))) 1) 0)) "N") 1 0) 0)))) (not (not (= (ite (str.contains (str.substr (str.substr value1 0 (- (str.indexof value1 "=" 0) 0)) 0 (- (- (str.len (str.substr value1 0 (- (str.indexof value1 "=" 0) 0))) 1) 0)) "M") 1 0) 0)))) (not (not (= (ite (str.contains (str.substr (str.substr value1 0 (- (str.indexof value1 "=" 0) 0)) 0 (- (- (str.len (str.substr value1 0 (- (str.indexof value1 "=" 0) 0))) 1) 0)) "L") 1 0) 0)))) (not (not (= (ite (str.contains (str.substr (str.substr value1 0 (- (str.indexof value1 "=" 0) 0)) 0 (- (- (str.len (str.substr value1 0 (- (str.indexof value1 "=" 0) 0))) 1) 0)) "K") 1 0) 0)))) (not (not (= (ite (str.contains (str.substr (str.substr value1 0 (- (str.indexof value1 "=" 0) 0)) 0 (- (- (str.len (str.substr value1 0 (- (str.indexof value1 "=" 0) 0))) 1) 0)) "J") 1 0) 0))))
)

(check-sat)

;(get-value (key1))
;(get-value (value2))
;(get-value (key2))
;(get-value (value1))