; (datatype nat zero (succ nat))

; (type add (nat nat) nat)
; 
; (def add (?x ?y)
;   (case ?x
;     (zero ?y)
;     ((succ ?x') (succ (add ?x' ?y)))))

; (theorem add_zero_left ((?x nat)) (add zero ?x) ?x)
; (theorem add_zero_right ((?x nat)) (add ?x zero) ?x)
;
; (theorem add_succ_left ((?x nat) (?y nat))
;   (add (succ ?x) ?y)
;   (succ (add ?x ?y)))

; (theorem add_succ_right ((?x nat) (?y nat)) (add ?x (succ ?y)) (succ (add ?x ?y)))
; 
; (theorem add_comm ((?x nat) (?y nat))
;   (add ?x ?y)
;   (add ?y ?x))


(datatype bool true false)

(type and (bool bool) bool)
(def and (?x ?y)
  (case ?x
    (true ?y)
    (false ?x)))

(theorem and_comm ((?x bool) (?y bool))
  (and ?x ?y)
  (and ?y ?x))
