
(datatype nat zero (succ nat))

(type add (nat nat) nat)
(type mult (nat nat) nat)
(type square (nat) nat)
(type double (nat) nat)

(def square (?x) (mult ?x ?x))
(def double (?x) (add ?x ?x))

(axiom add_comm ((?x nat) (?y nat))
  (add ?x ?y) (add ?y ?x))

(axiom mult_comm ((?x nat) (?y nat))
  (mult ?x ?y) (mult ?y ?x))

(axiom add_assoc ((?x nat) (?y nat) (?z nat))
  (add ?x (add ?y ?z))
  (add (add ?x ?y) ?z))

(axiom mult_add_dist ((?x nat) (?y nat) (?z nat))
  (mult ?x (add ?y ?z))
  (add (mult ?x ?y) (mult ?x ?z)))

(theorem test ((?x nat) (?y nat) (?z nat))
  (add ?x (add ?y ?z))
  (add ?y (add ?x ?z)))

; 4 -> 8 -> 10 -> 6
;   add 0 (add 1 2)
; = add (add 0 1) 2   [add_comm]
; = add (add 1 0) 2   [congr add add_comm id]
; = add 1 (add 0 2)   [add_assoc <-]

; (theorem binomial ((?x nat) (?y nat))
;   (square (add ?x ?y))
;   (add (square ?x) (add (double (mult ?x ?y)) (square ?y))))
