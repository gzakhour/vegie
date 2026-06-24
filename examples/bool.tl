(datatype bool true false)

(type not (bool) bool)
(def not (?b) (case ?b (true false) (false true)))

(theorem not_true () (not true) false)
(theorem not_false () (not false) true)
(theorem not_not ((?b bool)) (not (not ?b)) ?b)


(datatype nat zero (succ nat))

(type const (nat nat) nat)
(def const (?x ?y) ?x)

(theorem const_ignores_second ((?x nat) (?y nat))
  (const ?x ?y)
  ?x)
