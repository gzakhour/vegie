
(datatype nat zero (succ nat))
(datatype bool true false)

(type not (bool) bool)
(def not (?b) (case ?b
  (true false)
  (false true)))

(type add (nat nat) nat)
(def add (?a ?b) (case ?a
  (zero ?b)
  ((succ ?a) (succ (add ?a ?b)))))

(theorem bool_eq_destruct_id ((?x bool))
  (case ?x
    (true true)
    (false false))
  ?x)

(type foo () bool)
(def foo () (not true))

(type one () nat)
(def one () (succ zero))


(theorem add_zero_unit_left ((?y nat))
  (add zero ?y)
  ?y)

(theorem add_zero_unit_right ((?x nat))
  (add ?x zero)
  ?x)

(theorem add_comm ((?x nat) (?y nat))
  (add ?x ?y)
  (add ?y ?x))

(theorem add_assoc ((?x nat) (?y nat) (?z nat))
  (add ?x (add ?y ?z))
  (add (add ?x ?y) ?z))

(type mult (nat nat) nat)
(def mult (?x ?y)
  (case ?x
    (zero      zero)
    ((succ ?x) (add ?y (mult ?x ?y)))
  ))


(datatype test
  (T nat bool))

(type foo2 (test) bool)
(def foo2 (?x)
  (case ?x
    ((T (succ zero) true) true)
    ((T ?x false) true)
    ((T zero true) false)
    ((T (succ (succ ?x)) true) false)
  ))


(type eight () nat)
(def eight () (mult (succ one) (mult (succ one) (succ one))))
(eval eight)


(type odd (nat) bool)
(type even (nat) bool)

(def even (?n) (case ?n
  (zero true)
  ((succ ?x) (odd ?x))))

(def odd (?n) (case ?n
  (zero false)
  ((succ ?x) (even ?x))))

(eval (even eight))
(eval (even (succ eight)))
