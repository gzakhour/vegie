(datatype nat zero (succ nat))

(type add (nat nat) nat)

(def add (?a ?b)
  (case ?a
    (zero ?b)
    ((succ ?x) (succ (add ?x ?b)))))

(theorem 0+x=x ((?x nat))
  (add zero ?x)
  ?x)

(eval (add (succ zero) (succ (succ zero))))
