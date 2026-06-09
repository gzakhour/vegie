; NOT A BUG ANYMORE: NO MORE PANIC

(datatype nat zero (succ nat))

(type add (nat nat) nat)

(def add (?a ?b)
  (case ?a
    (zero ?b)
    ((succ ?x) (succ (add ?x ?b)))))

(theorem x+0=0 ((?x nat))
  (add ?x zero)
  ?x)

