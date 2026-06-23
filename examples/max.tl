(datatype nat zero (succ nat))

(type max (nat nat) nat)

(def max (?x ?y)
  (case ?x
    (zero ?y)
    ((succ ?a) (case ?y
      (zero ?x)
      ((succ ?b) (succ (max ?a ?b)))))))

(theorem max_idem ((?x nat))
  (max ?x ?x)
  ?x)
