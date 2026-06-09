; NOT A BUG ANYMORE: ALL THEOREMS CAN BE PROVEN

(datatype nat zero (succ nat))

(type add (nat nat) nat)
(def add (?x ?y)
  (case ?x
    (zero ?y)
    ((succ ?a) (succ (add ?a ?y)))))

(theorem 0+0=0 () (add zero zero) zero)

(theorem add_zero_x' ((?x nat)) (add (add zero zero) ?x) ?x)

(theorem add_zero_x ((?x nat)) (add zero ?x) ?x)
