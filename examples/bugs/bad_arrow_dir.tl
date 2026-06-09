; NOT A BUG ANYMORE: THE DIRECTIONS IN THE REWRITE ARE CORRECT

(datatype nat zero (succ nat))

(type add (nat nat) nat)

(def add (?a ?b)
  (case ?a
    (zero ?b)
    ((succ ?x) (add ?x (succ ?b)))))

(theorem 0+0=0 () (add zero zero) zero)
(theorem 0+0=0_forwards  () (add zero zero) zero)
(theorem 0+0=0_backwards () zero (add zero zero))
