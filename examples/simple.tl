(datatype nat zero (succ nat))

(type one () nat)
(def one () (succ zero))

(type const (nat nat) nat)
(def const (?x ?y) ?x)

(theorem const_ignores_second ((?x nat) (?y nat))
  (const ?x ?y)
  ?x)

(eval one)

(theorem one_is_succ_zero ()
  (succ zero)
  one)

(theorem with_case1 ((?n nat))
  (case ?n
    (zero zero)
    ((succ ?x) zero))
  zero)

(theorem with_case2 ((?n nat))
  (case ?n
    (zero zero)
    ((succ ?x) (succ ?x)))
  ?n)

(theorem with_case3_false ((?n nat))
  (case ?n
    (zero zero)
    ((succ ?x) (succ ?x)))
  (succ ?n))

(type sign (nat) nat)
(def sign (?n) (case ?n (zero zero) ((succ ?x) (succ zero))))

;; this theorem requires 4 iterations
;; (PS: if induction/cases were done before expansion then replacing the
;; `(succ zero)` rhs with `one` will make an unknown theorem.
;; Reason: it will be impossible to unfold the `one`
(theorem def_with_case ((?n nat))
  (case ?n
    (zero one)
    ((succ ?a) (sign ?n)))
  one)
