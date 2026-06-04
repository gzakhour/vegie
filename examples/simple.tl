(datatype nat zero (succ nat))
(datatype bool true false)

(type not (bool) bool)
(def not (?b) (case ?b (true false) (false true)))

(theorem not_true () (not true) false)
(theorem not_false () (not false) true)
(theorem not_not ((?b bool)) (not (not ?b)) ?b)

(type even (nat) bool)
(type odd (nat) bool)

(def even (?x) (case ?x (zero true) ((succ ?y) (not (odd ?y)))))
(def odd (?x) (case ?x (zero false) ((succ ?y) (not (even ?y)))))

(theorem even_zero () (even zero) true)
(theorem even_succ ((?x nat)) (even (succ ?x)) (not (odd ?x)))

(theorem odd_zero () (odd zero) false)
(theorem odd_succ ((?x nat)) (odd (succ ?x)) (not (even ?x)))

(theorem even_plus_2 ((?x nat))
  (even (succ (succ ?x)))
  (even ?x))

; (theorem even_succ_odd ((?x nat))
;   (even (succ ?x))
;   (not (even ?x)))


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

(theorem sign_succ_one ((?x nat))
  (sign (succ ?x)) one)

(theorem def_with_case ((?n nat))
  (case ?n
    (zero one)
    ((succ ?a) (sign ?n)))
  (succ zero))


(type add (nat nat) nat)
(def add (?x ?y)
  (case ?x
    (zero ?y)
    ((succ ?a) (succ (add ?a ?y)))))

(theorem add_zero_left ((?x nat))
  (add zero ?x)
  ?x)

(theorem add_zero_right ((?x nat))
  (add ?x zero)
  ?x)

(theorem add_succ ((?x nat) (?y nat))
  (succ (add ?x ?y))
  (add (succ ?x) ?y)
)

(theorem add_succ_left ((?x nat) (?y nat))
  (succ (add ?x ?y))
  (add (succ ?x) ?y)
)

(theorem add_succ_right ((?x nat) (?y nat))
  (succ (add ?x ?y))
  (add ?x (succ ?y))
)

(theorem add_comm ((?x nat) (?y nat))
  (add ?x ?y)
  (add ?y ?x)
)

(theorem add_assoc_succ0 ((?x nat) (?y nat) (?z nat))
  (add (succ ?x) (add ?y ?z))
  (add ?x (add (succ ?y) ?z)))

(theorem add_assoc_succ1 ((?x nat) (?y nat) (?z nat))
  (add (succ ?x) (add ?y ?z))
  (add ?x (add ?y (succ ?z))))


(theorem add_assoc_lemma0 ((?y nat) (?z nat))
  (add zero (add ?y ?z))
  (add (add zero ?y) ?z))

(theorem add_assoc_lemma1 ((?x nat) (?y nat) (?z nat))
  (add (succ ?x) (add ?y ?z))
  (succ (add ?x (add ?y ?z)))
)

(theorem add_comm_assoc ((?x nat) (?y nat) (?z nat))
  (add ?x (add ?y ?z))
  (add (add ?x ?z) ?y))

(theorem add_assoc ((?x nat) (?y nat) (?z nat))
  (add (add ?x ?y) ?z)
  (add ?x (add ?y ?z)))






(type traverse (nat) nat)
(def traverse (?x)
  (case ?x
    (zero zero)
    ((succ ?x) (traverse ?x))))

(theorem traverse_is_zero ((?x nat))
  (traverse ?x) zero)


(type expensive_id (nat) nat)
(def expensive_id (?x)
  (case ?x
    (zero zero)
    ((succ ?a) (succ (expensive_id ?a)))))

(theorem expensive_id_is_just_id ((?x nat))
  (expensive_id ?x) ?x)

(type stupid_id (nat) nat)
(def stupid_id (?x)
  (add (traverse ?x) ?x))

(theorem stupid_id_is_id ((?x nat))
  (stupid_id ?x) ?x)



(datatype 2nat (pair nat nat))

(type mult (nat nat) nat)
(def mult (?x ?y)
  (case ?x
    (zero zero)
    ((succ ?x) (add ?y (mult ?x ?y)))))


(theorem mult_def_zero ((?x nat))
  (mult zero ?x) zero)

(theorem mult_zero_right ((?x nat))
  (mult ?x zero) zero)

; order matters
(theorem mult_def_succ ((?x nat) (?y nat))
  (add ?y (mult ?x ?y))
  (mult (succ ?x) ?y)
)

(theorem mult_one_unit_left ((?x nat))
  (mult one ?x)
  ?x)

(theorem mult_one_unit_right ((?x nat))
  (mult one ?x)
  ?x)

(theorem mult_succ_def ((?x nat) (?y nat))
  (mult (succ ?x) ?y)
  (add ?y (mult ?x ?y))
)

(theorem mult_comm ((?x nat) (?y nat))
  (mult ?x ?y)
  (mult ?y ?x)
)

(theorem mult_add_dist ((?x nat) (?y nat) (?z nat))
  (mult ?x (add ?y ?z))
  (add (mult ?x ?y) (mult ?x ?z)))

(theorem mult_assoc ((?x nat) (?y nat) (?z nat))
  (mult ?x (mult ?y ?z))
  (mult (mult ?x ?y) ?z))

(type square (nat) nat)
(def square (?x) (mult ?x ?x))
(theorem square_def ((?x nat)) (square ?x) (mult ?x ?x))

(type double (nat) nat)
(def double (?x) (add ?x ?x))
(theorem double_def ((?x nat)) (double ?x) (add ?x ?x))

(type cube (nat) nat)
(def cube (?x) (mult ?x (mult ?x ?x)))
(theorem cube_def ((?x nat)) (cube ?x) (mult ?x (mult ?x ?x)))

(theorem binomial ((?x nat) (?y nat))
  (square (add ?x ?y))
  (add (square ?x) (add (double (mult ?x ?y)) (square ?y))))

(type sum_up_to (nat) nat)
(def sum_up_to (?x)
  (case ?x
    (zero zero)
    ((succ ?x) (add (succ ?x) (sum_up_to ?x)))))

(theorem sum_up_to_def0 ()
  (sum_up_to zero) zero)

(theorem sum_up_to_def1 ((?x nat))
  (add (succ ?x) (sum_up_to ?x))
  (sum_up_to (succ ?x)))

(theorem gauss_formula ((?x nat))
  (double (sum_up_to ?x))
  (mult ?x (succ ?x)))

(type sum_cubes_up_to (nat) nat)
(def sum_cubes_up_to (?x)
  (case ?x
    (zero zero)
    ((succ ?x) (add (cube (succ ?x)) (sum_cubes_up_to ?x)))))

(theorem sum_cubes_up_to0 ()
  (sum_cubes_up_to zero)
  zero)

(eval (sum_cubes_up_to (succ (succ zero))))

(theorem sum_cubes_up_to1 ((?x nat))
  (add (cube (succ ?x)) (sum_cubes_up_to ?x))
  (sum_cubes_up_to (succ ?x))
)

(theorem nicomachus ((?x nat))
  (double (double (sum_cubes_up_to ?x)))
  (square (sum_up_to ?x)))


