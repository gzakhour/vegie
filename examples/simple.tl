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

(theorem add_succ_swap_at_zero ()
  (add zero (succ zero))
  (add (succ zero) zero))

(theorem add_succ_swap_zero ((?x nat))
  (add ?x (succ zero))
  (add (succ ?x) zero))

; TODO the order here matterns!
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
  (add ?x (add ?y ?z)))

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



(type mult (nat nat) nat)
(def mult (?x ?y)
  (case ?x
    (zero zero)
    ((succ ?x) (add ?y (mult ?x ?y)))))


(theorem mult_def_zero ((?x nat))
  (mult zero ?x)
  zero)

; order matters
(theorem mult_def_succ ((?x nat) (?y nat))
  (add ?y (mult ?x ?y))
  (mult (succ ?x) ?y)
)

(theorem mult_zero_right ((?x nat))
  (mult ?x zero)
  zero)

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

; (theorem mult_comm ((?x nat) (?y nat))
;   (mult ?x ?y)
;   (mult ?y ?x)
; )
