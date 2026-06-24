(datatype nat zero (succ nat))
(datatype bool true false)


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

(type one () nat)
(def one () (succ zero))
(theorem one_def () one (succ zero))

(theorem sign_succ_one ((?x nat))
  (sign (succ ?x)) one)

(theorem def_with_case ((?n nat))
  (case ?n
    (zero one)
    ((succ ?a) (sign ?n)))
  (succ zero))


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


(type add (nat nat) nat)
(def add (?x ?y)
  (case ?x
    (zero ?y)
    ((succ ?a) (succ (add ?a ?y)))))

(theorem add_zero_left ((?x nat))
  (add zero ?x) ?x)


(type stupid_id (nat) nat)
(def stupid_id (?x)
  (add (traverse ?x) ?x))

(theorem stupid_id_is_id ((?x nat))
  (stupid_id ?x) ?x)



(datatype 2nat (pair nat nat))

