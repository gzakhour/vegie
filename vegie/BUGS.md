

* Proof is not unfolding the definition of `add`, it just starts with `(cases ...)`
```
(theorem 0+0=0 ()
  (add zero zero)
  zero)
```

**FIX**: Need case-reduce where scrutinee = constructor app

* Panic during proof extraction, even though theorem proven true
```
(theorem x+0=0 ((?x nat))
  (add ?x zero)
  ?x)
```


* unknown theorem `add_zero_x'` when a slightly simpler form is proven:
```
(theorem 0+0=0 () (add zero zero) zero)
(proof ...)

(theorem add_zero_x' ((?x nat)) (add (add zero zero) ?x) ?x)
(no-proof)

(theorem add_zero_x ((?x nat)) (add zero ?x) ?x)
(proof ...)
```
