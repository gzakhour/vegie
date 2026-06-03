
* unknown theorem `add_zero_x'` when a slightly simpler form is proven:
```
(theorem 0+0=0 () (add zero zero) zero)
(proof ...)

(theorem add_zero_x' ((?x nat)) (add (add zero zero) ?x) ?x)
(no-proof)

(theorem add_zero_x ((?x nat)) (add zero ?x) ?x)
(proof ...)
```

* `add_comm` is not proven correct anymore...

* `and_comm` may fail without the high congr/inj/abs costs manually added
