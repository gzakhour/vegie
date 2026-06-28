# Vegie

Vegie is a proof-of-concept automated inductive theorem prover built around [Versioned E-Graphs](https://doi.org/10.1145/3808249) that is capable of proof production.

Vegie has no dependencies except for a 2024 Rust compiler.
You can either run the usual `cargo build` or use `make` to produce two binaries: a fast dynamically-linked binary for your system or a (potentially slower) statically-linked binary for x86-64 Linux with musl included.

You can read `examples/nicomachus.tl` for examples on how to write definitions and theorems.
The error messages in Vegie are coarse but should point you roughly to where an error is.

If you run `./vegie examples/nicomachus.tl` you should see an output telling you all theorems were proven.
In `out/proofs/*` you will find the proofs of all the theorems in the file.
And in `out/dot/*` you will find the proof graphs for every theorem in DOT format.
You can view these conveniently with `xdot out/dot/nicomachus.dot` (e.g.)
