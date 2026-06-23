RUSTFILES=$(wildcard src/*.rs) $(wildcard src/lang/*.rs)

vegie: $(RUSTFILES)
	rustc -O --edition=2024 -o vegie src/main.rs
