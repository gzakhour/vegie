RUSTFILES=$(wildcard src/*.rs) $(wildcard src/lang/*.rs)

STATICFLAGS=-C target-feature=+crt-static --target x86_64-unknown-linux-musl

all: vegie vegie-linux-x86_64

vegie-linux-x86_64: $(RUSTFILES)
	rustc -O --edition=2024 -o vegie-linux-x86_64 $(STATICFLAGS) src/main.rs
	strip vegie-linux-x86_64

vegie: $(RUSTFILES)
	rustc -O --edition=2024 -o vegie src/main.rs
	strip vegie

clean:
	rm -f vegie vegie-linux-x86_64
	rm -rf target
