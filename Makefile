vegie: $(wildcard **/*.rs)
	rustc -O --edition=2024 -o vegie src/main.rs
