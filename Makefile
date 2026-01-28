.PHONY: clean default outdated print test

default: test

clean:
	rm -rf Cargo.lock target/

outdated:
	cargo-outdated

print:
	git status --porcelain

test: src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
	cargo test --workspace
	cargo clippy --workspace --tests --examples
	cargo machete

src/decompose/honors.generated.rs src/decompose/numbers.generated.rs:
	cargo run --release -p riichi-decompose-lut -- src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
