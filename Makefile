.PHONY: clean default outdated print test

default: test

clean:
	rm -rf Cargo.lock target/ target-rv/ target-rvv/ target-x86_64/

outdated:
	cargo-outdated

print:
	git status --porcelain

test: test-host test-rv test-rvv test-x86_64
	cargo clippy --workspace --tests --examples
	cargo machete

test-host: src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
	cargo test --workspace

test-rv: src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
	CARGO_TARGET_DIR=target-rv \
		cargo test --workspace --target riscv64gc-unknown-linux-gnu

test-rvv: src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
	CARGO_TARGET_DIR=target-rvv \
		CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS='-C target-feature=+v' \
		CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTDOCFLAGS='-C target-feature=+v' \
		cargo test --workspace --target riscv64gc-unknown-linux-gnu

test-x86_64: src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
	CARGO_TARGET_DIR=target-x86_64 \
		CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS='-C target-cpu=x86-64-v4 -C target-feature=+avx512vbmi2' \
		cargo test --workspace --target x86_64-unknown-linux-gnu

src/decompose/honors.generated.rs src/decompose/numbers.generated.rs:
	cargo run --release -p riichi-decompose-lut -- src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
