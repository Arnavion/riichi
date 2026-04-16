.PHONY: clean default outdated print test test-host test-rv test-rvv

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
	cargo test --quiet --workspace

test-rv: src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
	CARGO_TARGET_DIR=target-rv \
		QEMU_CPU='rv64,zca=true,zcb=true,zicond=true' \
		cargo test --quiet --workspace --target riscv64gc-unknown-linux-gnu

test-rvv: test-rvv-128 test-rvv-256 test-rvv-512 test-rvv-1024

# Suffix is VLEN
test-rvv-%: src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
	CARGO_TARGET_DIR=target-rvv \
		CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS='-C target-feature=+v,+zvbb' \
		CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTDOCFLAGS='-C target-feature=+v,+zvbb' \
		QEMU_CPU='rv64,zca=true,zcb=true,zicond=true,zve64x=true,zvbb=true,rvv_ta_all_1s=on,rvv_ma_all_1s=on,vlen=$*' \
		cargo test --quiet --workspace --target riscv64gc-unknown-linux-gnu

test-x86_64: src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
	CARGO_TARGET_DIR=target-x86_64 \
		CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS='-C target-cpu=x86-64-v4 -C target-feature=+avx512vbmi2' \
		cargo test --quiet --workspace --target x86_64-unknown-linux-gnu

src/decompose/honors.generated.rs src/decompose/numbers.generated.rs:
	cargo run --release -p riichi-decompose-lut -- src/decompose/honors.generated.rs src/decompose/numbers.generated.rs
