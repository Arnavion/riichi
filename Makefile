.PHONY: clean default outdated print test test-host test-rv

DECOMPOSE_LUTS = src/decompose/numbers.generated.rs

default: test

clean:
	rm -rf Cargo.lock target/ target-rv-*/ target-x86_64/

outdated:
	cargo-outdated

print:
	git status --porcelain

test: test-host test-rv test-x86_64
	cargo clippy --workspace --tests --examples
	cargo machete

test-host: $(DECOMPOSE_LUTS)
	cargo test --quiet --workspace

test-rv: test-rv-128 test-rv-256 test-rv-512 test-rv-1024

# Suffix is VLEN
test-rv-%: $(DECOMPOSE_LUTS)
	CARGO_TARGET_DIR='target-rv-$*' \
	QEMU_CPU='rva23u64,rvv_ta_all_1s=on,rvv_ma_all_1s=on,vlen=$*' \
		cargo test --quiet --workspace --target riscv64a23-unknown-linux-gnu

test-x86_64: $(DECOMPOSE_LUTS)
	CARGO_TARGET_DIR=target-x86_64 \
		CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS='-C target-cpu=native' \
		cargo test --quiet --workspace --target x86_64-unknown-linux-gnu

$(DECOMPOSE_LUTS) &:
	cargo run --release -p riichi-decompose-lut -- $(DECOMPOSE_LUTS)
