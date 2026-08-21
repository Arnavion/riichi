.PHONY: clean default outdated print test test-host test-rv test-rvv

DECOMPOSE_LUTS = src/decompose/numbers.generated.rs

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

test-host: $(DECOMPOSE_LUTS)
	cargo test --quiet --workspace

test-rv: $(DECOMPOSE_LUTS)
	CARGO_TARGET_DIR=target-rv \
		QEMU_CPU='rv64,zca=true,zcb=true,zicond=true' \
		cargo test --quiet --workspace --target riscv64gc-unknown-linux-gnu

test-rvv: $(DECOMPOSE_LUTS)
	CARGO_TARGET_DIR='target-rvv' \
		CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS='-Z llvm-target-feature=+v,+zvbb -C unsafe-allow-abi-mismatch=llvm-target-feature' \
		CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTDOCFLAGS='-Z llvm-target-feature=+v,+zvbb -C unsafe-allow-abi-mismatch=llvm-target-feature' \
		QEMU_CPU='rv64,zca=true,zcb=true,zicond=true,v=true,zvbb=true,rvv_ta_all_1s=on,rvv_ma_all_1s=on' \
		cargo test --quiet --workspace --target riscv64gc-unknown-linux-gnu

test-x86_64: $(DECOMPOSE_LUTS)
	CARGO_TARGET_DIR=target-x86_64 \
		CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS='-C target-cpu=native' \
		cargo test --quiet --workspace --target x86_64-unknown-linux-gnu

$(DECOMPOSE_LUTS) &:
	cargo run --release -p riichi-decompose-lut -- $(DECOMPOSE_LUTS)
