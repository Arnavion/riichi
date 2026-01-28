.PHONY: clean default outdated print test

default: test

clean:
	rm -rf Cargo.lock target/ target-rv/ target-rvv/ target-x86_64/

outdated:
	cargo-outdated

print:
	git status --porcelain

test: test-host test-rv test-rvv
	cargo clippy --workspace --tests --examples
	cargo machete

test-host:
	cargo test --workspace

test-rv:
	CARGO_TARGET_DIR=target-rv \
		cargo test --workspace --target riscv64gc-unknown-linux-gnu

test-rvv:
	CARGO_TARGET_DIR=target-rvv \
		CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS='-C target-feature=+v' \
		CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTDOCFLAGS='-C target-feature=+v' \
		cargo test --workspace --target riscv64gc-unknown-linux-gnu
