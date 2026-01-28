# Assembly

## Compiler Explorer

```sh
podman run -it --rm -v "$PWD:/src" -v "${RUSTUP_HOME:-$HOME/.rustup}:/root/.rustup:ro" -p 10240:10240 docker.io/node bash -c "
    apt update -y &&
    apt install --no-install-recommends -y rsync &&
    cd /src &&
    make
"
```

RV-v: `--edition 2024 --extern alloc -C opt-level=3 -C target-feature=-a,-m,+auipc-addi-fusion,+forced-atomics,+ld-add-fusion,+lui-addi-fusion,+zba,+zbb,+zbs,+zca,+zcb,+zic64b,+zicntr,+zicond,+zicsr,+zkt,+zmmul,+zicclsm`

RV+v: `--edition 2024 --extern alloc -C opt-level=3 -C target-feature=-a,-m,+auipc-addi-fusion,+forced-atomics,+ld-add-fusion,+lui-addi-fusion,+zba,+zbb,+zbs,+zca,+zcb,+zic64b,+zicntr,+zicond,+zicsr,+zkt,+zmmul,+zicclsm,+v,+zvl128b`

x86_64: `--edition 2024 --extern alloc -C opt-level=3`

## Panics

```sh
rm -f target/riscv64gc-unknown-linux-gnu/release/deps/*.rmeta &&
cargo rustc --lib --release --target riscv64gc-unknown-linux-gnu -- --extern alloc -C target-feature=-a,-m,+auipc-addi-fusion,+forced-atomics,+ld-add-fusion,+lui-addi-fusion,+zba,+zbb,+zbs,+zca,+zcb,+zic64b,+zicntr,+zicond,+zicsr,+zkt,+zmmul,+zicclsm --emit=asm=- |
    rustfilt |
    grep -Ev '^\s*\.(attribute\b|cfi_|file\b|globl\b|ident\b|p2align\b|section\b|size\b|type\b)' |
    grep -E 'panic|index|mismatch|fail' |
    wc -l
```

## Dump

```sh
rm -f target/riscv64gc-unknown-linux-gnu/release/deps/*.rmeta &&
cargo rustc --lib --release --target riscv64gc-unknown-linux-gnu -- --extern alloc -C target-feature=-a,-m,+auipc-addi-fusion,+forced-atomics,+ld-add-fusion,+lui-addi-fusion,+zba,+zbb,+zbs,+zca,+zcb,+zic64b,+zicntr,+zicond,+zicsr,+zkt,+zmmul,+zicclsm --emit=asm=- |
    rustfilt |
    grep -Ev '^\s*\.(attribute\b|cfi_|file\b|globl\b|ident\b|p2align\b|section\b|size\b|type\b)' |
    less
```
