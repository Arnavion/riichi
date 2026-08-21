# Assembly

## Compiler Explorer

```sh
podman run -it --rm -v "$PWD:/src" -v "${RUSTUP_HOME:-$HOME/.rustup}:/root/.rustup:ro" -p 10240:10240 docker.io/node bash -c 'apt update -y && apt install --no-install-recommends -y rsync && cd /src && make'
```

RV-v: `--edition 2024 -C opt-level=3 --target riscv64gc-unknown-linux-gnu -C target-feature=+b,+zca,+zcb,+zicond`

RV+v: `--edition 2024 -C opt-level=3 --target riscv64gc-unknown-linux-gnu -C target-feature=+b,+zca,+zcb,+zicond,+v,+zvbb`

x86_64: `--edition 2024 -C opt-level=3 --target x86_64-unknown-linux-gnu -C target-cpu=x86-64-v4`

## Panics

```sh
find target/riscv64gc-unknown-linux-gnu/ -name '*.rmeta' -delete; \
cargo rustc --lib --release --target riscv64gc-unknown-linux-gnu -- -C target-feature=+b,+zca,+zcb,+zicond --emit=asm=- |
    rustfilt |
    grep -Ev '^\s*\.(attribute\b|cfi_|file\b|globl\b|ident\b|p2align\b|section\b|size\b|type\b)' |
    grep -E 'panic|index|mismatch|fail' |
    wc -l
```

## Dump

```sh
find target/riscv64gc-unknown-linux-gnu/ -name '*.rmeta' -delete; \
cargo rustc --lib --release --target riscv64gc-unknown-linux-gnu -- -C target-feature=+b,+zca,+zcb,+zicond --emit=asm=- |
    rustfilt |
    grep -Ev '^\s*\.(attribute\b|cfi_|file\b|globl\b|ident\b|p2align\b|section\b|size\b|type\b)' |
    less
```
