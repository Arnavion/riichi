fn main() {
	// We don't have something like `core::simd::is_supported()`, so we have to handle it ourselves.
	// Not having vectorization is rare, so let's list targets without vectorization explicitly and have the default case assume vectorization.

	let target = std::env::var("TARGET").expect("TARGET not set");
	let use_core_simd =
		if target.starts_with("riscv") {
			let target_features = std::env::var("CARGO_CFG_TARGET_FEATURE").expect("CARGO_CFG_TARGET_FEATURE not set");
			target_features.split(',').any(|feature| feature == "zvl128b")
		}
		else {
			true
		};
	println!("cargo::rustc-check-cfg=cfg(use_core_simd)");
	if use_core_simd {
		println!("cargo::rustc-cfg=use_core_simd");
	}
}
