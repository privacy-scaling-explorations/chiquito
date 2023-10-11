
precommit:
	cargo check --all-features
	cargo clippy --all-targets --all-features -- -D warnings
	cargo fmt --all -- --check

build:
	cargo build
	maturin develop

.PHONY: precommit build
