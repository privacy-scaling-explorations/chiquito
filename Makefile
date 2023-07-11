
precommit:
	cargo check --all-features
	cargo clippy --all-targets --all-features -- -D warnings
	cargo fmt --all -- --check

.PHONY: precommit
