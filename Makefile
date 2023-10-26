
precommit:
	cargo check --all-features
	cargo clippy --all-targets --all-features -- -D warnings
	cargo fmt --all -- --check

build:
	cargo build
	maturin develop

test:
	# install dependencies
	rustup component add llvm-tools-preview
	cargo install grcov

	# clean test coverage directory
	rm -rf ./target/test_coverage
	mkdir -p ./target/test_coverage

	# run tests
	CARGO_INCREMENTAL=0 RUSTFLAGS='-Cinstrument-coverage' LLVM_PROFILE_FILE='target/test_coverage/profraw/cargo-test-%p-%m.profraw' cargo test --verbose

	# generate html coverage report
	grcov . --binary-path ./target/debug/deps/ -s . -t html --branch --ignore-not-existing --ignore '../*' --ignore "/*" -o target/test_coverage/html

	# generate lcov coverage report
	grcov . --binary-path ./target/debug/deps/ -s . -t lcov --branch --ignore-not-existing --ignore '../*' --ignore "/*" -o target/test_coverage/tests.lcov


.PHONY: precommit build test
