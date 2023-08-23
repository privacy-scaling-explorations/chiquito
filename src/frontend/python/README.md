# Quick Start
## Setup
Chiquito's Python frontend uses PyO3 and Maturin to expose Rust APIs to Python. Maturin requires the user to locally build a Python virtual environment. Run the following script to create a Python virtual environment, install required packages, and build the project.

```
# Clone this repo and its submodules
git clone --recursive https://github.com/privacy-scaling-explorations/chiquito/

# Navigate to the repository root directory 
cd chiquito

# Create a virtual environment
python3 -m venv .env

# Activate the virtual environment
source .env/bin/activate

# Install the required packages
pip install -r requirements.txt

# Build the project
maturin develop
```

If the above doesn't work, follow the guide here: https://pyo3.rs/main/getting_started#python

## Testing with examples
Run fibonacci.py example file using the following script in the virtual environment:

```
python3 example/fibonacci.py
```

Run mimc7.py example:

```
python example/mimc7.py
```

If setup is correct, all Halo2 and Chiquito Debug messages for generating and verifying proof should appear in the terminal.

# Technical Design
Python front end → Python AST object/TraceWitness → serialize to JSON string → pass JSON string to Rust using PyO3 → deserialize JSON string to Chiquito AST/TraceWitness → store AST in Rust `HashMap<UUID, AST>` → pass back UUID to Python → generate and verify proof from Python with AST UUID and TraceWitness JSON

## Notes:
Rust bindings to expose to Python, boilerplate functions, and `Deserialize` trait implementations for Rust Chiquito AST, TraceWitness, and their sub types are all in [src/frontend/python/mod.rs](https://github.com/privacy-scaling-explorations/chiquito/blob/main/src/frontend/python/mod.rs)
