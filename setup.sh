#!/usr/bin/env bash
set -x
echo "hi"

echo "installing lean"
pushd ~
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain v4.15.0 -y
source $HOME/.elan/env
popd

# Build and Install CVC5.
echo "installing cvc5"
git clone https://github.com/cvc5/cvc5
pushd cvc5
./configure.sh --auto-download
pushd build
make -j8
make check
sudo make install
popd
popd


# Build and Install Z3.
echo "installing z3"
git clone https://github.com/Z3Prover/z3
pushd z3
python scripts/mk_make.py
pushd build
make -j8
sudo make install
popd
popd

sudo apt update
sudo apt install -y clang libc++-dev

export CC=clang
export CXX=clang++

# Install smt-portfolio in venv.
pip install smt-portfolio

# Build the Lean project.
# lake script run check
lake update
lake exe cache get
lake build
lake build cvc5 SystemE mathlib LeanGeo

python patch.py --LeanEuclid_path $(pwd)
lake update REPL
lake build repl