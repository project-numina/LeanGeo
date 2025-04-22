#!/usr/bin/env bash
set -x
echo "hi"

echo "installing lean"
pushd ~
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain v4.8.0-rc2 -y
source $HOME/.elan/env
popd

# Build and Install CVC5.
echo "installing cvc5"
git clone https://github.com/cvc5/cvc5
pushd cvc5
./configure.sh
pushd build
make
make check
sudo make install
popd

# Build and Install Z3.
echo "installing z3"
git clone https://github.com/Z3Prover/z3
pushd z3
python scripts/mk_make.py
pushd build
make
sudo make isntall
popd

# Install smt-portfolio in venv.
pip install smt-portfolio

# Build the Lean project.
lake script run check
lake exe cache get
lake build SystemE Book UniGeo E3