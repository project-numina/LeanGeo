#!/usr/bin/env bash
set -x
echo "hi"

echo "installing lean"
pushd ~
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain v4.15.0 -y
source $HOME/.elan/env
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