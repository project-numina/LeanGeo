FROM ubuntu:latest

WORKDIR /LeanEuclid
COPY . .

# Install dependencies.
RUN apt-get update && apt-get install -y curl git cmake m4 python3-venv python3-pip

# Build and Install CVC5.
RUN git clone https://github.com/cvc5/cvc5
WORKDIR cvc5
RUN ./configure.sh --auto-download
WORKDIR build
RUN make -j8
RUN make install
WORKDIR /LeanEuclid

# Build and Install Z3.
RUN git clone https://github.com/Z3Prover/z3
WORKDIR z3
RUN python3 scripts/mk_make.py
WORKDIR build
RUN make -j8
RUN make install
WORKDIR /LeanEuclid

# Install smt-portfolio in venv.
RUN python3 -m venv venv
RUN venv/bin/pip install smt-portfolio
ENV PATH="/LeanEuclid/venv/bin:${PATH}"

# Install elan.
ENV ELAN_HOME="/.elan"
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y

# Build the Lean project.
RUN lake script run check
RUN lake exe cache get
RUN lake build SystemE Book UniGeo E3
