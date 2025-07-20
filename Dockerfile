FROM ubuntu:latest

WORKDIR /LeanEuclid
COPY . .

# Install elan.
ENV ELAN_HOME="/.elan"
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y

# install cpp deps
RUN apt install clang libc++-dev cvc5 libcvc5-dev

# Build the Lean project.
RUN lake script run check
RUN lake update
RUN lake exe cache get
RUN lake build SystemE Book UniGeo E3 mathlib REPL LeanGeo
