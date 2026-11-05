# Ariadne VST prototype: VST 2.17 (Verifiable C) + CompCert 3.18
# (clightgen) on Rocq 9.0.1, the same Rocq as the M0 image (../env).
#
# Version choices (see Ariadne/vst/README.md):
#   coq-vst 2.17 needs coq >= 9.0 & < 9.4 and coq-compcert 3.18.x;
#   coq-compcert 3.18 accepts coq < 9.3 and installs clightgen
#   (its opam build passes -clightgen).  Same base image as M0, so the
#   two toolchains could later share one image.

FROM rocq/rocq-prover:9.0.1-native-ocaml-4.14.2@sha256:9cdd1f5e80653c8b527bc841df99ef24d1190d3be1e442f7118103221793b594

USER rocq
WORKDIR /home/rocq
# The base image pins ocamlfind 1.9.6; coq-lsp 0.2.5 needs >= 1.9.8
# (same fix as M0).
RUN opam update -q \
 && opam pin remove -n ocamlfind \
 && opam install -y \
      ocamlfind.1.9.8 \
      coq-compcert.3.18 \
      coq-vst-zlist.2.13 \
      coq-vst.2.17 \
      coq-hammer-tactics.1.3.2+9.0 \
      coq-lsp.0.2.5+9.0 \
 && opam clean -a -c -s --logs

# ---------- SMTCoq (plan §9.2 Q10) ----------
# SMTCoq has no opam release for Rocq 9, so it is built from the
# `with-trakt-rocq-9.0v1` branch at a fixed commit (2026-06-10).  That
# branch needs Trakt (goal preprocessing for Z, nat, ...), built at the
# Trakt commit of the same day, on rocq-elpi 3.4.0 + elpi 3.7.1 (a pair
# listed in that Trakt commit's flake.nix for Rocq <= 9.2).  Trakt
# builds with dune's `(using rocq 0.11)` mode, which calls
# `rocq --config`; Rocq 9.0 only has `rocq c -config`, so a shim
# (smtcoq/rocq-config-shim.sh) maps one to the other during that build.
# Solvers, as SMTCoq's INSTALL.md at that commit asks: the veriT
# snapshot 9f48a98 (proof production on; built from source; the
# INSTALL.md URL at lri.fr now redirects, the file moved to
# usr.lmf.cnrs.fr) and CVC4 1.6 (static Linux binary).  cvc5 1.0.7 is
# only for SMTCoq's `abduce` tactic and is not installed.
# veriT is 2016 C: GCC 12 defaults to -fno-common, so it needs -fcommon.
# These layers come after the VST layer so that layer stays cached.
USER root
RUN apt-get update \
 && apt-get install -y --no-install-recommends bison flex libgmp-dev \
 && rm -rf /var/lib/apt/lists/*
WORKDIR /tmp/solvers
RUN curl -sSL -o veriT9f48a98.tar.gz \
      https://usr.lmf.cnrs.fr/~ckeller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz \
 && curl -sSL -o cvc4 \
      http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.6-x86_64-linux-opt \
 && printf '%s\n' \
      '89b41ada7151dac290f8bcb158ae9d1fc7ad07a362646157cb4c82c2cef0f4e5  veriT9f48a98.tar.gz' \
      '15d3adf254febf9ee2c5d2b06f01d80f02d2e27d2f87c964b5470d8596f03813  cvc4' \
    | sha256sum -c - \
 && tar xzf veriT9f48a98.tar.gz \
 && cd veriT9f48a98 && autoconf && ./configure && make CC="gcc -fcommon" \
 && install -m 755 veriT /usr/local/bin/veriT \
 && cd .. && install -m 755 cvc4 /usr/local/bin/cvc4 \
 && cd / && rm -rf /tmp/solvers

USER rocq
WORKDIR /home/rocq/src
COPY --chown=rocq smtcoq/rocq-config-shim.sh /home/rocq/src/shim/rocq
RUN curl -sSL -o smtcoq.tar.gz \
      https://github.com/smtcoq/smtcoq/archive/3df6204826a06f5025bc7408ab77855680c50367.tar.gz \
 && curl -sSL -o trakt.tar.gz \
      https://github.com/rocq-trakt/trakt/archive/c666cad53d794b0facecb7a87a6f74e6c89be088.tar.gz \
 && printf '%s\n' \
      'd5f6c3d438b883fcf54d51525d46a6b493970f51d599c8a28ca8c7cf9d629752  smtcoq.tar.gz' \
      'fb265239d350de25eea6adbd146825fc697a50a9fc930d540e4aea8dae433e0d  trakt.tar.gz' \
    | sha256sum -c - \
 && tar xzf smtcoq.tar.gz \
 && mv smtcoq-3df6204826a06f5025bc7408ab77855680c50367 smtcoq \
 && tar xzf trakt.tar.gz \
 && mv trakt-c666cad53d794b0facecb7a87a6f74e6c89be088 trakt \
 && rm smtcoq.tar.gz trakt.tar.gz \
 && opam install -y elpi.3.7.1 rocq-elpi.3.4.0 \
 && eval $(opam env) \
 && chmod +x shim/rocq \
 && (cd trakt \
     && PATH=/home/rocq/src/shim:$PATH dune build -p rocq-trakt @install \
     && PATH=/home/rocq/src/shim:$PATH dune install rocq-trakt) \
 && rm -rf shim trakt \
 && make -C smtcoq -j"$(nproc)" \
 && make -C smtcoq install \
 && opam clean -a -c -s --logs
# The source tree stays: CVC4's LFSC proofs are checked against the
# signatures shipped with SMTCoq.
ENV LFSCSIGS=/home/rocq/src/smtcoq/src/lfsc/tests/signatures/
ENV DONTSHOWVERIT=yes
WORKDIR /home/rocq
