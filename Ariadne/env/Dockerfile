# Ariadne M0 toolchain: Frama-C/WP + Why3 + Rocq + CoqHammer + coq-lsp.
#
# Version choices (see Ariadne/env/README.md):
#   Frama-C 33.0 needs why3 >= 1.8.2 & < 1.9; why3-coq 1.8.2 accepts
#   coq-stdlib < 9.1, so Rocq 9.0.1 is the newest usable Rocq.  The base
#   image uses plain OCaml 4.14.2 because frama-c conflicts with flambda.
#   Solver versions are the newest ones Why3 1.8.2 recognises.

FROM rocq/rocq-prover:9.0.1-native-ocaml-4.14.2@sha256:9cdd1f5e80653c8b527bc841df99ef24d1190d3be1e442f7118103221793b594

# Eprover is a prover, so it is pinned to the exact Debian revision that
# was tested; if Debian ever drops that revision the build fails instead
# of silently installing another one.  The other packages are build
# dependencies only.
USER root
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      graphviz libgmp-dev pkg-config autoconf m4 unzip curl ca-certificates \
      eprover=2.6+ds-3 clang zlib1g-dev \
 && rm -rf /var/lib/apt/lists/*

# External provers, pinned by checksum.  Vampire stays at 4.9: Vampire 5
# dropped --output_axiom_names, which CoqHammer 1.3.2 passes.
WORKDIR /tmp/provers
RUN curl -sSLO https://github.com/Z3Prover/z3/releases/download/z3-4.13.4/z3-4.13.4-x64-glibc-2.35.zip \
 && curl -sSLO https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-Linux-x86_64-static.zip \
 && curl -sSLO https://github.com/vprover/vampire/releases/download/v4.9casc2024/vampire \
 && printf '%s\n' \
      '93f91f9c6f4a00a041c19fc7a74adc1f441c8244ce70d486e19abcd89c6a014b  z3-4.13.4-x64-glibc-2.35.zip' \
      '6d44abc233980a14d72cc5809287d27c3335b1d6ee863381d0b5ffcbd0d8de56  cvc5-Linux-x86_64-static.zip' \
      'ce3b39047565a3980e3d490315ff129f0eca5f8fbd40eeb0d6850122eb295b54  vampire' \
    | sha256sum -c - \
 && unzip -q z3-4.13.4-x64-glibc-2.35.zip \
 && unzip -q cvc5-Linux-x86_64-static.zip \
 && install -m 755 z3-4.13.4-x64-glibc-2.35/bin/z3 /usr/local/bin/z3 \
 && install -m 755 cvc5-Linux-x86_64-static/bin/cvc5 /usr/local/bin/cvc5 \
 && install -m 755 vampire /usr/local/bin/vampire \
 && cd / && rm -rf /tmp/provers

USER rocq
WORKDIR /home/rocq
# The base image pins ocamlfind 1.9.6; coq-lsp 0.2.5 needs >= 1.9.8.
RUN opam update -q \
 && opam pin remove -n ocamlfind \
 && opam install -y \
      ocamlfind.1.9.8 \
      why3.1.8.2 why3-coq.1.8.2 \
      alt-ergo.2.6.4 \
      frama-c.33.0 \
      coq-hammer.1.3.2+9.0 \
      coq-lsp.0.2.5+9.0 \
 && opam clean -a -c -s --logs

COPY patch-why3-rocq9.sh coq-ariadne.drv /tmp/
RUN eval $(opam env) \
 && sh /tmp/patch-why3-rocq9.sh \
 && why3 config detect
