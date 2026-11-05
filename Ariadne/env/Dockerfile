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
# dependencies only, except clang-format-14 (pinned): it reformats
# preprocessed benchmarks so macro-generated code can be annotated.
USER root
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      graphviz libgmp-dev pkg-config autoconf m4 unzip curl ca-certificates \
      eprover=2.6+ds-3 clang zlib1g-dev clang-format-14=1:14.0.6-12 \
 && rm -rf /var/lib/apt/lists/*

# External provers, pinned by checksum.  Vampire stays at 4.9: Vampire 5
# dropped --output_axiom_names, which CoqHammer 1.3.2 passes.
# CoqHammer's other two ATP backends call `z3_tptp` and `cvc4`:
# - z3_tptp is Z3's TPTP front end (examples/tptp in the source tree),
#   built here against the release's static libz3.a, so it is the same
#   Z3 4.13.4 as /usr/local/bin/z3.
# - cvc4 is CVC4 1.8's static binary (CoqHammer does not call cvc5).
#   The releases/download URL of that asset returns Not Found to curl,
#   so it is fetched through the API asset URL (asset id 24275597).
WORKDIR /tmp/provers
RUN curl -sSLO https://github.com/Z3Prover/z3/releases/download/z3-4.13.4/z3-4.13.4-x64-glibc-2.35.zip \
 && curl -sSLO https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-Linux-x86_64-static.zip \
 && curl -sSLO https://github.com/vprover/vampire/releases/download/v4.9casc2024/vampire \
 && curl -sSL -o z3-src.tar.gz https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.13.4.tar.gz \
 && curl -sSL -H 'Accept: application/octet-stream' -o cvc4 \
      https://api.github.com/repos/cvc5/cvc5/releases/assets/24275597 \
 && printf '%s\n' \
      '93f91f9c6f4a00a041c19fc7a74adc1f441c8244ce70d486e19abcd89c6a014b  z3-4.13.4-x64-glibc-2.35.zip' \
      '6d44abc233980a14d72cc5809287d27c3335b1d6ee863381d0b5ffcbd0d8de56  cvc5-Linux-x86_64-static.zip' \
      'ce3b39047565a3980e3d490315ff129f0eca5f8fbd40eeb0d6850122eb295b54  vampire' \
      '4071977e66e9f3d239b7b098ceddfe62ffdf3c71e345e9524a4a5001d1f4adf3  z3-src.tar.gz' \
      'd38a79cf984592785eda41ec888d94ca107ac1f13058740238041e28c8472e51  cvc4' \
    | sha256sum -c - \
 && unzip -q z3-4.13.4-x64-glibc-2.35.zip \
 && unzip -q cvc5-Linux-x86_64-static.zip \
 && install -m 755 z3-4.13.4-x64-glibc-2.35/bin/z3 /usr/local/bin/z3 \
 && install -m 755 cvc5-Linux-x86_64-static/bin/cvc5 /usr/local/bin/cvc5 \
 && install -m 755 vampire /usr/local/bin/vampire \
 && install -m 755 cvc4 /usr/local/bin/cvc4 \
 && tar xzf z3-src.tar.gz z3-z3-4.13.4/examples/tptp \
 && clang++ -std=c++17 -O2 -w -Iz3-4.13.4-x64-glibc-2.35/include \
      -o /usr/local/bin/z3_tptp \
      z3-z3-4.13.4/examples/tptp/tptp5.cpp \
      z3-z3-4.13.4/examples/tptp/tptp5.lex.cpp \
      z3-4.13.4-x64-glibc-2.35/bin/libz3.a -lpthread \
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
