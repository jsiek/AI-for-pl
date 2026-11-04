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
