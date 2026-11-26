# Task: VST proof of memory safety for musl's `{unit}`

You are verifying C code with VST (Verifiable C 2.17, CompCert 3.17
clightgen, Rocq 9.0.1).  Files in this directory:

* `{unit}.c`: musl libc 1.2.6's source of {functions}, preprocessed
  into one self-contained file.
* `spec_{unit}.v`: `CompSpecs`, `Vprog` and the frozen funspecs.

## What to produce

One file, `verif_{unit}.v`, that

1. starts with `Require Import VST.floyd.proofauto. Require Import
   VST.floyd.library. Require Import Libc.{unit} Libc.spec_{unit}.` and
   uses `CompSpecs`, `Vprog` and the funspecs of `spec_{unit}.v` (do not
   redefine them);
2. defines a funspec for each function of `{unit}.c` that has none in
   `spec_{unit}.v` (your choice: what the other proofs need);
3. defines `Gprog : funspecs` containing a funspec for every function;
4. proves `Lemma body_f : semax_body Vprog Gprog f_f f_spec.` for each
   function f (exactly these names), each ending in `Qed.`

Helper lemmas are fine.  VST's own `progs64/verif_strlib.v` (in the
image) proves VST's string functions against specs like these; musl's
code differs (for example it reads through `unsigned char *` casts).
