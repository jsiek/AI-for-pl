# Task: VST proof of memory safety and leak freedom for picol

You are verifying a complete C program with VST (Verifiable C 2.17,
CompCert 3.17 clightgen, Rocq 9.0.1): picol, a small Tcl interpreter.
Files in this directory:

* `picol_full.c`: the program to verify, one self-contained file: picol
  (`picol.c`, with `main` renamed `picol_main`), musl libc's definitions
  of `stdin`/`stdout`/`stderr`, musl's `strlen`, `__strchrnul`,
  `strchr`, `strcmp`, `memcpy`, `isupper`, `__isupper_l`, and a
  `main(void)` that calls `picol_main` in REPL mode and in script mode.
  `picol.c` and `picol_vst.c` are the readable sources (with comments);
  `picol_full.c` is what is verified.
* `spec_picol.v`: `CompSpecs`, `Vprog`, and frozen funspecs: the
  external functions (`realloc`, `fmt_double`, `strtod`, `fopen`,
  `fclose`, `fputs`, `fflush`, `fgets`, `fread`, `perror`, each with an
  axiom `body_X`; `exit` is VST's library spec, `body_exit`), the musl
  functions, `picol_main_spec` and `main_spec`.
* `libc_proofs/`: VST proofs of the musl functions against these specs
  for a program containing only them; they replay unchanged against
  `picol_full.c` (drop their `Require Import Libc...` line).

## What to produce

`verif_picol.v` (you may split the work over more files; then list all
your .v files, in compilation order, one per line, in `proof_files.txt`,
ending with `verif_picol.v`) that

1. starts with `Require Import VST.floyd.proofauto. Require Import
   VST.floyd.library. Require Import Picol.picol_full Picol.spec_picol.
   #[export] Existing Instance NullExtension.Espec.` and uses
   `CompSpecs`, `Vprog` and the funspecs of `spec_picol.v` (do not
   redefine them);
2. defines a funspec for every other function of `picol_full.c`: your
   choice, whatever the proofs need;
3. defines `Gprog : funspecs` (e.g. `ltac:(with_library prog [...])`),
   once, in any of your files, containing every frozen funspec of
   `spec_picol.v` and yours;
4. proves `semax_body Vprog Gprog f_X X_spec` for every function, and
5. proves `Lemma prog_correct : semax_prog prog tt Vprog Gprog.`
   (`prove_semax_prog`, then `semax_func_cons body_X` for each function
   in the order of `prog`'s definitions, the external ones with the
   `body_X` axioms of `spec_picol.v` and VST's `body_exit`).

**Leak freedom.**  No postcondition of yours may contain `TT`, an
existential over `mpred`, or `!! P` outside a conjunction: a function
must give back exactly the memory it owns.  (The check lints every
funspec.)

## Notes

* picol calls its commands through function pointers
  (`c->func(i,argc,argv,c)`); VST handles calls through function
  pointers with `func_ptr'` (see VST's `progs64/verif_funcptr.v` and
  `progs64/verif_object.v` in the image).
* String literals are global variables; `main_pre` (and
  `globvars2pred gv (prog_vars prog)` in `picol_main_spec`) holds them
  (see `expand_main_pre` in VST).
* For an external function, `semax_func_cons body_X` may leave a goal
  that the return value is well typed; it follows from the frozen
  postcondition (e.g. `fopen`'s result is NULL or, by
  `FILE_handle_ptr`, a pointer; `realloc`'s is NULL or holds a
  `data_at`).  `eapply semax_func_cons_ext` shows the goals.
* Compiling a large proof file takes a while: split into several files
  if that helps you iterate.  Checking `prog_correct` needs about 6.5 GB
  of memory: run one such build at a time.
