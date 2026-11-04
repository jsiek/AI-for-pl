# VST as an alternative verifier for Ariadne

This directory checks whether VST ("Verifiable C", Princeton; built on
CompCert Clight and Rocq) could replace or complement the Frama-C/WP
pipeline of `../env` and `../m1a`.  It contains a pinned image and a
smoke test that verifies a malloc/write/free program end to end and
shows that VST refuses use after free, a write through a freed alias,
and double free, with no ghost model and no instrumentation.

```bash
cd Ariadne/vst
docker build -t ariadne-vst:dev .   # ~16.5 min on 24 cores (CompCert ~3.5, VST ~8.5)
cd smoke && ./check.sh               # four PASS lines, ~25 s
COQCHK=1 ./check.sh                  # plus coqchk, five PASS lines, ~2.5 min
```

**Recommendation (details in section 6):** run both pipelines on B1
for M1, with VST as the likely primary from M2 on.  VST fixes the two
structural problems M0/M1a found in WP (no allocation model; ACSL
definitions exported as unchecked axioms) without new trusted code.
The cost is more manual proof work per function, no SMT, and an
agent loop that has to write tactic scripts instead of annotations.

Items marked **[unverified]** were not checked here.

---

## 1. Fit and trust base

### 1.1 What a VST certificate says

The C file is translated by `clightgen` into a Rocq file (`good.v`)
holding the program's Clight AST (`prog`).  The proof file proves:

* `semax_body Vprog Gprog f_use_cell use_cell_spec`, one per function:
  the body satisfies its separation-logic spec, assuming every callee
  satisfies its spec in `Gprog`;
* `semax_prog prog tt Vprog Gprog`: all functions, linked, including
  `main` against `main_pre`.

VST's soundness theorem (`semax_prog_rule`, `veric/SeparationLogicSoundness.v`)
turns `semax_prog` into safety of the program: it never gets stuck
under CompCert Clight's operational semantics.  In Clight a load,
store, or `free` on a freed block is stuck (CompCert's memory model
removes the block's permissions in `Mem.free`), so **safety includes
the absence of use after free and double free.**  VST's typechecker
also asks for no signed overflow (`tc_nobinover`, `veric/expr.v`),
no division by zero, in-range shifts, and pointer comparisons only
between valid pointers.  This matches plan §2.1.  Whether reading
an uninitialised field is rejected (loaded values must pass
`tc_val`) **[unverified]**, but VST's `data_at_` (contents
undefined) vs `data_at` (contents known) points that way.

The certificate is the `.vo` of the proof file plus the `.vo` of the
AST.  It is re-checked with `coqc`/`coqchk` (done here; coqchk took
1 min 40 s for the smoke test including all of VST).  Proofs are
partial correctness: termination is not proved (plan §1.4 does not
need it).

### 1.2 Trusted base, compared to WP

| | Frama-C/WP (M0/M1a) | VST |
|---|---|---|
| C front end | Frama-C/CIL normalisation, `cpp` | `cpp` + CompCert's parser (Menhir, Rocq-validated grammar automaton **[unverified for 3.18]**) + elaborator (`cparser/Elab.ml`, `cfrontend/C2C.ml`, unverified OCaml) + SimplExpr/SimplLocals (proved Rocq passes, extracted) + `Clightnorm.ml` (unverified, `-normalize`) + `ExportClight.ml` (unverified printer).  See `export/ExportDriver.ml` in CompCert 3.18. |
| Obligation generation | RTE plugin: a missed obligation is a missed bug | none: obligations come from the Clight semantics, through VST's proved logic |
| VC generator + memory model | WP, Typed model, Qed simplifier (all trusted) | VST's program logic, **proved sound** in Rocq against Clight |
| Allocation | no model; ghost-liveness contracts + `dead_heap` axiom + stack admits + an instrumentation pass (all trusted, `../m1a/README.md`) | `malloc_spec'`/`free_spec'` in `floyd/library.v`: `Parameter`s `mem_mgr`, `malloc_token`, `body_malloc`, `body_free`, `create_mem_mgr`, … (standard, small, shared by all VST users).  Could be replaced by the verified allocator `progs/memmgr` (Naumann and Appel, ISMM 2020) **[unverified with 2.17]** |
| Spec definitions | ACSL `logic`/`inductive` exported as `Parameter` + `Axiom`; non-terminating ones accepted (guardrail 3a) | Rocq `Fixpoint`/`Definition`/`Inductive`: checked by the kernel, so no 3a hole |
| SMT | Alt-Ergo, Z3, CVC5 in the TCB (decision Q1) | none |
| Kernel | Rocq kernel, `coqchk` | same |
| Translation to the binary | not covered (any compiler) | not covered unless compiled with CompCert (then CompCert's correctness theorem composes); with gcc/clang the result is about the Clight semantics only |

Axioms measured on the smoke test (`smoke/expected_assumptions.txt`,
`Print Assumptions prog_correct`): `classic`, `prop_ext`,
`functional_extensionality_dep`, `Extensionality_Ensembles`, two
`ClassicalDedekindReals` axioms, and the six allocator assumptions from
`floyd/library.v` above.  `coqchk -o` lists 232 names: the same ones
plus `proof_irrelevance`, `eq_rect_eq`, CompCert's own parameters
(`external_functions_sem`, `inline_assembly_sem`, their `_properties`,
`Archi.win64`), two VST axioms about CompCert external calls
(`Clight_core.ef_deterministic_fun`, `inline_external_call_mem_events`),
`malloc_token_valid_pointer`, `malloc_token_change_composite`,
`body_exit`, and 204 fields of the opaquely sealed modules
`VST.msl.shares.Share` (174) and `VST.veric.compcert_rmaps.R` (30)
plus one deep-embedding field.  The sealed-module fields are proved
inside the modules (`Module Share : SHARE_MODEL := tree_shares.Share`),
and coqchk lists them because of the opaque `:`; that is my reading,
**[unverified]** with the Rocq developers.  The plan §7.4 allow-list
would be built from this list once and then diffed, as for WP.

**Net change to the TCB.** Removed: RTE, WP and its memory model, Qed,
Why3 and its Coq driver, SMT solvers, the ghost allocator model and
the instrumentation pass, and the ACSL-definitions-as-axioms risk.
Added: CompCert's front end and `clightgen` (unverified elaboration,
normalisation and printing; mitigated by reviewing the `-dclight`
output and by a regeneration check: re-run `clightgen` and require a
byte-identical `.v`), the VST allocator axioms, and VST's two axioms on
external calls.  The front-end risk is comparable to trusting CIL.

### 1.3 malloc/free and use after free

No ghost model is needed.  `malloc` returns `malloc_token Ews t p *
data_at_ Ews t p` (ownership of the new cell); `free` takes both back.
After `free(p)` nothing in the precondition mentions `p`, so a load or
store through `p` (or any alias, since ownership is per address, not
per variable) has no `data_at` to justify it.  `forward` fails with
"It is not obvious how to move forward here.  Find a SEP clause of the
form [data_at _ _ _ p] …" (see `smoke/verif_bad.v`).  A second `free`
needs `emp |-- malloc_token … p * data_at_ … p * Frame`, which is not
provable for `p <> NULL`.  Pointers to locals cannot be freed for the
same reason (they never carry a `malloc_token`).

Why the bad functions cannot be verified at all (not only by these
tactics): if `semax_body` held for them with a satisfiable
precondition, soundness would make them safe in Clight, but there is
an execution where `malloc` returns a block and the access after
`free` is stuck.  This argument assumes the allocator axioms are
consistent with Clight's `EF_malloc`/`EF_free` semantics, which is
what the verified `memmgr` allocator would establish.

### 1.4 Separation logic vs ACSL `\separated`

Intrusive DL lists and trees are the textbook case for separation
logic: a representation predicate like (a sketch, not compiled here)

```coq
Fixpoint dlrep (vs: list (Z * val)) (prev p: val) : mpred :=
  match vs with
  | nil => !! (p = nullval) && emp
  | (v, q) :: vs' => !! (p = q) &&
      EX nx: val, data_at Ews t_ilist (Vint (Int.repr v), (nx, prev)) p
                  * dlrep vs' p nx
  end.
```

carries disjointness in `*`, so the footprint sets, `\separated`
clauses and frame lemmas of plan §4.2 go away.  It is a Rocq
`Fixpoint`, so plan §4.3 ("connect WP's export to real definitions")
and guardrail 3a are moot.  VST ships singly linked `lseg`/`listrep`
(`progs/list_dt.v`, `progs/verif_reverse2.v`) and binary trees
(`progs/verif_bst.v`, `tree_rep`/`treebox_rep`, insert/lookup/delete),
but **no doubly linked list and no C red-black tree** (the only
red-black tree, `veristar/redblack.v`, is a functional Gallina one).
Ariadne would write `dlrep`/`dlseg` and an RB variant of `tree_rep`
with colours (plus parentless rotations, which sglib's RB code uses)
as the G7 library.

## 2. Practicalities

### 2.1 Versions (checked in opam on 2026-11-03)

| Package | Version | Rocq bound | Notes |
|---|---|---|---|
| `coq-vst` | **2.17** (2026-09-22) | `coq >= 9.0 & < 9.4` | needs `coq-compcert 3.18.x`; release notes say "Rocq 9.1–9.3", but it **builds and works on 9.0.1** (this image) |
| `coq-vst` | 2.16 | `coq >= 9.0 & < 9.4` | `coq-compcert >= 3.16 & < 3.18` (CCV, §4.3, used 2.16 + Rocq 9.0.0 + CompCert 3.17) |
| `rocq-vst` | 3.2beta (2026-08-24, prerelease) | Rocq 9.0–9.1 | Iris-based VST 3; CompCert 3.17, Iris 4.5.0; different proof style |
| `coq-compcert` | **3.18** (2026-08-30) | `coq >= 8.15 & < 9.3` | opam build passes `-clightgen`, so `clightgen` is installed.  The 3.18 tarball's `VERSION` file says 3.17, so `clightgen -version` prints 3.17 |
| `coq-vst-zlist` | 2.13 | | VST dependency |
| `coq-vst-lib` | 2.15.1 | `< 9.4` | VSTlib VSUs (axiomatised malloc, verified memmgr "soon") |
| `coq-hammer` | 1.3.2+9.0, 1.3.2+9.1, 1.3.3+9.1, 1.3.3+9.2 | | same 1.3.2+9.0 as M0 |
| `coq-lsp` (Pétanque) | 0.2.5+9.0, 0.2.5+9.1 | | same 0.2.5+9.0 as M0; no 9.2 build listed |

So VST, CompCert, CoqHammer and coq-lsp all exist for **Rocq 9.0.1,
the Rocq that M0 already pins** (Frama-C/Why3 cannot go past 9.0).  One
image could hold both toolchains.  Without Frama-C, Rocq 9.1 would also
work for all four **[unverified build]**.

### 2.2 Install route

`opam install coq-compcert.3.18 coq-vst-zlist.2.13 coq-vst.2.17` on the
M0 base image (`rocq/rocq-prover:9.0.1-native-ocaml-4.14.2`, same
digest), plus `coq-lsp.0.2.5+9.0` (needs the same `ocamlfind` 1.9.8
fix as M0) and `coq-hammer-tactics.1.3.2+9.0`.  See `Dockerfile`.
Build: CompCert ~3.5 min, VST ~8.5 min, whole image 16.5 min on 24
cores; image 7.0 GB.  The base image has the native compiler on, so
`coqc` must be called with `-native-compiler no` (otherwise
compilation fails at the end with `Unbound module
NVST_veric_compspecs`).

### 2.3 License

VST is BSD-2-Clause.  CompCert (and so `clightgen`) is under the
**INRIA Non-Commercial License** (`LICENSE` in CompCert 3.18); only
some files (`common/`, `lib/`, `cparser/`, `export/`, `Clight.v`,
`C2C.ml`, …) are also LGPL, while `clightgen` links non-LGPL passes
(`SimplExpr`, `SimplLocals`).  VST's `CLIGHTGEN-LICENSE` says academic
use for research is free; commercial use needs an AbsInt license.
For Ariadne (academic research at IU) this is fine.  Consequences:
(a) the Docker image must not be published as something others may use
commercially; (b) **generated `.v` ASTs can be shipped in the
certificate bundle**, and a third party re-checking a bundle does not
need `clightgen` at all (VST's own license note says so), which suits
G4; (c) the Clight semantics files themselves are LGPL.

## 3. Handling sglib

`clightgen -normalize` accepts all of sglib: run here on the plan's
B1 and B2 drivers and on `samples/{dllist,rbtree,hash,listsort}.c`
(sglib master); each `.v` compiles with `coqc` (B1: 107 lines of
Clight, B2: 1996 lines, 26 functions; rbtree.c: 2004 lines).
Shadowed macro locals are renamed (`it`, `it__1`, `it__2`), chained
assignments and `&&`/`||` with loads are split into temporaries.

Verifiable C's C subset (`doc/VC.tex`, "Verifiable C" chapter): no
int/pointer casts, no `goto`, no bitfields, no struct copy/struct
parameters/returns, structured `switch` only, no varargs except
limited `printf`/`fprintf`.  sglib's DL-list, RB-tree, list and hash
code uses none of these: no `goto` (the three hits in `sglib.h` are
comments), no varargs, no `__builtin_memcpy` (struct copy) in any
Clight output, no `switch`; the only casts are pointer-to-pointer and
integer ones.  Things that need specs: `__assert_fail` (33 call sites
in B2, from `assert` in the RB-tree consistency checks; spec with
precondition `False`, i.e. unreachable), `printf` in the samples (drop
it, as plan B1 already does, or use VST's `progs/printf.c` support),
and `malloc`/`free` in drivers (VST's library specs).

Function pointers / comparators.  sglib's `comparator` is a macro
argument pasted textually: `CMP_NODES(x, y)` becomes an inline
expression, a function name becomes a direct call needing an ordinary
funspec.  True function pointers appear only in the hash iterator
(`int (*subcomparator)(type *, type *)`); VST handles them with
`func_ptr' spec f` in the precondition (`progs/funcptr.c`,
`progs/verif_funcptr.v`; comparisons in `progs64/fptr_cmp.c`).

Level-0 macros expand inside the caller (B1 is a single `main` with
three loops), so the proof is one `semax_body` for `main`.  Level-1
code (`SGLIB_DEFINE_RBTREE_FUNCTIONS`) gives real functions with one
`semax_body` each.  Plan decision Q4 (annotate the preprocessed file)
becomes simpler: **the C is never annotated**.  Specs and invariants
live in `.v` files and refer to Clight identifiers (`_list`, `_e`,
`_it__1`), and the overlay guardrail (§7.1) becomes "the `.v` AST is
byte-identical to `clightgen` output of the frozen C".

## 4. Automation and AI fit

### 4.1 VST-Floyd

Proofs are tactic scripts that symbolically execute the function:
`start_function`, `forward` (one statement), `forward_call`,
`forward_if`, `forward_while`/`forward_loop`/`forward_for_simple_bound`
(take a loop invariant as argument), `Intros`/`Exists`, and entailment
solvers `entailer!`, `cancel`, `list_solve` (zlist).  On the smoke test
the whole `use_cell` proof is 20 tactic calls, and every step returns
a small, structured goal (PROP/LOCAL/SEP).  There is no SMT; arithmetic
side conditions go to `lia`/`rep_lia`.  Whether CoqHammer helps on VST
side goals **[unverified]**: entailments in separation logic are
higher order and unlikely to suit ATPs, but leftover pure goals
(`Int.repr` arithmetic, list lemmas) might.

### 4.2 Close examples in VST (`progs/`, VST 2.17)

* singly linked lists: `verif_reverse*.v`, `verif_append*.v`,
  `verif_queue*.v` (malloc/free, `listspec`), `verif_insertion_sort.v`,
  `verif_merge.v`;
* binary search trees with malloc: `verif_bst.v` (64-bit copy in
  `progs64/`), `verif_bst_oo.v`, `verif_tree.v`;
* allocator: `progs/memmgr/` (verified malloc/free);
* function pointers: `verif_funcptr.v`, `progs64/verif_fptr_cmp.v`;
* none for doubly linked lists or C red-black trees (§1.4).

### 4.3 LLM/agent work on VST

* **CCV** (Li et al., "Automatically Building Machine-Checked Assurance
  Cases from C Codebases to Requirements", arXiv 2609.40119, 2026;
  <https://arxiv.org/html/2609.40119v1>).  VST 2.16, Rocq 9.0.0,
  CompCert 3.17.  An agent writes specs, lemmas and proofs; memory
  safety and leak freedom for all 299 functions of six C benchmarks,
  including **a red-black tree (287 LOC, 12 functions, allocation,
  rotations, insertion repair; 1.55 days)** and **a linked-list library
  (148 LOC, 10 functions; ~0.22 days, 0.22 B tokens including cache
  reads)**, under one person-day of human effort per benchmark.
  Models: Claude Opus 5 (Claude Code) for one benchmark, GLM-5.3 and
  GLM-5.3-Flash (OpenCode) for another.  It reports that stalls often
  need spec revision and that an agent once silently weakened a theorem
  statement (an argument for frozen, hashed specs).  No artifact URL in
  the paper.  Token counts are large compared with plan §11's budget.
* **SynVer** (Mukherjee and Delaware, "Towards Automated Verification
  of LLM-Synthesized C Programs", arXiv 2410.14835): LLM-generated C
  checked with VST, with syntactic biases to keep Floyd automation
  working.
* **VST-A** (Zhou, Qin, Wang, Appel, Cao, POPL 2024,
  <https://www.cs.princeton.edu/~appel/papers/vst-a.pdf>): annotated C
  (assertions and invariants in comments) on top of VST, with the same
  soundness; residual goals in Rocq.  Closest to the ACSL workflow
  Ariadne planned; whether it builds with Rocq 9 **[unverified]**.

### 4.4 Mapping plan §12 roles onto VST

| Plan role | Frama-C pipeline | VST |
|---|---|---|
| Human (frozen) | ACSL contracts, shape predicates | funspecs (`DECLARE … WITH … PRE … POST`), rep predicates (`dlrep`, `rbrep`) as Rocq definitions; hash both |
| Annotator (Opus) | loop invariants, asserts, ghost code, lemmas | loop invariants (the arguments of `forward_while`/`forward_loop`), `forward_if` join assertions, helper lemmas about rep predicates, specs of internal (static) functions |
| Prover tier | tactics for WP's leftover Coq goals | the tactics between those points: `forward`, `entailer!`, unfolding/folding rep predicates, `sep_apply` of lemmas, side goals |
| Oracle | Frama-C/WP + Why3 + Pétanque | `coqc` + Pétanque only (shown in `smoke/pet_check.py`) |

The harness can keep the two roles separate by generating a proof
*skeleton* per function: `start_function`, then one `forward`/
`forward_call` per straight-line statement, and holes where the
annotator must supply an invariant or join assertion.  The prover then
closes the entailment/side goals left in each hole.  Unlike WP, a stall
usually shows up as a precise Floyd error at a statement (as in the
use-after-free test), which is a good *needs-annotation* signal.
Guardrails: `Admitted`/`admit`/`Axiom` linting and the `Print
Assumptions`/coqchk allow-list apply unchanged; additionally reject any
change to the funspecs, the rep-predicate definitions, or the
generated AST.

## 5. Effort to M1 (B1 fully verified for memory safety)

Estimates are judgement, not measurements.

**VST.**  Remaining work: a `dlrep`/`dlseg` predicate and its
unfold/fold lemmas (~100 lines of Rocq); `main_spec`; one proof for
`main` with three loop invariants (the `for` with `malloc` and
`SGLIB_DL_LIST_ADD`, then the two `MAP_ON_ELEMENTS` walks, backward
then forward); bounds on `sum` (VST checks the `long` addition for
overflow); `__assert_fail` is not used by B1.  For someone fluent in
VST: **2–5 days**.  For a VST newcomer, add **1–2 weeks** for
*Software Foundations* vol. 5 (Verifiable C).  CCV's numbers (a
148-line list library in ~0.22 days of agent time) suggest the agent
version of B1 (M3) is feasible, at a token cost to be measured against
§11.

**Frama-C/WP.**  Remaining work from `../m1a/README.md`: the
instrumentation plugin (OCaml, plus its own review and count check),
allocator contracts for `ilist`, ACSL `dll_seg` with footprints and
`\separated`, frame lemmas, Coq realisations so WP's exported axioms
are justified (plan §4.3 is still **[verify]**), and the 3a guardrail.
Estimate: **3–6 weeks** to M1, most of it on the plugin and the Coq
side of the shape predicates.  Its advantage is that many goals close
by Qed/SMT, so the M1 *proof* effort is smaller once the
infrastructure exists.

## 6. Recommendation

**Run both on B1 for M1; plan to make VST the primary pipeline from
M2 unless the B1 comparison says otherwise.**

Owner's note: use **SMTCoq** to automate some of the Rocq proofs on
the VST side (pure arithmetic/logic side goals), keeping the SMT solver
outside the trust base by checking its certificates in Rocq.  See plan
§9.2 Q10 for what to check first.

For VST:
* use after free, double free, and freeing a stack object are caught
  by the logic, with no ghost model, no instrumentation pass, no
  `admit`s, and no trusted SMT (M1a's whole TCB addition disappears);
* rep predicates are kernel-checked Rocq definitions: guardrail 3a's
  hole cannot happen;
* the logic is proved sound against Clight, and the certificate is one
  theorem (`semax_prog`) re-checkable with `coqc`/`coqchk` from the
  shipped AST without `clightgen`;
* same Rocq 9.0.1, CoqHammer and coq-lsp/Pétanque versions as M0;
  Pétanque already drives VST proofs (`smoke/pet_check.py`);
* there is recent, close evidence that LLM agents can do this (CCV:
  red-black tree and linked list in VST, including GLM-5.3-Flash).

Against VST:
* no SMT: every function needs a tactic proof, so the prover role does
  much more work, and token cost may be high (CCV's linked list: 0.22 B
  tokens, mostly cache reads);
* plan §§3–5, §7.1–7.3 and G3 ("annotation-only ACSL edits") are written
  for ACSL and must be rewritten for specs/invariants in Rocq files;
* `clightgen` and CompCert's elaborator join the TCB, and CompCert is
  non-commercial (fine for this project);
* no existing VST library for doubly linked lists or C red-black trees
  (the WP side has none either).

Staying with WP alone is not recommended: it needs new trusted code
(the plugin) just to see use after free, and its spec layer is
axiomatic.  Switching outright before M1 throws away a cheap
comparison: B1 in VST is days of work, and the M1 goal census from both
sides is a useful result for the paper (G6).

## 7. Prototype

Files (all in this directory):

| File | What |
|---|---|
| `Dockerfile` | VST 2.17 + CompCert 3.18 + coq-lsp 0.2.5+9.0 + coq-hammer-tactics on the M0 base image |
| `run.sh` | as `../env/run.sh`, image `ariadne-vst:dev` (`ARIADNE_VST_IMAGE` overrides) |
| `smoke/good.c` | `use_cell`: malloc, null check, two writes, a read, free; `main` calls it |
| `smoke/bad.c` | `use_after_free`, `write_after_free_alias`, `double_free` |
| `smoke/verif_good.v` | funspecs, `semax_body` for both functions, `semax_prog` (`prog_correct`), `Print Assumptions` |
| `smoke/verif_bad.v` | the same steps on each bad function; the step at the `BAD` line is wrapped in `Fail`, so the file compiles only if VST refuses it |
| `smoke/expected_assumptions.txt` | recorded `Print Assumptions prog_correct` |
| `smoke/pet_check.py` | Pétanque runs `body_use_cell` sentence by sentence (`proof_finished: True`), then replays `use_after_free` and checks that `forward` after `free` returns VST's error |
| `smoke/check.sh` | steps: clightgen; good proof + assumptions diff; bad refusals (4 `Fail`s, 2 with the "not obvious how to move forward" message, from a `coqtop` transcript); Pétanque; with `COQCHK=1`, coqchk |

Status: **all steps PASS** (2026-11-03).  Exact commands:

```bash
cd Ariadne/vst
docker build -t ariadne-vst:dev .
cd smoke
./check.sh                # PASS x4
COQCHK=1 ./check.sh       # PASS x5; cert/coqchk.txt lists the axioms
```

By hand: `../run.sh clightgen -normalize good.c bad.c`, then
`../run.sh coqc -native-compiler no -Q . Smoke good.v` (and `bad.v`,
`verif_good.v`, `verif_bad.v`).

Not done: B1 itself in VST (that is M1); a combined Frama-C + VST
image; `coq-hammer` with ATPs in this image; VST-A; the verified
`memmgr` allocator in place of the axiomatised one.

## Sources

* VST: <https://github.com/PrincetonUniversity/VST>, release v2.17
  (2026-09-22, notes: "Compatible with Rocq 9.1-9.3 and with CompCert
  3.18"), v3.2beta (2026-08-24); files cited: `floyd/library.v`,
  `veric/SeparationLogicSoundness.v`, `veric/Clight_core.v`,
  `veric/expr.v`, `doc/VC.tex`, `CLIGHTGEN-LICENSE`, `progs/`,
  `lib/README.md`.
* CompCert: <https://github.com/AbsInt/CompCert>, v3.18 (2026-08-30):
  `LICENSE`, `Changelog.md` ("Stricter formal semantics for `free`"),
  `export/ExportDriver.ml`, `export/Clightnorm.ml`.
* opam metadata (`opam show`, rocq-released + default repositories,
  2026-11-03) for the version bounds in §2.1.
* sglib master: <https://github.com/Marian-Vittek/sglib>.
* CCV: <https://arxiv.org/html/2609.40119v1>.
* SynVer: <https://arxiv.org/abs/2410.14835>.
* VST-A: <https://popl24.sigplan.org/details/POPL-2024-popl-research-papers/71/VST-A-A-Foundationally-Sound-Annotation-Verifier>.
* VST-Floyd: Cao, Beringer, Gruetter, Dodds, Appel, J. Automated
  Reasoning 2018 (doi 10.1007/s10817-018-9457-5).
* Naumann and Appel, "Verified Sequential Malloc/Free", ISMM 2020
  (doi 10.1145/3381898.3397211).
