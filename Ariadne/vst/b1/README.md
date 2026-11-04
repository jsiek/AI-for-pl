# B1a in VST: sglib doubly linked list, memory safety

The same benchmark as `../../bench/b1` (Frama-C/WP), verified with VST
2.17 / CompCert 3.18 `clightgen` / Rocq 9.0.1 (image `ariadne-vst:dev`,
`../Dockerfile`), so the two pipelines can be compared (plan §9.2 Q10).

**Status: fully verified.**  Every function in `b1.c` has a
`semax_body` proof and the whole program has `semax_prog`
(`prog_correct`).  No `admit`, `Admitted`, or new axiom; `Print
Assumptions prog_correct` is exactly the smoke test's list (VST's
malloc/free assumptions plus classical axioms).

```bash
cd Ariadne/vst/b1
./check.sh        # five PASS lines, ~2 min (see Metrics)
```

## What is verified

| Function | Proof | Status |
|---|---|---|
| `sglib_dllist_add` | `body_sglib_dllist_add` | proved |
| `sglib_dllist_it_init_on_equal` | `body_sglib_dllist_it_init_on_equal` | proved |
| `sglib_dllist_it_init` | `body_sglib_dllist_it_init` | proved |
| `sglib_dllist_it_next` | `body_sglib_dllist_it_next` | proved (both call modes) |
| `b1` (driver, 3 loops) | `body_b1` | proved |
| `main` | `body_main` | proved |
| whole program | `prog_correct : semax_prog prog tt Vprog Gprog` | proved |

The guarantee is VST's soundness theorem: `semax_prog` implies that
the program, under CompCert Clight's semantics, never gets stuck.
Loads, stores and `free` on freed or unallocated blocks are stuck in
Clight, so this includes no use after free, no double free, no NULL
dereference, no out-of-bounds read of `input`, and no signed overflow
in `k++`.  The frees are of malloc'd blocks because `free`'s spec
consumes the block's `malloc_token`, which only `malloc` produces.
Termination and functional correctness (the returned value) are not
proved.  `b1`'s postcondition holds no list nodes, and the proof hands
every node to `free` (none is dropped by an entailment); `semax_prog`
does not state leak freedom, so this is an observation about the
proof, not a guarantee.

## Files

| File | What |
|---|---|
| `make_b1.py` | writes `b1.c` and the mutants `bad_uaf.c`, `bad_nonull.c` from `../../bench/b1/b1_gen.c` |
| `b1.c` | types and the four sglib functions **byte-identical** to `b1_gen.c` (asserted by the script), the B1a driver with real `malloc`/`free`, a global `input[4]`, `main` |
| `bad_uaf.c`, `bad_nonull.c` | types, sglib prototypes, and a mutated driver (still named `b1`) |
| `verif_b1.v` | representation predicate, funspecs, proofs, `prog_correct`, `Print Assumptions` |
| `verif_bad.v` | the negative tests |
| `expected_assumptions.txt` | recorded `Print Assumptions prog_correct` (identical to `../smoke/expected_assumptions.txt`) |
| `check.sh` | the check (below) |

`b1.v`, `bad_*.v` (clightgen output) and `cert/` are generated and
git-ignored.

The generator started as a one-off script handed to me; it had a bug:
its function finder matched the continuation line of the `extern`
prototype of `sglib_dllist_it_init_on_equal` (a line at column 0 that
does not end in `;`), so it emitted `sglib_dllist_add` twice and no
`it_init_on_equal`.  It now skips prototypes (no `extern`, no `;` in
the header) and asserts that every copied piece occurs verbatim in
`b1_gen.c`.  No change to the C was needed for `clightgen`: it accepts
the file as generated.  (`clightgen` renames the parameter `input` of
`b1` to `input__1` because of the global `input`; in the mutants,
which have no global, it stays `input`.)

## The specification

All in `verif_b1.v`, sections "Specification".

**Representation.**  A list is a Rocq list of nodes
`(address, value of field i)`.

```coq
Fixpoint dlseg (prev: val) (s: list (val * int)) (t: val) : mpred :=
  match s with
  | nil => emp
  | (p, x) :: s' =>
      data_at Ews t_dll (Vint x, (hd_or s' t, prev)) p
      * malloc_token Ews t_dll p * dlseg p s' t
  end.
Definition dll (prev: val) (s: list (val * int)) := dlseg prev s nullval.
```

Each node owns its cell and its `malloc_token`; `ptr_to_next` is the
next node (or `t`), `ptr_to_previous` the previous one (or `prev`).
Distinctness of nodes comes from `*`: there is no `mem`, `all_live`,
`unchanged`, or frame lemma as in the Frama-C version.  `prev` of a
whole list is NULL; after the driver frees the head, the rest is
`dll p s'` with `p` dangling, which is fine because nothing reads it.

**Funspecs** (restricted as in the Frama-C contracts):

- `sglib_dllist_add(list, elem)`: `*list` holds the **head** of
  `dll nullval s` (any writable cell), `elem` is a separate malloc'd
  node with `i` set; afterwards `*list = elem` and
  `dll nullval ((elem, x) :: s)`.
- `sglib_dllist_it_init_on_equal(it, list, subcomparator, equalto)`:
  `subcomparator == NULL`, `list` the head of `dll nullval s`,
  `equalto` arbitrary, `*it` uninitialised; returns the head and leaves
  `*it = {head, NULL, second node, NULL, equalto}`.
- `sglib_dllist_it_init(it, list)`: the same with `equalto = NULL`.
- `sglib_dllist_it_next(it)`: no subcomparator, and `iter_pre`:
  either `prevelem == NULL` and `nextelem` heads `dll q s` (later calls;
  `q` arbitrary), or `prevelem` is the head of a whole list
  (`q = NULL`) and `nextelem` its successor (the call from
  `it_init_on_equal`).  Returns `hd s`, sets `prevelem = NULL`,
  `nextelem = hd (tl s)`, `currentelem = hd s`; the nodes are unchanged
  (`dll q s` in both pre and post).  The subcomparator loops are
  unreachable under this precondition (`it->subcomparator != NULL` is
  false), as in the Frama-C version.
- `b1(input, n)`: `0 <= n <= Int.max_signed`, `input` points to `n`
  readable ints; post: the same ints, the allocator state, an int.
- `main`: VST's `main_pre`.

## Negative tests (`verif_bad.v`)

The mutants are checked against the same `b1_spec` and sglib funspecs.
Each proof replays `verif_b1.v` up to the bad statement, where the next
Floyd step must fail (`Fail tac` succeeds only if `tac` fails):

| Mutant | Refused step |
|---|---|
| `bad_uaf.c`: forward walk after the free loop | after the free loop no SEP clause mentions the head `p`; `if (l != NULL)` leaves `... |-- denote_tc_test_eq p nullval` (comparing a freed pointer is undefined in Clight), which `entailer!` cannot prove; and the load `l->i` fails with "It is not obvious how to move forward here … data_at …" |
| `bad_nonull.c`: no NULL check after `malloc` | `l->i = …` fails: malloc's post gives the cell only under `if eq_dec l nullval then emp else …`, and in the `l == NULL` case there is no cell at all (two `Fail forward`) |

`check.sh` counts 4 refusals, 3 of them Floyd's "not obvious how to move
forward" message.  **These tests only show that Floyd's tactics stop;
the real guarantee is VST's soundness**: if `semax_body` held for a
mutant with a satisfiable precondition, the mutant would be safe in
Clight, but each mutant has a stuck execution (a load from a freed
block; a store through NULL when `malloc` fails).  The walk invariant
in the UAF test is the honest one (what the program still owns); no
other invariant could hold a `data_at` for `p` either, since `free`
consumed it.

## check.sh

1. `make_b1.py` regenerates `b1.c`, `bad_uaf.c`, `bad_nonull.c`
   byte-identically (and its own verbatim asserts pass);
2. `clightgen -normalize` on the three files; `coqc` on the ASTs;
3. lint: no `Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture` in the
   proof files;
4. `coqc verif_b1.v`; `Print Assumptions` output (`cert/assumptions.txt`,
   must start with `Axioms:`) equals `expected_assumptions.txt`;
5. `coqc verif_bad.v` and a `coqtop` transcript
   (`cert/bad_transcript.txt`): exactly 4 refusals, 3 with the
   "not obvious" message, no `Error`.

Any failing command, an empty or missing report, or a count mismatch
prints `FAIL` and makes the script exit non-zero.  coqchk was not added
(the smoke test shows it works: `COQCHK=1 ../smoke/check.sh`).

## Comparison with Frama-C/WP (`../../bench/b1`)

Same C code (sglib part byte-identical), same driver except real
`malloc`/`free` instead of the ghost allocators, same contract
restrictions.

### Metrics

Lines are non-blank, non-comment lines.

| | Frama-C/WP | VST |
|---|---|---|
| Spec: definitions + contracts (frozen part) | 91 lines of top-level ACSL (6 predicates incl. inductive `dll`, 6 lemma statements, 5 contracts) | ~95 lines: rep predicate `dlseg`/`dll` + helpers (16), funspecs + `iter_pre` (~80) |
| Annotations (agent role: invariants, asserts, join points) | 30 lines in function bodies (loop invariants, `loop assigns`, 7 guiding asserts) | ~169 lines inside proofs: 3 loop invariants x (inv, continue, break) in `b1`, and 9 `forward_if` join assertions (6 in `it_next`) |
| Hand-written proof script | 3 Coq lemmas, 60 lines (`mem_cons`, `all_live_cons`, `dll_frame`) | ~136 tactic lines for the 6 functions + `prog_correct`, plus 6 helper lemmas (8 lines); 293 tactic sentences in all (`body_b1` 112, `it_next` 74, `add` 41, `it_init_on_equal` 33, `main` 7, `it_init` 3, `prog_correct` 10, lemmas 13) |
| Goals / automation | 183 goals: Qed 109, SMT 71 (Alt-Ergo 65, CVC5 5, Z3 1), Coq 3 | no goal census: every statement is one Floyd step; 38 `entailer!`, 3 `cancel`, 3 `sep_apply` close the entailments |
| Helper lemmas | 6 (3 by SMT, 3 in Coq) | 6: `dlseg_cons` (refl), `dlseg_local_facts`, `dll_local_facts`, `hd_or_app`, `last_or_snoc` (induction), `dlseg_snoc` (induction) |
| Negative tests | 3 mutants (vacuity, uaf, nullchk) | 2 mutants (uaf, nonull), 4 `Fail`s; vacuity is not needed in the same way (see below) |
| Extra trusted code | ghost allocator model, `-ariadne` instrumentation plugin, `dead_heap` axiom, WP/Qed/SMT, ACSL lemmas as axioms until proved | `clightgen` front end; VST's 6 allocator assumptions (`expected_assumptions.txt`) |
| Wall-clock of `check.sh` (this machine, 24 cores) | 231 s (`bench/b1/check.sh`: full proof + 3 mutants; this run split SMT as Alt-Ergo 64, CVC5 6, Z3 1) | 126 s (all five steps; the two `coqc verif_*.v` runs dominate) |

On vacuity: in VST an inconsistent precondition would show up as a
`b1_spec` nobody can call; `main` calls `b1` with the real global
array and `main_pre`, and `semax_prog` checks that, so the
precondition is satisfiable for the actual input.

### Effort, honestly

Agent time for the VST version: one session, about 50 edit/compile
iterations of `verif_b1.v` (each `coqc` run 30-60 s), from no VST
proof to `prog_correct`.  By function: `add` and `it_init*` were quick
(a few iterations each); `it_next` and `b1` took most of the time.

What Floyd did automatically: every field load and store, the
malloc/free/sglib calls (`forward_call` with the WITH tuple), all
typechecking side conditions (pointer comparisons via
`valid_pointer` from `data_at`, `input[k]` bounds, `k + 1` overflow,
`Int.repr` ranges), and almost all entailments (`entailer!`).  No
arithmetic goal was proved by hand.

Where I got stuck or needed manual work:

- **Join assertions.**  `forward_if` needs an explicit postcondition
  whenever the `if` is followed by more code.  `it_next` (24 lines of
  C) has 6 such ifs; each join restates the whole state, so its proof
  is mostly assertions.  WP needs none of this.
- **Case splits on the list before the first access.**  Loading
  `*list` or `it->nextelem` gives a `tc_val` goal for `hd_ptr s`; it
  closed only after splitting on `s` and adding the `saturate_local`
  hints `dlseg_local_facts`/`dll_local_facts`.  Every function proof
  starts with `destruct s` and handles empty/non-empty separately.
- **Rewriting under abbreviations.**  `rewrite dlseg_cons` or
  `simpl dlseg` inside a `semax` goal whose `POSTCONDITION` mentions
  the same term broke Floyd (`simplify_Delta did not put Delta_specs
  and Delta into canonical form`).  Workaround: unfold once at the
  start and write all join assertions in unfolded form.
- **An elaboration failure in loop invariants.**  A `data_at` of a
  struct value written inline under `EX` in a `forward_loop` argument
  fails with "has type environ -> mpred while it is expected to have
  type mpred" (it works with explicit `@exp (environ -> mpred) _ T
  (fun x => …)`, and in funspecs).  It cost several iterations to
  isolate; workaround: the definitions `it_val`/`iter_at` and a folded
  `continue:` invariant for the walk.
- **Clight shape.**  `clightgen` turns `for (int k = 0; …)` into a
  `for` whose init `forward_loop` executes, `t = f(); l = t;` is
  absorbed by `forward_call`, and the third loop's init is a separate
  call; each mismatch showed up as a Floyd error message, which was
  usually precise enough to fix the next step.
- **Unreachable branches.**  The subcomparator branches
  (`it->subcomparator != NULL`, with a function-pointer call inside a
  loop) are discharged by `discriminate` on `false = true` right after
  `forward_if`; no spec for a function pointer was needed.
- **Manual lemmas**: only `dlseg_snoc` (append a node at the end of a
  segment; needed for the forward walk's invariant) and `last_or_snoc`
  need induction; both are a few lines.

Compared with WP: the VST spec has no liveness bookkeeping (`mem`,
`all_live`, `unchanged`, `dll_frame`, the guiding `others_live` asserts
all disappear), and nothing is trusted beyond VST and `clightgen`.  The
price is the proof script: ~300 tactic sentences against WP's 3 small
Coq lemmas, because every statement is a tactic step and every
branch join is hand-written.

### Candidates for an SMT checker (SMTCoq)

Not installed or tried; this is a reading of the proof.  The goals
left by Floyd and closed by hand are few, because `entailer!` already
discharges the pure arithmetic (via `lia`/`rep_lia`):

- **Propositional / equality facts (about 30 steps).**  `discriminate`
  on `false = true` for the unreachable subcomparator branches (13),
  `contradiction`/`congruence` after `p = nullval` vs `isptr p` or
  `l <> nullval` (12; the `isptr p` fact itself comes from an SL
  entailment, `assert_PROP (isptr p) by entailer!`, so only the last
  step is SMT-shaped), and the `iter_pre` side conditions of the
  `it_next` calls, e.g. `iter_pre nullval nullval nullval []` or
  `(p,y)::s' <> [] /\ p = hd_ptr ((p,y)::s') /\ …` (3).  These are in
  SMTCoq's fragment (EUF + datatypes as uninterpreted functions), but
  each is already a one-tactic step, so SMTCoq would save little.
- **List facts (2).**  `s1 ++ [] = s1` and `(s1 ++ [x]) ++ s2 =
  s1 ++ x :: s2`: need list axioms or induction; SMTCoq has no
  induction, so they would need the lemmas as hypotheses.
- **Arithmetic: none by hand.**  `0 <= k + 1 <= n` from `k < n`,
  `Int.repr` ranges, `Zlength contents = n`: all closed inside
  `entailer!`.  If `lia` were too slow in larger benchmarks, these are
  the goals SMTCoq (LIA) would take.

Not for SMTCoq: every separation-logic entailment (`entailer!` on
`… |-- dlseg …`, `cancel`, `sep_apply dlseg_snoc`, the induction in
`dlseg_snoc`, the `saturate_local` facts) and every Floyd step.  These
are higher-order goals about `mpred`; this is where the effort went
(join assertions, folding/unfolding `dlseg`).

## Not done

- coqchk and Pétanque runs for B1 (both work on the smoke test).
- B1b/B1c (reverse walk, `get_first`/`get_last`, `sort`).
- The general (non-head) `add` and the subcomparator paths, as in
  the Frama-C version.
- Leak freedom as a theorem (`semax_prog` does not state it).
