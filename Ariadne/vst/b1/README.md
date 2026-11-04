# B1a + B1b in VST: sglib doubly linked list, memory safety

The same benchmark as `../../bench/b1` (Frama-C/WP), verified with VST
2.17 / CompCert 3.18 `clightgen` / Rocq 9.0.1 (image `ariadne-vst:dev`,
`../Dockerfile`), so the two pipelines can be compared (plan §9.2 Q10).
Stages, as in sglib's `samples/dllist.c`:

- **B1a**: build a list with `sglib_dllist_add`, walk it forward, and
  free every element while iterating with `sglib_dllist_it_init` /
  `sglib_dllist_it_next`;
- **B1b**: the forward walk starts from `sglib_dllist_get_first`, and a
  backward walk (via `ptr_to_previous`) from `sglib_dllist_get_last`
  runs before the free loop.

**Status: fully verified.**  Every function in `b1.c` has a
`semax_body` proof and the whole program has `semax_prog`
(`prog_correct`).  No `admit`, `Admitted`, or new axiom; `Print
Assumptions prog_correct` is exactly the smoke test's list (VST's
malloc/free assumptions plus classical axioms), unchanged from B1a.

```bash
cd Ariadne/vst/b1
./check.sh        # five PASS lines, ~3 min (see Metrics)
```

## What is verified

| Function | Proof | Status |
|---|---|---|
| `sglib_dllist_add` | `body_sglib_dllist_add` | proved (B1a) |
| `sglib_dllist_get_first` | `body_sglib_dllist_get_first` | proved (B1b) |
| `sglib_dllist_get_last` | `body_sglib_dllist_get_last` | proved (B1b) |
| `sglib_dllist_it_init_on_equal` | `body_sglib_dllist_it_init_on_equal` | proved (B1a) |
| `sglib_dllist_it_init` | `body_sglib_dllist_it_init` | proved (B1a) |
| `sglib_dllist_it_next` | `body_sglib_dllist_it_next` | proved (both call modes, B1a) |
| `b1` (driver, 4 loops) | `body_b1` | proved |
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
| `make_b1.py` | writes `b1.c` and the mutants `bad_*.c` from `../../bench/b1/b1_gen.c` |
| `b1.c` | types and the six sglib functions **byte-identical** to `b1_gen.c` (asserted by the script), the B1b driver with real `malloc`/`free`, a global `input[4]`, `main` |
| `bad_uaf.c`, `bad_uaf_back.c`, `bad_nonull.c` | types, sglib prototypes, and a mutated driver (still named `b1`) |
| `bad_nullfirst.c`, `bad_nulllast.c` | types and `get_first` / `get_last` with `(result) = NULL;` after the traversal |
| `verif_b1.v` | representation predicate, funspecs, proofs, `prog_correct`, `Print Assumptions` |
| `verif_bad.v` | the negative tests |
| `expected_assumptions.txt` | recorded `Print Assumptions prog_correct` (identical to `../smoke/expected_assumptions.txt`) |
| `check.sh` | the check (below) |

`b1.v`, `bad_*.v` (clightgen output) and `cert/` are generated and
git-ignored.

`b1_gen.c` already contains `get_first` and `get_last` (sglib's
`SGLIB_DL_LIST_GET_FIRST/LAST` expanded by `../../bench/b1/gen.sh`), so
B1b needed no change to the generated code: `make_b1.py` copies the two
functions with the same verbatim check as the others.

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
`last_or prev s` is the address of the last node of `s` (`prev` if `s`
is empty).

**Funspecs** (restricted as in the Frama-C contracts):

- `sglib_dllist_add(list, elem)`: `*list` holds the **head** of
  `dll nullval s` (any writable cell), `elem` is a separate malloc'd
  node with `i` set; afterwards `*list = elem` and
  `dll nullval ((elem, x) :: s)`.
- `sglib_dllist_get_first(list)`, `sglib_dllist_get_last(list)` (B1b):
  WITH `s1 s2`; `list = hd_ptr s2` and SEP `dll nullval (s1 ++ s2)`,
  that is, `list` is any node of a whole list (the node at position
  `length s1`), or NULL when `s2 = []`.  Post: the same
  `dll nullval (s1 ++ s2)`, and the result is `first_of s1 s2` /
  `last_of s1 s2`: NULL if `s2 = []`, otherwise the head
  `hd_ptr (s1 ++ s2)` / the last node `last_or nullval (s1 ++ s2)` of
  that same list.
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

### get_first / get_last against the Frama-C contracts

Frama-C (`../../bench/b1/b1.c`): `requires list == \null ||
in_live_list(list)`; `ensures list == \null ==> \result == \null`;
`heads_list`: there are `s, k` with `live_dll(\null, \result, s)` and
`nth(s, k) == list`; `last_of_list`: there are `h, s, k` with
`live_dll(\null, h, s)`, `nth(s, k) == list` and `\result ==
nth(s, length(s) - 1)`; `assigns \nothing`.

Differences, all in the direction of the VST spec being at least as
strong:

- **Which list.**  WP's postcondition says the result belongs to *some*
  live list containing `list`; since a node's links determine its list
  (`dll_links`), that is the argument's list.  The VST spec names it:
  the list in the postcondition is the one in the precondition,
  `s1 ++ s2`, node for node, with the same values.
- **Unchanged.**  `assigns \nothing` in ACSL; in VST the same
  `dll nullval (s1 ++ s2)` before and after, and nothing else is
  owned, so the function cannot touch anything else.
- **NULL in.**  ACSL requires nothing when `list == NULL`; the VST
  precondition always asks for some whole list `s1` (`s2 = []`), but
  `s1 = []` makes that `emp`, so every caller can meet it.
- **Liveness** is ownership (`data_at` + `malloc_token`) instead of
  `all_live` over the ghost heap.

## Negative tests (`verif_bad.v`)

The driver mutants are checked against the same `b1_spec` and sglib
funspecs; the function mutants against the funspec of the function
they change.  Each proof replays `verif_b1.v` up to the bad statement,
where the next Floyd step must fail (`Fail tac` succeeds only if `tac`
fails):

| Mutant | Refused step | Frama-C mutant |
|---|---|---|
| `bad_uaf.c`: forward walk (from `get_first`) after the free loop | the call `get_first(the_list)`: after the free loop no SEP clause mentions the head `p`, and `get_first`'s precondition `dll nullval ([] ++ (p, y) :: s')` needs `data_at … p`; `entailer!` cannot prove it | `uaf` (`get_first`'s precondition) |
| `bad_uaf_back.c`: backward walk (from `get_last`) after the free loop | the call `get_last(the_list)`, the same way | `uaf_back` (`get_last`'s precondition) |
| `bad_nonull.c`: no NULL check after `malloc` | `l->i = …` fails: malloc's post gives the cell only under `if eq_dec l nullval then emp else …`, and in the `l == NULL` case there is no cell at all (two `Fail forward`) | `nullchk` |
| `bad_nullfirst.c`: `get_first` returns NULL after its traversal | `return result;` in the non-empty case: the postcondition needs `nullval = first_of s1 ((p, y) :: s2)`, i.e. NULL equals the head of the list; `forward; entailer!` leaves exactly that goal | `nullfirst` (`heads_list`) |
| `bad_nulllast.c`: `get_last` returns NULL after its traversal | the same at `return`, with the last node `last_of …` | `nulllast` (`last_of_list`) |

`check.sh` counts 6 refusals: 2 with Floyd's "not obvious how to move
forward" message (`bad_nonull`), 4 with `entailer!`'s "No applicable
tactic".  For the two NULL mutants the empty-list case (`s2 = []`)
still proves: returning NULL is right there; the proof fails only in
the non-empty case, as it should.  The Frama-C `vacuity` mutant has no
counterpart: in VST an inconsistent precondition would show up as a
`b1_spec` nobody can call; `main` calls `b1` with the real global array
and `main_pre`, and `semax_prog` checks that.

**These tests only show that Floyd's tactics stop; the real guarantee
is VST's soundness**: if `semax_body` held for a driver mutant with a
satisfiable precondition, the mutant would be safe in Clight, but each
has a stuck execution (a load from a freed block; a store through NULL
when `malloc` fails).  Two caveats on the call refusals: the walk
invariants are the honest ones (what the program still owns), and the
`Fail` tries one witness for `get_first`/`get_last`'s WITH clause
(`s1 = []`, `s2` the freed list).  No witness can work, since every
witness with `hd_ptr s2 = p` needs a `data_at` for `p` (or `p = NULL`,
false here) and `free` consumed it, but the `Fail` does not check other
witnesses.

## check.sh

1. `make_b1.py` regenerates `b1.c` and the five `bad_*.c`
   byte-identically (and its own verbatim asserts pass);
2. `clightgen -normalize` on the six files; `coqc` on the ASTs;
3. lint: no `Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture` in the
   proof files;
4. `coqc verif_b1.v`; `Print Assumptions` output (`cert/assumptions.txt`,
   must start with `Axioms:`) equals `expected_assumptions.txt`;
5. `coqc verif_bad.v` and a `coqtop` transcript
   (`cert/bad_transcript.txt`): exactly 6 refusals, 2 with the
   "not obvious" message, 4 with "No applicable tactic", no `Error`.

Any failing command, an empty or missing report, or a count mismatch
prints `FAIL` and makes the script exit non-zero.  coqchk was not added
(the smoke test shows it works: `COQCHK=1 ../smoke/check.sh`).

## B1b: what it added

- **Funspecs**: `get_first`, `get_last` (above), and the helpers
  `first_of`, `last_of` (4 lines).
- **Helper lemmas** (all for splitting a list at an arbitrary node):
  `dlseg_app_split` / `dlseg_app_join` (`dlseg prev (a ++ b) t` is
  `dlseg prev a (hd_or b t) * dlseg (last_or prev a) b t`; induction),
  `dlseg_unsnoc` (take the last node off a segment), `dlseg_last_ptr`
  and `dlseg_last_pn` (the last node of a segment is a pointer),
  `snoc_cases` (a list is empty or `a' ++ [x]`), `hd_or_app_gen`,
  `first_of_nil`, `last_of_nil`.  None needed more than one try except
  `dlseg_last_pn` (one: `sep_apply` of a pure fact leaves `!! P && …`;
  `derives_trans` works).
- **Invariants**: `get_first`'s and `get_last`'s loops, and the
  driver's backward walk, all have the same shape as B1a's forward
  walk: the list is `a ++ b`, the current node is the head of `b` (or
  the last node of `a` for the driver's backward walk), and SEP is
  `dlseg nullval a (hd_ptr b) * dlseg (last_or nullval a) b nullval`.
  Each has a `continue:` variant that adds the fact the loop test just
  established (`a <> nil` or `tl b <> nil`).
- **Case splits before loads.**  A load whose value is a link field
  (`_dll_->ptr_to_previous`, `l->ptr_to_previous`) has a `tc_val`
  side condition: the value must be a pointer or NULL.  For
  `last_or nullval a` that is only known after exposing the last node
  of `a` (`snoc_cases`, `dlseg_unsnoc`) or from `dlseg_last_pn`.
- **Clight shape**: `for (; c; x = x->ptr_to_previous) ;` becomes a
  loop whose body is `t = x->ptr_to_previous; if (!(t != NULL))
  break;` and whose increment repeats the load.  The fall-through
  branch of `forward_if` comes first, then the `break`; a `break:`
  clause of `forward_loop` is wrong (it adds an extra goal that
  `entailer!` refuses) when the loop is the last statement of an `if` that
  has a join assertion.

## Comparison with Frama-C/WP (`../../bench/b1`)

Same C code (sglib part byte-identical), same driver except real
`malloc`/`free` instead of the ghost allocators, same contract
restrictions.

### Metrics

Line counts are non-blank, non-comment lines, counted by one script for
both stages (so the B1a column differs slightly from the hand counts in
the B1a version of this README).  Frama-C: ACSL lines at top level
(predicates, lemmas, contracts) vs. inside function bodies (loop
invariants and assigns, asserts); Coq: lines of the proof scripts in
`session/interactive/` between `Proof.` and `Qed.`.  VST: `Definition`
and `Fixpoint` sentences (spec), helper lemmas (statement + proof),
`forward_loop` / `forward_if` with a join / `assert_PROP` sentences
inside function proofs (annotations), and the remaining lines of the
function proofs and `prog_correct` (tactics).

| | Frama-C/WP B1a | Frama-C/WP B1b | VST B1a | VST B1b |
|---|---|---|---|---|
| Spec (definitions + contracts) | 77 | 106 | 99 | 118 |
| Annotations (invariants, asserts, join points) | 47 | 80 | 144 | 217 |
| Hand-written proof: function bodies | 0 | 0 | 179 tactic lines | 297 tactic lines |
| Hand-written proof: helper lemmas | 58 (3 Coq lemmas) | 107 (4 Coq lemmas) | 31 (6 lemmas) | 91 (15 lemmas) |
| Goals / automation | 183: Qed 109, SMT 71, Coq 3 | 222: Qed 126, SMT 92 (Alt-Ergo 82, CVC5 9, Z3 1), Coq 4 | no goal census: every statement is one Floyd step | same; 61 `entailer!`, 18 `sep_apply` in `verif_b1.v` |
| Negative tests | 3 mutants | 6 mutants (vacuity, uaf, uaf_back, nullchk, nullfirst, nulllast) | 2 mutants, 4 `Fail`s | 5 mutants, 6 `Fail`s |
| Extra trusted code | ghost allocator model, `-ariadne` plugin, `dead_heap` axiom, WP/Qed/SMT, ACSL lemmas as axioms until proved | same | `clightgen`; VST's 6 allocator assumptions | same |
| Wall-clock of `check.sh` (this machine, 24 cores) | see `../../bench/b1` | see `../../bench/b1` | 126 s | 182 s (197 s on a first run) |

B1b's share: VST +19 spec, +73 annotation, +118 tactic, +60 lemma
lines; Frama-C +29 spec, +33 annotation, +49 Coq lines (and 39 more
goals).  In both, B1b roughly doubled the hand-written proof for
three loops that only read the list.  The Frama-C cost went into the
index view of `dll` (`dll_links`, `dll_first`) and an SMT slowdown
fixed with one more assert in `add` (`../../bench/b1/README.md`); the
VST cost went into list splitting lemmas and into restating each
loop's state (invariant, continue, join) in full.

### Effort, honestly

**B1a** (earlier session): about 50 edit/compile iterations of
`verif_b1.v` (each `coqc` run 30-60 s), from no VST proof to
`prog_correct`; `add` and `it_init*` were quick, `it_next` and `b1`
took most of the time.

**B1b** (this session, measured): wall-clock about 55 minutes (07:31 to
08:26), from reading the B1a files to the commit; of that, 26 minutes to
a fully proved `verif_b1.v`, 10 more for `verif_bad.v` and `check.sh`,
the rest for metrics and this README.  Compile iterations: 17 runs of `coqc
verif_b1.v` (16 failed, the 17th proved everything), 2 of `coqc
verif_bad.v`, plus 16 `coqtop` runs to print a goal.  Failed `coqc`
runs, by where the error was:

| Function / part | Failed runs | Cause of each failure |
|---|---|---|
| helper lemmas | 1 | `sep_apply` of a pure entailment in `dlseg_last_pn` |
| `get_first` | 8 | impossible branch is `false = true` (`discriminate`, not `contradiction`); a typo of mine in a `sed` edit that hit `add`'s proof; a load before the case split (`tc_val`); goal order of `forward_if` (fall-through first); missing `forward` over the empty rest of the loop body; leftover `a' ++ [x] <> []`; a `break:` clause that left an extra goal `entailer!` refused (2 runs) |
| `get_last` | 1 | leftover `tl b <> nil` (the other four `get_first` fixes were applied to both at once) |
| `b1` driver | 5 | leftover `match` from `first_of` / `last_of` (2); `tc_val` of `last_or nullval a'` (needed `dlseg_last_pn`); a hypothesis name; a variable name clash (`r`) between two loops |
| `verif_bad.v` | 1 (it compiled) | the two use-after-free `Fail`s failed for the wrong reason (a lost `is_pointer_or_null` fact made the load of `the_list` leave a `tc_val` goal); caught by reading the transcript, fixed by keeping the fact as in B1a |

The proofs of `get_first` and `get_last` came out in the first
attempt's structure; every failure was a local Floyd detail.  The
driver's backward walk reused the shape of the forward walk.

What Floyd did automatically: every field load and store, the
malloc/free/sglib calls (`forward_call` with the WITH tuple), all
typechecking side conditions once the right node was exposed, and
almost all entailments (`entailer!`).  No arithmetic goal was proved
by hand.

Where I got stuck or needed manual work (B1a, still true in B1b):

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
  start and write all join assertions in unfolded form; in B1b, split
  the list with `sep_apply` (which touches only the precondition).
- **An elaboration failure in loop invariants.**  A `data_at` of a
  struct value written inline under `EX` in a `forward_loop` argument
  fails with "has type environ -> mpred while it is expected to have
  type mpred" (it works with explicit `@exp (environ -> mpred) _ T
  (fun x => …)`, and in funspecs).  Workaround: the definitions
  `it_val`/`iter_at`; in B1b, invariants that keep the nodes folded in
  `dlseg` and expose them inside the loop body instead.
- **Clight shape.**  `clightgen` turns `for (int k = 0; …)` into a
  `for` whose init `forward_loop` executes, `t = f(); l = t;` is
  absorbed by `forward_call`, and the later loops' inits are separate
  calls; each mismatch showed up as a Floyd error message, which was
  usually precise enough to fix the next step.
- **Unreachable branches.**  The subcomparator branches
  (`it->subcomparator != NULL`, with a function-pointer call inside a
  loop) are discharged by `discriminate` on `false = true` right after
  `forward_if`; no spec for a function pointer was needed.

Compared with WP: the VST spec has no liveness bookkeeping (`mem`,
`all_live`, `unchanged`, `dll_frame`, `in_live_list`, the guiding
`others_live` asserts all disappear), and nothing is trusted beyond VST
and `clightgen`.  The price is the proof script: every statement is a
tactic step and every branch join is hand-written.

### Candidates for an SMT checker (SMTCoq)

Plan item, not installed or tried; this is a reading of the proof.
The goals left by Floyd and closed by hand are few, because
`entailer!` already discharges the pure arithmetic (via
`lia`/`rep_lia`):

- **Propositional / equality facts.**  `discriminate` on `false = true`
  for impossible branches (13 in B1a, 5 more in B1b: the NULL tests of
  `get_first`, `get_last` and the backward walk),
  `contradiction`/`congruence` after `p = nullval` vs `isptr p` or
  `l <> nullval` (12 in B1a, 5 more in B1b, plus 6 `contradiction`s
  on `b <> nil`-style hypotheses right after a `destruct`; the `isptr p`
  fact itself
  comes from an SL entailment, `assert_PROP (isptr p) by entailer!`, so
  only the last step is SMT-shaped), and the `iter_pre` side
  conditions of the `it_next` calls (3).  These are in SMTCoq's
  fragment (EUF + datatypes as uninterpreted functions), but each is
  already a one-tactic step, so SMTCoq would save little.
- **List facts.**  B1a: `s1 ++ [] = s1` and `(s1 ++ [x]) ++ s2 =
  s1 ++ x :: s2`.  B1b adds 4 more of the same kind:
  `(a ++ [x]) ++ b = a ++ x :: b` (3, `rewrite <- app_assoc`),
  `a ++ [x] <> []` (2), `tl (x :: y :: b) <> []`, and the two
  `match s with [] => … end = …` goals from `first_of`/`last_of`
  (`destruct s; reflexivity`).  They need list axioms or induction;
  SMTCoq has no induction, so they would need `app_assoc` etc. as
  hypotheses.  These were the most frequent cause of a failed run in
  B1b (4 of 16), because `entailer!` leaves them silently and the next
  bullet then fails; an automatic list-equality solver here would have
  saved iterations, not lines.
- **Arithmetic: none by hand.**  `0 <= k + 1 <= n` from `k < n`,
  `Int.repr` ranges, `Zlength contents = n`: all closed inside
  `entailer!`.  If `lia` were too slow in larger benchmarks, these are
  the goals SMTCoq (LIA) would take.

Not for SMTCoq: every separation-logic entailment (`entailer!` on
`… |-- dlseg …`, `cancel`, `sep_apply dlseg_snoc` / `dlseg_unsnoc`, the
inductions in `dlseg_app_split`/`join` and `dlseg_snoc`, the
`saturate_local` facts) and every Floyd step.  These are higher-order
goals about `mpred`; this is where the effort went (join assertions,
folding/unfolding `dlseg`, choosing where to split the list).

## Not done

- coqchk and Pétanque runs for B1 (both work on the smoke test).
- B1c (`sort`).
- The general (non-head) `add` and the subcomparator paths, as in
  the Frama-C version.
- Leak freedom as a theorem (`semax_prog` does not state it).
