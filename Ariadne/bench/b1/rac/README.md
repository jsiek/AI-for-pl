# B1 runtime checking: the "test first" pass (plan §5 step 0)

A prototype of plan §5 step 0 on benchmark B1 (`../b1.c`): sanitizer
builds of the driver on random inputs, an E-ACSL build of the annotated
code with executable twins (plan §4 item 5) in place of the logic
definitions E-ACSL cannot execute, and the seven WP mutants of
`../check.sh` rerun as tests.  It is a filter only: nothing here enters
a proof or the trust base.

```bash
./check.sh                  # needs the M0 image (../../../env); ~40 s
./check.sh 300 1 200 quick  # runs seed large [quick: skip the mutants]
```

**Status:** b1.c passes every step; all seven mutants are caught at
run time, five of them at the same annotation WP rejects them at.

## Output of `./check.sh`

```
step 0 (generate twins, b1_rac.c x8): 0.9 s; gen_twins: 1 inductive(s), 6 builtins, 15 ACSL definitions, 1 not translated (see rac_twins.txt)
    gen_rac: 48 dropped, 37 kept, 27 rewritten clauses
PASS: gen_rac.py clause splitting: ok: 3 clause-splitting cases
PASS: ASan+UBSan build of b1.c: ok: 300 runs, 7044 nodes, 74 with an injected allocation failure, largest n = 200
SKIP: MSan (clang 14 in the image has no MSan runtime)
step 1 (sanitizers, b1.c): 0.4 s
PASS: twin unit tests: ok
step 2 (twin unit tests): 0.3 s
PASS: E-ACSL build of b1.c: ok: 300 runs, 7044 nodes, 74 with an injected allocation failure, largest n = 200
step 3 (E-ACSL, b1.c): build 9.2 s, run 2.5 s
E-ACSL ignored 3 annotation(s) of b1_rac.rte.c (all warnings: build/eacsl_warnings.txt):
    b1_rac.rte.c:818: E-ACSL construct `labeled \offset' is not yet supported. Ignoring annotation.
    b1_rac.rte.c:2512: E-ACSL construct `\valid_function' is not yet supported. Ignoring annotation.
    b1_rac.rte.c:2554: E-ACSL construct `\valid_function' is not yet supported. Ignoring annotation.
    checks failed: 0 distinct, 0 total
coverage: 63 clauses checked at run time, 60 evaluated, 3 never evaluated, 2 side flags, 0 failures; 48 clauses not (or only partly) checked at run time
step 3b (coverage, b1.c): 14.9 s
mutant     ASan+UBSan             E-ACSL (first check to fire)
vacuity    -                      Assertion vacuity in b1  [ok]
uaf        heap-use-after-free    Precondition in sglib_dllist_get_first  [ok]
uaf_back   heap-use-after-free    Precondition in sglib_dllist_get_last  [ok]
nullchk    ubsan: null member access Assertion rte/mem_access in b1  [ok]
nullfirst  -                      Postcondition heads_list in sglib_dllist_get_first  [ok]
nulllast   oracle                 Postcondition last_of_list in sglib_dllist_get_last  [ok]
noinit     oracle                 Assertion payload_written in b1  [ok]
step 4 (mutants x7, both builds): 10.7 s
ASan start-up retries (DEADLYSIGNAL): 2
PASS: runtime checking of B1
```

(`build/` holds every intermediate file and log, `build/coverage.md`
the coverage report.  The mutants run in parallel, eight cores or more
help.  Run of 2026-11-06, 40 s wall time with container start-up.)

## The mutants (main result)

`oracle` is the driver's own functional check (b1 returns the last value
it stored, see `rac_main.c`), not part of b1.c's spec; it is listed so
the table shows what plain testing would have found.

| Mutant | WP (`../check.sh`) rejects at | ASan + UBSan | E-ACSL: first check to fire | Same place as WP? |
|--------|-------------------------------|--------------|-----------------------------|-------------------|
| `vacuity` (`assert \false` at the end of b1) | the assert | not caught (no assert in this build) | the assert | yes, but it means only "the end of b1 is reachable": vacuity of the spec is a proof-only question, runtime checking cannot test it |
| `uaf` (forward walk after the free loop) | `get_first`'s precondition at the call | heap-use-after-free | `get_first`'s precondition `list == \null \|\| in_live_list(list)` (twin `rac_head` finds no live list) | yes |
| `uaf_back` (backward walk after the free loop) | `get_last`'s precondition | heap-use-after-free | `get_last`'s precondition | yes |
| `nullchk` (no NULL check after allocation) | the `live` / `rte_mem_access` assert on `l->i` | null member access (UBSan), **only with fault injection** | RTE `mem_access` on `l->i = input[k]` in b1, **only with fault injection** | yes |
| `nullfirst` (`get_first` returns NULL) | postcondition `heads_list` | not caught: no memory error, and b1's result does not change | postcondition `heads_list` | yes |
| `nulllast` (`get_last` returns NULL) | postcondition `last_of_list` | oracle (wrong result) | postcondition `last_of_list` | yes |
| `noinit` (`l->i = input[k];` removed) | `add`'s precondition `elem_init` at the call | oracle (ASan fills fresh blocks with 0xbe; MSan would report the read, but is unavailable) | `add`'s precondition `elem_init` | yes |

Notes:

- **`nullchk` needs a failing malloc.**  The driver injects one: every
  4th run with n > 0, allocation number `rac_fail_at` (random in 0..n-1)
  returns NULL (`rac_alloc.c`).  Without injection neither build sees
  the mutant.  Injection also tests b1's real NULL-check path (74 runs).
- **The E-ACSL check comes first** in every case where both fire: it is
  at the call (precondition) rather than at the bad access, so it names
  the annotation, the same one WP names.
- **Two mutants only the spec catches**: `nullfirst` (no build without
  the spec notices) and `vacuity`.  `noinit` would also be spec-only
  without the oracle and without ASan's malloc fill.
- The table is checked: `check.sh`'s `expect` fails if any entry changes.

## What runs where

| Step | What | How |
|------|------|-----|
| 0 | generate | `../../../harness/acsl_expand.py` expands the spec template invocations of b1.c (`../../sglib_spec`; `ARIADNE_ALLOC` and `ARIADNE_FREE` are kept, rac.h redefines them), and every later step reads the expanded text; `../../../rac/gen_twins.py` generates the twins, the executable spec block and the manifest from b1.c into `build/twins/`; `gen_rac.py` turns b1.c (and each mutant from `../mutants.py`, shared with `../check.sh`) into `build/<v>/b1_rac.c` plus `annotations.txt`, the fate of every clause |
| 1 | sanitizers | gcc `-fsanitize=address,undefined`, b1.c unchanged (ACSL is comments), `rac_alloc.c` (malloc/free + registry + fault injection), `rac_main.c` (300 random runs: n = 0..5 always, n = 200 every 25th run, else 0..40; LeakSanitizer on) |
| 2 | twin unit tests | `rac_twins_test.c` under ASan + UBSan: good lists n = 0..5, a cycle through `ptr_to_next`, a cycle through `ptr_to_previous`, a broken back link, a repeated node, a freed node mid-list: every call returns, with the ACSL value, and reads no freed memory |
| 3 | E-ACSL | `frama-c -rte -rte-initialized @all` (as for WP, minus alignment, below) and `-print`, then `e-acsl-gcc` with the twins as builtins; twins compiled apart (`build/twins/rac_twins.c` and `../../../rac/rac_rt.c`, not instrumented) and linked |
| 4 | mutants | steps 1 and 3 on each mutant, in parallel; classified by `classify.py` |

MSan: the image's clang 14 has no compiler-rt runtimes
(`libclang_rt.msan-x86_64.a` missing), so the MSan step reports SKIP.
E-ACSL's `\initialized` checks (RTE `-rte-initialized @all`) cover the
same reads, and caught `noinit`.

## Executable twins

Generated from b1.c's spec block by `../../../rac/gen_twins.py` (rules,
limits: `../../../rac/README.md`) into `build/twins/` at every run:
`rac_twins.c` / `.h` (twins and builtins), `rac_spec.h` (the executable
spec block), `rac_twins.json` (manifest read by `gen_rac.py` and this
`check.sh`), `rac_twins.txt` (diagnostics).  For B1:

- **`dll` → `m_dll`, builtin `rac_dll`**: one branch per case;
  `dll_nil` matches `(_, \null, \Nil)`, `dll_cons` matches
  `\Cons(h, t)` with `h` the second argument, then checks
  `h != \null`, `\valid(h)` (the registry: "registered, not freed"),
  `h->ptr_to_previous == prev`, `!mem(h, t)` (C twin `tw_mem`), and
  `dll(h, h->ptr_to_next, t)` by a recursive call; step bound
  (`RAC_FUEL` steps, `RAC_DEPTH` levels).  Stricter than `dll` off the
  B1 path (valid non-heap nodes, dead nodes WP still calls `\valid`);
  every B1 use of `dll` is conjoined with `all_live`, so the
  conjunction has the same value.
- **Witnesses**, derived from `dll`'s cases (exported modes):
  `rac_dll_s_of_h(h)` (the nodes reached from `h`; was `rac_reach`),
  `rac_dll_prev_of_h(h)` (was `rac_prev`), `rac_dll_h_of_s`,
  `rac_dll_prev_of_s`, and the member walk `rac_dll_h_of_member(x)`
  (back along `ptr_to_previous`; was `rac_head`).  `live_dll` inherits
  them (it is `dll(...) && ...` of its own parameters).
- **Kept in ACSL** (E-ACSL runs them): `live`, `mem`, `all_live`,
  `all_init`, `live_dll`, `iter_at`, `iter_fields`; `in_live_list` with
  its binders replaced by witnesses (the member walk); `iter_pre` and
  `iter_ok` with their binders replaced by the witnesses of
  `../../sglib_spec/rac_witnesses.json` (below); `heap` / `dead` as the
  registry.
- **Not translated**: `unchanged` (two labels; only dropped annotations
  use it); the lemmas (proof facts).

**The iterator's witnesses** (`--witness-hints
../../sglib_spec/rac_witnesses.json`, rules in `../../../rac/README.md`).
`iter_pre(it)` and `iter_ok(it, cur)` say `\exists \list s, integer b,
f; iter_at(it, s, b, f) && ...`: the list through the iterator's
position.  No conjunct determines `s` by a mode of `dll`, but it can be
computed by walking links: from `prevelem` (or `nextelem`, or, for
`iter_ok` after the last node was returned, `cur`) back to the head
along `ptr_to_previous` (`rac_dll_h_of_member`), then forward
(`rac_dll_s_of_h`); `b` and `f` are the indices of `prevelem` and
`nextelem` in `s` (`rac_index`, -1 or `\length(s)` for NULL), `c` the
index of `cur`.  Both walks stop on a repeated node (Brent's cycle
detection) or after `RAC_FUEL` steps, and give "no witness" then.  A
witness only picks the value to test: `iter_at` is then checked in full,
so a wrong walk makes the check fail, never pass wrongly.  Twin unit
tests (`rac_twins_test.c`): `rac_index`; a back-link cycle not through
the head and a self loop (the walk stops on the repeated node); a
broken `previous` link (the walk skips a node, the list fails `dll`);
freed nodes, kept and not.

The generated files replace the hand-written `rac_twins.c` and
`rac_spec.h` of the first version, with the same mutant table and the
same outcome for every annotation (`annotations.txt` differs only in
the witness names).

Proving a twin against its predicate with WP was not done: the twins work on arena arrays and the registry, so the contract
`\result != 0 <==> dll(prev, h, s)` needs an abstraction function from
a `rac_seq` to `\list` and a registry invariant implying `\valid`; that
is a small verification project of its own (likely with Coq for the
induction), left for later.

## Liveness: registry, not E-ACSL's `\freeable`

`heap(b)` and `dead(v, b)` (ghost model, `ariadne_alloc.h`) become an
allocation registry in `../../../rac/rac_rt.c`, updated by the ariadne allocators
in `rac_alloc.c` (`rac_heap`, `rac_dead`, and `rac_heap_of(p)` /
`rac_dead_of(p)` for `heap(\base_addr(p))`, which find the registered
block containing `p`).  Why not E-ACSL's own `\freeable` / `\valid`:

- `heap(b)` is "b was ever returned by an allocator", true of dead
  blocks too; `\freeable` cannot tell a freed heap block from a stack
  address, so `!heap(\base_addr(input))` would change meaning;
- the twins are plain C (not instrumented) and must know whether a node
  may be read before reading it; the registry answers that, E-ACSL's
  shadow memory is not callable from there;
- E-ACSL 33 does not execute `\base_addr` at all;
- the same registry works in the sanitizer builds and the unit tests.

**Freed nodes in the E-ACSL builds (`-DRAC_KEEP_FREED`).**  In the
ghost model `free` changes only `__heap` (the block becomes `dead`);
`\valid` of the block and its contents persist, and the iterator's
contracts rely on that: B1's driver frees each node while iterating, and
`iter_at` still describes the whole list, freed prefix included (only
the nodes still to visit must be `live`).  So in the E-ACSL builds
`ariadne_free_dllist` marks the block dead in the registry and does not
release it, and `rac_valid` accepts such a block (`rac_keep_freed`).
Use after free stays caught: by the contracts' `live` (the registry's
`dead`) under E-ACSL, and by ASan in the sanitizer build, which frees
for real (mutants `uaf`, `uaf_back`).

E-ACSL's tracking is still used where the spec says `\valid`,
`\offset`, `\initialized`, and by every RTE check: use after free and
uninitialised reads in the code are E-ACSL's findings, not the
registry's.

## Translation rules (`gen_rac.py`)

`gen_rac.py` never translates an annotation by hand: every annotation of
b1.c (or a mutant) goes through these rules, and `annotations.txt`
records the outcome of each clause.

1. **Spec block → `rac_spec.h`.**  The ACSL block of logic definitions
   is replaced by the generated `build/twins/rac_spec.h`, found by its
   SHA-256 (recorded by `gen_twins.py`), so a mutant may not change the
   spec.  `#include "ariadne_alloc.h"` becomes `rac.h` (executable
   allocator contracts).
2. **Clauses and conjuncts.**  An annotation is split into clauses; the
   predicate of an assert / requires / ensures / invariant into its
   top-level conjuncts, each translated on its own.  A conjunct that
   cannot be translated is dropped (the check gets weaker, never wrong);
   a premise is never dropped, only a whole implication.  The split
   respects ACSL precedence: `==>`, `<==>`, `||`, `^^` and `?:` bind
   looser than `&&`, so a predicate with one of them at top level is a
   single conjunct (`a ==> b && c` is `a ==> (b && c)`; dropping `b`
   must not leave `c` unguarded), and `<==>` is not split at its `==>`.
   `test_gen_rac.py` (run by `check.sh`) checks these cases.
3. **Binders over lists or pointers.**  `\exists`: each list or pointer
   variable gets a witness from a conjunct that determines it (an
   exported mode of the manifest, or `rac_tail` of one for
   `\Cons(e, t)`, or the member walk), substituted in place; integer variables stay
   in an `\exists integer` over the remaining conjuncts (E-ACSL runs
   bounded integer quantifiers).  `\forall` over lists with a premise
   `dll(P, H, s) && ...`: `s` is determined, same substitution (exact
   witnesses only, no "any value").  A conjunct that uses a definition
   the manifest lists as dropped is dropped.  Dropped:
   `\forall` over pointers (no finite range) and over all lists with no
   determining premise (frame facts such as `frame`, `old_lists_live`).
4. **Labels.**  A witness under a label is computed at that label,
   `\at(rac_dll_s_of_h(H), L)`, only when `H` has the same value there
   (`\at(..., L)` or a constant); otherwise dropped (`rest`).  A spec
   predicate applied at a label (`dll{Pre}(...)`) is dropped: E-ACSL 33
   translates neither `P{L}(...)` nor `\at(P(...), L)` (it ignored
   `linked` silently, `tail` with a warning).
5. **List terms.**  `\nth`, `\length`, `\Cons`, `\Nil` → `rac_nth`,
   `rac_length`, `rac_cons`, `(rac_list)0`.
6. **`assigns` / `loop assigns`** are dropped (E-ACSL does not check
   them).

7. **Pointers over the registry.**  `\forall T *q; P ==> Q` where the
   conjuncts of `P` include `live(q)`, or `heap(\base_addr(q))` with
   `\offset(q) == 0`: `q` ranges over the allocation registry's slots,
   `\forall integer rac_i; 0 <= rac_i < rac_reg_count(0) ==> (P ==> Q)`
   with `q := rac_reg_nth(rac_i)` (the registry holds every block an
   allocator returned, which is what `heap` means).  Not when `q` occurs
   under `\at` or a label (`keep_prev`, `keep_next`, `keep_init`):
   E-ACSL 33 ignores such a clause, and still evaluates its other `\at`
   terms eagerly at the label, where `\at(*list, Pre)->previous` reads
   through NULL when the list was empty; dropped.

Outcome for b1.c (2026-11-06): 112 clauses; 37 kept, 27 rewritten, 48
dropped (57 before the iterator's witnesses and rule 7).  Every
requires and ensures is executed (32 of 32).  Dropped, with the reason
`annotations.txt` gives:

| Clauses | Reason |
|---------|--------|
| 6 `assigns`, 8 `loop assigns` | E-ACSL does not check assigns |
| asserts `frame` x2, `init_frame` x2, `back`, `forward`, `end`, `found`, `mid_back`, `mid_fwd`, `cmp_frame`, `start_cmp`, `old_lists_live`, `iter_after_free`; 4 loop invariants of `it_next`'s comparator loops | `\forall` over all lists: `s` is determined only by a premise at label `Pre` (`iter_at{Pre}(it, s, b, f)`, `all_init{Pre}(s)`) or by none (frame facts over every list); E-ACSL 33 does not evaluate a predicate under a label, and a witness computed at `Pre` would need the walk at `Pre` |
| asserts `written`, `start`, `others_live`, `old_nodes_live`, `new_live`, `new_dll`, `links`, `distinct`, `frame_prev`, `frame_next` | `\forall` over pointers whose premise is not `live` / `heap` (rule 7 does not apply) or is at label `Pre` |
| asserts `keep_prev`, `keep_next`, `keep_init` (in `add`) | `\forall` over pointers with the variable under `\at` / a label: E-ACSL 33 does not evaluate it (rule 7) |
| asserts `insert_list`, `inserted` | `\exists` over the list after the insertion (`t`): no walk from a known node determines it in the form the assert states |
| assert `eq_frame` | `iter_fields{Pre}`: a predicate under a label |

All dropped asserts are the prover role's (frame and liveness facts for
WP); the comparator loops are unreachable in B1 (no subcomparator).
E-ACSL 33 also ignores, with a warning, three kept clauses (listed by
`check.sh`: `old_prev` in `add`, a labelled `\offset`, and two RTE
`\valid_function` checks); the coverage report shows `old_prev` as
never evaluated.

## Coverage (plan Q11 step 0, `build/coverage.md`)

Step 3b builds b1.c again with `gen_rac.py --cov`: every clause kept or
rewritten is named `rac_cov_<n>` (`coverage_map.json` maps names to
clauses), and each side of a top-level implication or disjunction gets a
probe (`rac_side_<n>_<j>`: the antecedent; for disjunct k, "the first k-1
are false and disjunct k holds").  `../../../rac/rac_collect.c` replaces
E-ACSL's assertion function: it counts every evaluation of every check,
true and false, lets the run go on after a failure, never fails a probe,
and prints the counts at exit (on stderr: E-ACSL's runtime has released
its memory model by then, and file I/O there crashes).
`../../../rac/coverage.py` writes the report: per clause, the evaluations
per input, failures, how often each side held; flags for a clause never
evaluated, an antecedent that never held, a disjunct that was never the
one that held; and the clauses not checked at run time with the reason.

For B1's driver (300 runs, seed 1, n <= 200): 63 clauses checked at run
time, 60 evaluated, 0 failures.  Flagged:

- never evaluated: `old_prev` (ignored by E-ACSL 33, above), and the
  two `assert \true` in
  `it_next`'s comparator loops (unreachable in B1);
- antecedent never held: `it_init_on_equal`'s two requires guarded by
  `subcomparator != \null` (B1 never passes a comparator).

`../../selftest/rac.sh` gives the same report for sglib's self-test and
for random operation sequences, where the comparator paths run.

### E-ACSL workarounds (E-ACSL in Frama-C 33.0)

Found by building and running; each is applied mechanically
(`gen_rac.py`'s `wrap`, `null_args`, `base_addr`, `labels`):

| E-ACSL 33 limitation | Workaround |
|----------------------|------------|
| logic functions without a body are not executed | twins are C functions declared as builtins (`-e-acsl-builtins`); the C prototype, not a `logic` declaration, declares them |
| `-e-acsl-builtins` and E-ACSL's own `-rte -then -e-acsl` do not mix (builtins forgotten after `-then`) | two stages: `frama-c -rte ... -print` first, then `e-acsl-gcc` on the printed file |
| the builtin's prototype is dropped from E-ACSL's output (used only in logic), so gcc assumed `int` and truncated pointers | `gcc -include rac_twins.h` |
| `\let` on a pointer: "not yet supported" | substitute the witness for the variable |
| `\base_addr`: "not yet supported" | `heap_of(p)` / `dead_of(p)` via the registry |
| a function application as an argument of a predicate or of `\valid` / `\initialized`: "not yet supported" | builtins return `long`; calls written `(T)(0 + rac_f(...))` |
| a predicate specialised by its arguments' integer ranges: a node parameter called with `\null` got C type `int` and truncated real nodes | node arguments stay pointers; `\null` arguments of spec predicates become `rac_null` (a C global) |
| a `const` global: the runtime aborts marking it read-only | `rac_null` is not `const` |
| `\aligned` on a NULL pointer aborts the runtime ("Use of invalid address 0x0 in predicate") | alignment alarms off in the RTE stage (`-no-warn-unaligned-pointer`; B1 has no casts that could misalign) |
| printing data of a failed assertion evaluated `\offset` of NULL eagerly | `-e-acsl-no-assert-print-data` |
| `\initialized(p)` of a struct includes padding | the allocator writes `dllist`'s padding bytes, so a node is "initialised" when its three fields are, as in WP's model |
| `strtoull` has no memory model: every later verdict "unsound" (a warning per check) | the driver uses `atol` |
| `\valid_function` (RTE `pointer_call` in `it_next`): not supported | ignored (2 annotations; the subcomparator branch is unreachable in B1) |
| `\forall i; A \|\| B ==> P`: "missing guard for i"; the definition is ignored, and then every clause using it, silently (no warning at the use) | `gen_twins.py` writes `(\forall i; A ==> P) && (\forall i; B ==> P)` (`iter_at`) |
| an upper bound `i <= t` in a quantifier over a predicate's parameter: internal error "Interval inference was not performed on construct t + 1" | written `i < t + 1` |

GCC 12's ASan sometimes fails to start under this kernel's address-space
randomisation (endless `AddressSanitizer:DEADLYSIGNAL` before `main`,
about 1 start in 3; the container cannot turn ASLR off): `check.sh`
retries such a start up to 10 times and reports the count.

## Files

| File | What |
|------|------|
| `check.sh` | the steps above, timed |
| `gen_rac.py` | b1.c (or a mutant) → `b1_rac.c`, `b1_types.h`, `annotations.txt` |
| `test_gen_rac.py` | clause-splitting regression tests for `gen_rac.py` |
| `rac.h` | replaces `ariadne_alloc.h`: executable allocator contracts |
| `build/twins/` | generated by `../../../rac/gen_twins.py`: twins, executable spec block, manifest, diagnostics |
| `../../../rac/rac_rt.{h,c}` | runtime: registry, list values, step bound |
| `rac_twins_test.c` | unit tests of the generated twins (good and corrupt heaps) |
| `rac_alloc.c` | ariadne allocators: malloc/free, registry, fault injection, padding |
| `rac_main.c` | random-input driver with the oracle |
| `classify.py` | one-line summary of a run log, for the mutant table |
| `../../sglib_spec/rac_witnesses.json` | the iterator's witnesses (`gen_twins.py --witness-hints`) |
| `../../../rac/rac_collect.c` | E-ACSL assertion function of the coverage build: counts, never stops |
| `../../../rac/coverage.py` | the per-clause coverage report |
| `../mutants.py` | the seven mutants (shared with `../check.sh`) |

## Limitations

- **What is not checked**: assigns clauses; the prover-role asserts
  listed above (frame facts over all lists or all pointers, and
  predicates at another label); `old_prev`, which E-ACSL ignores;
  `\valid_function`.  A spec that is wrong only there passes this
  filter.
- **Sound only up to the inputs**: 300 random runs with n ≤ 200 (seed
  fixed; `./check.sh 1000 7 500` for more); no shrinking of failing
  inputs yet (the failing run's index is in the log).
- **Twins are trusted test code**: generated, but neither the generator
  nor the twins are proved against the predicates (see above); stricter
  than `dll` off the B1 path (non-heap or dead nodes), and bounded
  (`RAC_FUEL`, `RAC_DEPTH`).
- **`gen_rac.py` still parses annotations as text** (the spec block goes
  through Frama-C's AST in `gen_twins.py`, the annotations of the code
  do not); its witness rule is generic (the manifest), its other
  rewrites (`wrap`, `null_args`, `base_addr`) are E-ACSL 33 specific.
- **MSan not run** (no runtime in the image); E-ACSL's `\initialized`
  checks play its part.
- Cost: O(n^3) per run in the worst case (the twin's `!mem` is linear,
  and loop invariants re-walk the list); fine at n = 200 (1.2 s for 300
  runs).  Hash-consed list cells keep repeated witnesses from
  allocating; time is not memoised.
