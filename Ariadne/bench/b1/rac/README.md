# B1 runtime checking: the "test first" pass (plan §5 step 0)

A prototype of plan §5 step 0 on benchmark B1 (`../b1.c`): sanitizer
builds of the driver on random inputs, an E-ACSL build of the annotated
code with executable twins (plan §4 item 5) in place of the logic
definitions E-ACSL cannot execute, and the seven WP mutants of
`../check.sh` rerun as tests.  It is a filter only: nothing here enters
a proof or the trust base.

```bash
./check.sh                  # needs the M0 image (../../../env); ~18 s
./check.sh 300 1 200 quick  # runs seed large [quick: skip the mutants]
```

**Status:** b1.c passes every step; all seven mutants are caught at
run time, five of them at the same annotation WP rejects them at.

## Output of `./check.sh`

```
step 0 (generate twins, b1_rac.c x8): 0.4 s; gen_twins: 1 inductive(s), 6 builtins, 8 ACSL definitions, 1 not translated (see rac_twins.txt)
    gen_rac: 27 dropped, 24 kept, 1 partly-kept, 22 rewritten clauses
PASS: gen_rac.py clause splitting: ok: 3 clause-splitting cases
PASS: ASan+UBSan build of b1.c: ok: 300 runs, 7044 nodes, 74 with an injected allocation failure, largest n = 200
SKIP: MSan (clang 14 in the image has no MSan runtime)
step 1 (sanitizers, b1.c): 0.4 s
PASS: twin unit tests: ok
step 2 (twin unit tests): 0.2 s
PASS: E-ACSL build of b1.c: ok: 300 runs, 7044 nodes, 74 with an injected allocation failure, largest n = 200
step 3 (E-ACSL, b1.c): build 7.2 s, run 1.2 s
E-ACSL ignored 2 annotation(s) of b1_rac.rte.c (all warnings: build/eacsl_warnings.txt):
    b1_rac.rte.c:1947: E-ACSL construct `\valid_function' is not yet supported. Ignoring annotation.
    b1_rac.rte.c:1987: E-ACSL construct `\valid_function' is not yet supported. Ignoring annotation.
mutant     ASan+UBSan             E-ACSL (first check to fire)
vacuity    -                      Assertion vacuity in b1  [ok]
uaf        heap-use-after-free    Precondition in sglib_dllist_get_first  [ok]
uaf_back   heap-use-after-free    Precondition in sglib_dllist_get_last  [ok]
nullchk    ubsan: null member access Assertion rte/mem_access in b1  [ok]
nullfirst  -                      Postcondition heads_list in sglib_dllist_get_first  [ok]
nulllast   oracle                 Postcondition last_of_list in sglib_dllist_get_last  [ok]
noinit     oracle                 Precondition elem_init in sglib_dllist_add  [ok]
step 4 (mutants x7, both builds): 8.8 s
ASan start-up retries (DEADLYSIGNAL): 1
PASS: runtime checking of B1
total 17.80 s
```

(Container start-up is included; `build/` holds every intermediate file
and log.  The mutants run in parallel, eight cores or more help.)

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
| 0 | generate | `../../../rac/gen_twins.py` generates the twins, the executable spec block and the manifest from b1.c into `build/twins/`; `gen_rac.py` turns b1.c (and each mutant from `../mutants.py`, shared with `../check.sh`) into `build/<v>/b1_rac.c` plus `annotations.txt`, the fate of every clause |
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
  `all_init`, `live_dll`; `in_live_list` and `iter_ok` with their
  binders replaced by witnesses; `heap` / `dead` as the registry.
- **Not translated**: `unchanged` (two labels; only dropped annotations
  use it); the lemmas (proof facts).

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

Outcome for b1.c: 74 clauses; every requires, ensures and loop
invariant is executed (24 kept as is, 22 rewritten); dropped are the 12
assigns clauses and 15 asserts that the prover role added (frame and
liveness-carrying facts: `frame` x3, `init_frame` x2 and one conjunct
of a third, `linked`, `linked_init`, `tail`, `live_frame`, `rest`,
`old_nodes_live`, `old_lists_live`, `others_live`, `other_lists_live`,
`other_live_dlls`).  The frozen contracts are fully checked.

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
| `../mutants.py` | the seven mutants (shared with `../check.sh`) |

## Limitations

- **What is not checked**: assigns clauses; the 15 prover-role asserts
  listed above (frame facts over all lists or all pointers, and
  predicates at another label); `\valid_function`.  A spec that is
  wrong only there passes this filter.
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
