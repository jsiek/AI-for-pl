# B1a + B1b: sglib doubly linked list, memory safety (M1 baseline)

Benchmark B1 (plan §6.2), first two stages, as in sglib's
`samples/dllist.c`:

- **B1a**: build a list with `sglib_dllist_add`, and free every element
  while iterating with `sglib_dllist_it_init` / `sglib_dllist_it_next`;
- **B1b**: walk it forward from `sglib_dllist_get_first` and backward
  (via `ptr_to_previous`) from `sglib_dllist_get_last`.

**Status: fully verified**: every goal,
including lemmas, is proved; use-after-free is covered by the ghost
liveness model (`-ariadne`), and reads of uninitialised memory by RTE's
initialisation checks (see "Initialisation").

```bash
./check.sh     # needs the M0 image and the plugin built; eight PASS lines
./run.sh       # just the proof run, with the goal census
```

## Files

| File | What |
|------|------|
| `../sglib/` | sglib at commit `cf92b44e` (MIT): `sglib.h`, `LICENSE`, `samples/dllist.c` |
| `gen_in.c`, `gen.sh` | expand sglib's macros for the sample's instantiation and format them with `clang-format-14` into `b1_gen.c` (plan Q4: annotate the preprocessed code) |
| `b1.c` | `b1_gen.c` between `BEGIN/END GENERATED` markers, code unchanged, with ACSL inserted; plus the spec and our driver `b1` |
| `session/interactive/*.v` | the Coq proof scripts (WP session) |
| `run.sh` | `-ariadne` + WP: the five B1a functions, then the lemmas |
| `check.sh` | `run.sh` plus seven mutants that must be rejected |
| `mutants.py` | writes the seven mutants (used by `check.sh` and `rac/check.sh`) |
| `rac/` | runtime checking (plan §5 step 0): sanitizers, E-ACSL with executable twins, the mutants as tests; see `rac/README.md` |
| `b1_frozen.c` | the frozen-only variant (M3): `b1.c` without the human's internal annotations and lemmas; see "Frozen-only variant" |

The driver replaces the sample's `main`: an input array instead of
`argv`/`sscanf`, no `printf` (body-less libc functions are not
instrumented, see `plugin/README.md`), ariadne allocators instead of
`malloc`/`free`, and a NULL check after allocation, which the sample
lacks (mutant `nullchk` shows the check is needed).  `l` is declared
with `= NULL` (see "Initialisation").

## Goal census (M1)

321 goals, all proved (310 for the 7 functions, 11 lemmas).  Earlier
stages, without initialisation checks: B1a + B1b 222 (214 + 8), B1a
alone 183.

| Closed by | B1a + B1b + init | B1a + B1b | B1a alone |
|-----------|------------------|-----------|-----------|
| WP's simplifier (Qed) | 189 | 126 | 109 |
| Alt-Ergo 2.6.4 | 115 | 82 | 65 |
| CVC5 1.2.1 | 9 | 9 | 5 |
| Z3 4.13.4 | 3 | 1 | 1 |
| Coq 9.0.1 (hand-written scripts) | 5: `mem_cons`, `all_live_cons`, `all_init_cons`, `dll_frame`, `dll_links` | 4 | 3 |

(The split between the SMT provers moves by a goal or so from run to
run: all three run in parallel and the first to finish is counted.)

Mutants (`check.sh`), each rejected:

| Mutant | Rejected by |
|--------|-------------|
| `vacuity`: `assert \false` at the end of `b1` | the assert (spec consistent) |
| `uaf`: forward walk after the free loop | `get_first`'s precondition at the call (the list's nodes are dead) |
| `uaf_back`: backward walk after the free loop | `get_last`'s precondition at the call |
| `nullchk`: no NULL check after allocation | the `live` assert on `l->i` |
| `nullfirst`: `get_first` returns NULL after its traversal | its postcondition `heads_list` |
| `nulllast`: `get_last` returns NULL after its traversal | its postcondition `last_of_list` |
| `noinit`: the driver does not store `input[k]` into the new node (`l->i = input[k];` removed) | `add`'s precondition `elem_init` at the call |

## The specification (for review: frozen spec, plan §4 and guardrail 3a)

All in `b1.c`; these are the definitions a human must approve.

- `live(p)`: `p` is valid, at offset 0, a heap block, and not dead.
- `mem(p, s)`, `all_live(s)`, `all_init(s)`: membership in,
  liveness of, and initialisation of (every field of every node), a
  sequence of nodes (`\list<dllist *>`).
- `dll(prev, h, s)` (inductive): following `ptr_to_next` from `h` gives
  exactly `s`; each node is valid, its `ptr_to_previous` is its
  predecessor (`prev` for `h`), and none repeats.  **Shape only**:
  liveness is kept apart in `all_live`, so `alloc`/`free` (which change
  only `__heap`) leave `dll` syntactically unchanged.  An earlier
  version with liveness inside `dll` left 6 goals SMT could not close.
- `live_dll(prev, h, s) = dll(prev, h, s) && all_live(s) && all_init(s)`.
- `unchanged{L1,L2}(s)`: the nodes' link fields are equal at `L1` and
  `L2` and still valid at `L2`.
- `iter_ok(it, cur)`: iterator after `it_init`/`it_next` without a
  subcomparator: backward walk done, `nextelem` starts a live list, and
  `cur` (the element just returned) is live and not in that list; the
  fields `it_next` reads (`subcomparator`, `prevelem`, `nextelem`) are
  initialised.

Lemmas: `mem_cons`, `all_live_cons`, `all_live_nil`, `all_init_cons`,
`all_init_nil` (list facts), `dll_null`, `dll_inv`, `live_dll_inv`
(unfolding), `dll_frame` (induction), and B1b's `dll_links`,
`dll_first`.  Coq proves `mem_cons`, `all_live_cons`, `all_init_cons`,
`dll_frame`, `dll_links`; SMT the rest.

Contracts (restricted to what B1a uses; noted as such):

- `sglib_dllist_add(list, elem)`: `*list` is initialised and is the
  **head** of a live list (`live_dll(\null, *list, s)`), `elem` is live,
  not in it, and its `i` field is initialised (`elem_init`); afterwards
  `*list` is initialised and heads a live list.  sglib allows `*list` to be any
  element; the general contract is future work.
- `it_init`, `it_init_on_equal` (with `subcomparator == \null`),
  `it_next` (no subcomparator, and the three fields it reads
  initialised): establish / preserve `iter_ok`.
- The driver `b1(input, n)`: `input[0 .. n-1]` is readable and
  initialised, and `input` is not a heap block (`!heap`, which implies
  the old `!dead` precondition).  The
  subcomparator paths (calls through a function pointer) are not
  verified; their branches are unreachable under these preconditions.

Annotations the agent role of plan §12 would write (not part of the
frozen spec, all proved): loop invariants and `loop assigns` in `b1`;
asserts `old_nodes_live`/`old_lists_live` after allocation and
`others_live`/`other_lists_live` after free (carry liveness across the
`__heap` change); a `frame` assert at the end of `add`, `it_init_on_equal`,
and `it_next` (lets `dll_frame` apply across the writes).  For
initialisation: `init_frame` next to each `frame`, `old_head_init`,
`linked_init`, `tail`, `single` in `add`, `it_init`, `live_frame`,
`rest` in `it_next`, `other_live_dlls` after free, and loop invariants
for `the_list`, `input`, and (backward walk) `live(l) && \initialized(l)`.

## What M1 taught (input for M2/M3)

- **Hard goals are frame and unfolding goals** for the shape predicate,
  not the safety checks themselves.  They closed with: separating shape
  from liveness, three list lemmas, and a handful of guiding asserts;
  only 3 lemmas needed Coq, each under 25 lines.
- **Missing `loop assigns`** made WP forget everything (even
  `\valid(&the_list)`); set comprehensions over heap blocks express
  "fields of any heap node".  One term per comprehension.
- **Every pointer parameter needs a liveness precondition**: the plugin
  checks reads through `input` too.
- **Termination** is off (`-generated-spec-custom terminates:skip`),
  per plan §1.4.
- **Coq by hand**: run `coqc -native-compiler no -R
  /home/rocq/.opam/4.14.2/lib/why3/coq Why3 …` on a session file; the
  image's native compiler fails on Why3's list library.  WP's own check
  (`coqtop -batch`) is unaffected.
- Not yet done: the overlay check (stripped `b1.c` equals `b1_gen.c` +
  driver), and a certificate bundle (`coqc` + `coqchk` of the Coq
  goals, axiom list).

## B1b: what it added

- **Contracts**: `get_first` and `get_last` accept any node of a whole
  live list (`in_live_list`).  NULL in gives NULL out; otherwise the
  result is the head (`heads_list`) or the last node (`last_of_list`)
  of *the same* live list that contains the argument.  (A first version
  only said "some live list", which a function returning NULL would
  meet; mutants `nullfirst`/`nulllast` now check this.)  Loop invariant
  in both: the current node and the argument are nodes of one live
  list.
- **Lemmas**: `dll_links` (index view: node k's previous link is node
  k-1, or `prev` at k = 0; its next link is node k+1, or NULL at the
  end; induction, Coq, 50 lines) and `dll_first` (only node 0 has a NULL
  previous link in a whole list; SMT, from `dll_links`).
- **Asserts**: `at_head` at the end of `get_first`, `at_last` at the
  end of `get_last`, `head_is_node0` in the driver, and `linked` in
  `add`.
- **An SMT side effect worth knowing.**  New lemmas are hypotheses of
  every goal, not only the goals that need them.  Adding
  `dll_nth0` (`dll(prev, h, s) && h != NULL ==> nth(s, 0) == h`) made
  `add`'s postcondition, proved in B1a, time out even at 180 s
  (`lemma_ablation.sh` found the culprit by removing lemmas one at a
  time).  The fix was to drop `dll_nth0` (the fact follows from
  `dll_inv`) and to give `add` one more guiding assert (`linked`);
  `dll_links` and `dll_first` alone still slow `add` without it.
- **Lemma order matters**: a lemma can use only the lemmas declared
  before it (`dll_first` failed until moved below `dll_links`).
- **Coq detail**: Why3's `Length.length` is a real fixpoint, so `cbn`
  computes `length nil`; WP writes `-1 + i` as `Z.opp 1 + i`, so match
  indices from the goal rather than typing the literal.

## Initialisation

**Why.**  A comparison with the VST prototype (`../../vst/`) showed a
gap: in VST a load must produce a defined value (`data_at_` holds
undefined contents, `data_at` known ones), but RTE does not add
initialisation checks unless asked, so B1 as first verified would
also have accepted a driver that reads a node's `i` before writing
it.  With `-rte-initialized @all` added to the unchanged B1b files,
WP made 289 function goals and left 18 `rte_initialization` goals open
(in `add`, `it_init_on_equal`, `it_next`, `get_first`, `get_last`,
`b1`), plus a few that now timed out.  The cause: the spec never said
that list nodes, the iterator, `*list`, or `input` are initialised.

**What changed** (human-approved change to the frozen spec):

- `run.sh` and the mutant runs of `check.sh` pass `-rte-initialized
  @all` (an `\initialized` assert before every read of a scalar
  lvalue) and `-wp-no-filter-init` (below).
- New predicate `all_init(s)`: every node of `s` is `\initialized` as a
  whole struct (all three fields); lemmas `all_init_cons` (Coq, a copy
  of `all_live_cons`'s script) and `all_init_nil` (SMT), like
  `all_live`'s.  `live_dll` now includes `all_init(s)`; `dll` and its
  Coq scripts are unchanged.
- Contracts: `add` requires `\initialized(list)` and `elem_init:
  \initialized(&elem->i)` and ensures `\initialized(list)` (`add`
  assigns `*list`, which also forgets its initialisation); `it_next`
  requires its three read fields initialised, and `iter_ok` promises
  them; `b1` requires `\initialized(input + (0 .. n-1))` and
  `!heap(\base_addr(input))` (without it, `input` could overlap a
  node's link fields, which `add` assigns, so `input`'s initialisation
  would not survive the loop).
- One C change, in our driver: `dllist *l = NULL`.  WP gives a call's
  result to a local only the initialisation the local already had
  (hypothesis `Init_l_before ==> Init_l_after`): with `n == 0`, `l =
  sglib_dllist_get_first(...)` would leave `l` "uninitialised" although
  every callee returns an initialised value.  Stating
  `\initialized(&l)` in a loop invariant does not help: taking `&l`
  makes the plugin admit `!heap(&l)`, WP then keeps `l` in memory, and a
  call result stored in memory has unknown initialisation.
- Proof annotations (agent-level, all proved): listed under "The
  specification" above; `head_is_node0` now states
  `live_dll(\null, the_list, \Cons(the_list, t))` directly (the old form
  took 29 s with the new hypotheses, the new one 5 s), and lemma
  `live_dll_inv` (unfold one node of `live_dll`) keeps the forward walk's
  invariant provable in mutant `uaf`.

**WP pitfall: `-wp-filter-init`.**  By default WP drops hypotheses that
mention initialisation ("aggressive filtering").  Once `live_dll`
mentioned `\initialized`, that removed every `live_dll` hypothesis and
44 goals failed, including liveness asserts unrelated to
initialisation.  `-wp-no-filter-init` keeps them.

**Mutant `noinit`** drops `l->i = input[k];`.  It is rejected at
`add`'s precondition `elem_init` at the call, not at an
`rte_initialization` goal: the fact "nodes are initialised" enters the
proof at that precondition, so that is the first annotation that a
missing write breaks; the later reads of `l->i` are proved from it.

**Counts.**  321 goals (310 functions + 11 lemmas), all proved; Qed
189, Alt-Ergo 115, CVC5 9, Z3 3, Coq 5.  Slowest goal 14 s (`b1`'s call
to `add`, `live_dll` precondition).  A fresh `run.sh -wp-cache none`
takes about 40 s (before this change several goals ran into the 60 s
timeout; the initial reproduction took about 3 min); `check.sh` takes
about 8 min, mostly the mutants' 60 s timeouts.

## Frozen-only variant (`b1_frozen.c`, M3)

The starting point of milestone M3: what the annotator gets.  Each item
of `b1.c` is kept or removed by what plan §4 item 4 and §7 (2, 3a) call
frozen:

| Item of `b1.c` | Decision | Why |
|---|---|---|
| predicates `live`, `mem`, `all_live`, `all_init`, `unchanged`, `live_dll`, `in_live_list`, `iter_ok`; inductive `dll` | kept | shape predicates: frozen spec (§4.1, guardrail 3a: the agent may not add or change definitions) |
| `requires` / `assigns` / `ensures` of `add`, `get_first`, `get_last`, `it_init_on_equal`, `it_init`, `it_next`, `b1` (with their names, e.g. `elem_init`, `heads_list`) | kept | frozen contracts (§4.4, guardrail 2) |
| `ARIADNE_ALLOC` / `ARIADNE_FREE` contracts and `#include "ariadne_alloc.h"` | kept | the ghost liveness model (`-ariadne`, plan §10 fallback 1) is trusted spec |
| C code, including the labels `before_alloc:` / `before_free:` | kept | the overlay rule (7.1): only annotations may differ |
| the 11 lemmas (`mem_cons`, `all_live_cons`, `all_live_nil`, `all_init_cons`, `all_init_nil`, `dll_null`, `dll_inv`, `dll_links`, `dll_first`, `dll_frame`, `live_dll_inv`) and their comments | removed | not frozen: lemmas are proved, so the agent may add them (§5 step 5c); they are the human's proof strategy |
| loop invariants, `loop assigns`, `loop variant` (in `get_first`, `get_last`, the four loops of `b1`) | removed | internal annotations (§4.4) |
| the asserts in `add`, `get_first`, `get_last`, `it_init_on_equal`, `it_next`, `b1` | removed | internal annotations |

`guardrails.frozen(b1.c, b1_frozen.c)` passes: 18 frozen items, the same
hashes (digest `213986017b964d3e`), nothing changed, removed or added.

**Census before any annotation** (`../../harness/b1_frozen.json`, the
same WP flags as M1; `harness/results/b1-frozen-census.md`): 254 goals
(the human's annotations add 67), **206 proved: WP's simplifier (Qed)
158, Alt-Ergo 46, CVC5 2, Z3 0**; 48 open, 0 lemmas.  The open goals,
by function: `b1` 33 (every access and call after its first loop),
`get_first` 6 and `get_last` 6 (the loop body's accesses, `assigns`,
the postcondition), `add` 1 (the postcondition `live_dll`),
`it_init_on_equal` 1 (a precondition of its call to `it_next`), `it_next`
1 (its postcondition).  Step 0 (sanitizers and E-ACSL, without the
mutants, whose anchors are the human's annotations) passes.

## Next

B1c (stretch): `sglib_dllist_sort`.
