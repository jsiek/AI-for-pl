# B1a + B1b: sglib doubly linked list, memory safety (M1 baseline)

Benchmark B1 (plan §6.2), first two stages, as in sglib's
`samples/dllist.c`:

- **B1a**: build a list with `sglib_dllist_add`, and free every element
  while iterating with `sglib_dllist_it_init` / `sglib_dllist_it_next`;
- **B1b**: walk it forward from `sglib_dllist_get_first` and backward
  (via `ptr_to_previous`) from `sglib_dllist_get_last`.

**Status: fully verified**: every goal,
including lemmas, is proved; use-after-free is covered by the ghost
liveness model (`-ariadne`).

```bash
./check.sh     # needs the M0 image and the plugin built; seven PASS lines
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
| `check.sh` | `run.sh` plus three mutants that must be rejected |

The driver replaces the sample's `main`: an input array instead of
`argv`/`sscanf`, no `printf` (body-less libc functions are not
instrumented, see `plugin/README.md`), ariadne allocators instead of
`malloc`/`free`, and a NULL check after allocation, which the sample
lacks (mutant `nullchk` shows the check is needed).

## Goal census (M1)

222 goals, all proved (214 for the 7 functions, 8 lemmas; B1a alone
was 183):

| Closed by | B1a + B1b | B1a alone |
|-----------|-----------|-----------|
| WP's simplifier (Qed) | 126 | 109 |
| Alt-Ergo 2.6.4 | 82 | 65 |
| CVC5 1.2.1 | 9 | 5 |
| Z3 4.13.4 | 1 | 1 |
| Coq 9.0.1 (hand-written scripts) | 4: `mem_cons`, `all_live_cons`, `dll_frame`, `dll_links` | 3 |

Mutants (`check.sh`), each rejected:

| Mutant | Rejected by |
|--------|-------------|
| `vacuity`: `assert \false` at the end of `b1` | the assert (spec consistent) |
| `uaf`: forward walk after the free loop | `get_first`'s precondition at the call (the list's nodes are dead) |
| `uaf_back`: backward walk after the free loop | `get_last`'s precondition at the call |
| `nullchk`: no NULL check after allocation | the `live` assert on `l->i` |
| `nullfirst`: `get_first` returns NULL after its traversal | its postcondition `heads_list` |
| `nulllast`: `get_last` returns NULL after its traversal | its postcondition `last_of_list` |

## The specification (for review: frozen spec, plan §4 and guardrail 3a)

All in `b1.c`; these are the definitions a human must approve.

- `live(p)`: `p` is valid, at offset 0, a heap block, and not dead.
- `mem(p, s)`, `all_live(s)`: membership in, and liveness of, a
  sequence of nodes (`\list<dllist *>`).
- `dll(prev, h, s)` (inductive): following `ptr_to_next` from `h` gives
  exactly `s`; each node is valid, its `ptr_to_previous` is its
  predecessor (`prev` for `h`), and none repeats.  **Shape only**:
  liveness is kept apart in `all_live`, so `alloc`/`free` (which change
  only `__heap`) leave `dll` syntactically unchanged.  An earlier
  version with liveness inside `dll` left 6 goals SMT could not close.
- `live_dll(prev, h, s) = dll(prev, h, s) && all_live(s)`.
- `unchanged{L1,L2}(s)`: the nodes' link fields are equal at `L1` and
  `L2` and still valid at `L2`.
- `iter_ok(it, cur)`: iterator after `it_init`/`it_next` without a
  subcomparator: backward walk done, `nextelem` starts a live list, and
  `cur` (the element just returned) is live and not in that list.

Lemmas: `mem_cons`, `all_live_cons`, `all_live_nil` (list facts),
`dll_null`, `dll_inv` (unfolding), `dll_frame` (induction).  SMT proves
`all_live_nil`, `dll_null`, `dll_inv`; Coq the other three.

Contracts (restricted to what B1a uses; noted as such):

- `sglib_dllist_add(list, elem)`: `*list` is the **head** of a live
  list (`live_dll(\null, *list, s)`), `elem` is live and not in it;
  afterwards `*list` heads a live list.  sglib allows `*list` to be any
  element; the general contract is future work.
- `it_init`, `it_init_on_equal` (with `subcomparator == \null`),
  `it_next` (no subcomparator): establish / preserve `iter_ok`.  The
  subcomparator paths (calls through a function pointer) are not
  verified; their branches are unreachable under these preconditions.

Annotations the agent role of plan §12 would write (not part of the
frozen spec, all proved): loop invariants and `loop assigns` in `b1`;
asserts `old_nodes_live`/`old_lists_live` after allocation and
`others_live`/`other_lists_live` after free (carry liveness across the
`__heap` change); a `frame` assert at the end of `add`, `it_init_on_equal`,
and `it_next` (lets `dll_frame` apply across the writes).

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

## Next

B1c (stretch): `sglib_dllist_sort`.
