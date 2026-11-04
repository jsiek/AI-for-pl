# B1a: sglib doubly linked list, memory safety (M1 baseline)

Benchmark B1 (plan §6.2), first stage: build a list with
`sglib_dllist_add`, walk it forward, and free every element while
iterating with `sglib_dllist_it_init` / `sglib_dllist_it_next`, as in
sglib's `samples/dllist.c`.  **Status: fully verified**: every goal,
including lemmas, is proved; use-after-free is covered by the ghost
liveness model (`-ariadne`).

```bash
./check.sh     # needs the M0 image and the plugin built; four PASS lines
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

183 goals, all proved:

| Closed by | Goals |
|-----------|-------|
| WP's simplifier (Qed) | 109 |
| Alt-Ergo 2.6.4 | 65 |
| CVC5 1.2.1 | 5 |
| Z3 4.13.4 | 1 |
| Coq 9.0.1 (hand-written scripts) | 3: `mem_cons`, `all_live_cons`, `dll_frame` |

Mutants (`check.sh`), each rejected:

| Mutant | Rejected by |
|--------|-------------|
| `vacuity`: `assert \false` at the end of `b1` | the assert (spec consistent) |
| `uaf`: forward walk after the free loop | the walk's loop invariant (the list's nodes are dead) |
| `nullchk`: no NULL check after allocation | the `live` assert on `l->i` |

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
  driver), and a certificate bundle (`coqc` + `coqchk` of the 3 Coq
  goals, axiom list).

## Next

B1b: `get_first` / `get_last` and the reverse walk.  B1c (stretch):
`sglib_dllist_sort`.
