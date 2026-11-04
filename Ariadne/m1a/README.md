# M1a: does WP catch use-after-free?

Plan §10 asks whether Frama-C 33 WP, with the Frama-C libc specs of
`malloc`/`free`, catches use-after-free, invalid `free`, and double
`free`.  **It does not.**  A ghost liveness model, with no change to WP,
does.

```bash
./check.sh     # needs the M0 image (../env); three PASS lines expected
```

| File | What |
|------|------|
| `alloc.c` | test cases against the libc `malloc`/`free` specs |
| `ghost.c` | the same cases under the ghost liveness model, plus stack-pointer and extra vacuity cases |
| `run_models.sh` | runs WP (RTE on, Alt-Ergo + Z3 + CVC5, 10 s) per memory model, writes `report_*.json` |
| `summarize.py` | scores each test function against the expectations written in the C file |
| `check.sh` | both experiments; fails if either result changes |

Each test function is `good_*` (every goal must be proved), `bad_*` (the
goal on the line marked `BAD` must fail, everything else must be
proved), or `vacuous_*` (an `assert \false` that must *not* be proved;
if it were, the specs would be inconsistent and the other results would
mean nothing).

## Result 1: WP with the libc specs

WP warns "Allocation, initialization and danglingness not yet
implemented" for `\fresh`, `\freeable`, and `\allocable`, and drops them.
The `Typed` and `Bytes` models give the same results:

| Case | Result | Why |
|------|--------|-----|
| `good_*` (malloc, write, free) | **incomplete** | `\fresh` dropped, so a new block is not known to be `\valid`; the void* → int* cast also loses validity in `Typed` ("Cast with incompatible pointers types") |
| every `free(p)`, even correct ones | **incomplete** | `requires \freeable(p)` "degenerates" to an unprovable goal |
| `bad_use_after_free`, `bad_list_link_after_free` | **UNSOUND** | the read after `free` is *proved* `\valid`: `free` does not end validity, so the `\valid(p)` known before `free` is still assumed afterwards |
| `bad_free_stack`, `bad_free_interior` | caught | only because every `free` precondition fails |
| `vacuous_*` | ok | specs not inconsistent |

`Region` aborts on the libc string axiomatics; `Eva` (experimental)
needs a `main` and would put Eva in the TCB.  Neither was pursued.

So "WP as is" is ruled out: under `Typed`, if `\fresh` were supported,
`bad_use_after_free` would be fully proved.

## Result 2: ghost liveness model (plan §10, fallback 1)

`ghost.c` replaces `malloc`/`free` with typed allocators (`malloc_int`,
`malloc_node`, `free_int`, `free_node`) whose contracts track a ghost
heap version `__heap` and two abstract predicates:

- `heap(b)`: block base `b` was returned by an allocator;
- `dead(v, b)`: block `b` is freed in heap version `v`;
- axiom `dead_heap`: `dead(v, b) ==> heap(b)`;
- allocators: result is `\valid`, at offset 0, a heap block, not dead,
  and distinct from every live heap block; `free` requires a live heap
  block at offset 0 and makes it dead; both frame all other blocks;
- instrumentation (by hand here, by a pass later): before each
  dereference of `p`, `assert live: !dead(__heap, \base_addr(p))`, and
  at each address-taken variable `x`, `admit !heap(\base_addr(&x))`.

All 12 test functions are scored correct (61 / 69 goals proved; the 8
unproved are exactly the 5 `BAD` goals and the 3 vacuity asserts):

| Case | Caught by |
|------|-----------|
| use after free, write after free through alias, freed node via link | `live` assert |
| double free, free of a stack object | `freeable` precondition of `free_*` |
| pointer to a local, before and after a `free` | proved, thanks to `dead_heap` + the stack `admit` |

WP's own RTE `\valid` goal on a freed read is still (wrongly) proved;
the `live` assert is what catches the bug.  The certificate is only
meaningful together with the instrumentation.

## What this adds to the TCB

1. The allocator contracts (4 short contracts per allocated type, or
   one generic set once casts are handled).
2. Axiom `dead_heap`; consistent (`dead` = false is a model), and should
   get a Coq realisation to make that checked.
3. The stack `admit`s: one per address-taken variable, justified by C's
   rule that a live object's storage is never returned by `malloc`.
4. The instrumentation pass: it must put a `live` assert before every
   dereference.  A missed dereference is a missed bug, so the pass must
   be small and reviewed, and its output checked (e.g. count
   dereferences in the normalised code vs asserts emitted).

## Open items for M1

- **Casts.**  `Typed` loses validity across `void*` → `T*`.  The typed
  allocators avoid the cast.  `sglib.h` never calls `malloc`, `calloc`,
  `realloc`, or `free`, so only benchmark drivers allocate; drivers are
  ours, so they can call typed allocators.  The overlay check (plan
  §7.1) must allow exactly this rewrite.  The RB-tree and DL-list code
  contains no pointer casts at all (the only ones are `(unsigned char *)`
  in the hash functions), which settles the cast check plan Q2 left for
  M1.
- **A natural use-after-free benchmark.**  sglib's map-on-elements
  macros run a user command per element, and a comment in
  `SGLIB___BIN_TREE_MAP_ON_ELEMENTS` says the command "can free the
  element".  Whether the macro reads the element after the command is
  exactly what the ghost model should check.
- **Instrumentation pass.**  A Frama-C plugin (OCaml; walks the
  normalised AST, sees every dereference) or a script on `-print`
  output.  Plugin preferred: it sees the same AST WP does.
- **Coq side.**  Goals that go to Coq will mention `P_heap`/`P_dead`;
  the Coq library (G7) needs lemmas for the frame properties.
- **Improving WP instead** (fallback 2) remains possible later, and
  `check.sh` step 1 will notice if a future Frama-C release starts
  handling `\fresh`/`\freeable`/`\allocable`.
