# Ariadne Frama-C plugin (`-ariadne`)

Adds the ghost liveness instrumentation of plan §10 (fallback 1;
`../m1a/README.md`) so WP can catch use-after-free, double free, and
invalid free.

```bash
../env/run.sh env DUNE_CACHE=disabled dune build      # from this directory
../env/run.sh frama-c -load-module _build/default/ariadne.cmxs \
  -cpp-extra-args=-Ishare -ariadne prog.c -then -wp -wp-rte -wp-model Typed
tests/check.sh                                        # four PASS lines
```

It builds against the Frama-C in the M0 image, in the workspace; the
image does not change.

## What it does

With `-ariadne`, before WP runs:

1. **Refuses raw allocation.**  Any use of `malloc`, `calloc`,
   `realloc`, `free`, or `aligned_alloc` is an error: direct calls, the
   `T *p = malloc(...)` initializer form, and taking the function's
   address (calls through a function pointer).  Programs use the typed
   allocators of `share/ariadne_alloc.h` instead.
2. **`live` asserts.**  For every memory access that RTE would check
   (`RteGen.Visit.iter_stmt` with only memory-access alarms, trivial
   ones removed), adds `assert live: !dead(__heap, \base_addr(&lv));`
   on the same statement.  Reusing RTE's enumeration means the plugin
   misses an access only if RTE does, and RTE is already trusted.
3. **`stack` admits.**  For every variable a pointer may reach, adds
   `admit stack: !heap(\base_addr(&x));`: locals at the start of their
   own block, formals and globals at the start of each function body.
   "May reach" is `vaddrof`, or any struct, union, or array variable,
   because CIL does not set `vaddrof` when only `&s.f` is taken.  An
   extra admit is harmless: `!heap(&x)` holds for every variable.

All annotations use the `ariadne` emitter (WP goal names contain
`ariadne_live`), so guardrails can tell plugin-made admits from any
others.  It prints `N live asserts, M stack admits`.

## The ghost model (`share/ariadne_alloc.h`)

Trusted; part of the frozen spec.  It declares the ghost heap version
`__heap`, predicates `heap(b)` and `dead(v, b)`, the axiom
`dead(v, b) ==> heap(b)`, and two contract macros.  Declare one
allocator pair per allocated type:

```c
/*@ ARIADNE_ALLOC */ struct node *ariadne_alloc_node(void);
/*@ ARIADNE_FREE */  void ariadne_free_node(struct node *p);
```

The contracts mention only `\result`, `p`, and `__heap`, so one copy
of each serves every type (Frama-C preprocesses annotations, so the
macros expand).

Functions that take pointers and do not allocate need, in their
contracts, liveness of what they read (`requires !dead(__heap,
\base_addr(p))`) and an `assigns` clause without `__heap`; see
`write_through` in `tests/uaf.c`.

## Tests (`tests/check.sh`)

- `tests/raw_malloc.c`: four uses of `malloc`/`free` (direct calls, a
  global and a local function pointer) all refused.
- `tests/uaf.c`: 18 functions, no hand-written instrumentation.  All
  scored correct (89 / 98 goals; the 9 unproved are the 7 `BAD` goals
  and 2 vacuity asserts):

| Case | Caught by |
|------|-----------|
| read after free, read through alias, freed node via link | `live` assert |
| double free, free of a stack object, free of an interior pointer | `freeable` precondition |
| freed pointer passed to a function | callee's liveness precondition |
| pointer to a local, nested-block local, local array, struct field, global, formal | proved (stack admits) |
| vacuity after alloc; after free with stack admits | not proved (specs consistent) |

WP's own RTE `\valid` goal on a freed read is still (wrongly) proved;
the `live` assert is what catches the bug, so a certificate is only
meaningful for code processed by `-ariadne`.

## Known limits (open)

- **Functions without bodies that access memory** (e.g. `memcpy`,
  `strlen`) are not instrumented; only their contracts are checked, and
  the libc contracts require `\valid`, not liveness.  sglib calls none.
  A guardrail should refuse calls to body-less functions with pointer
  parameters unless their contract mentions `dead`.
- **String literals**: a dereference of a literal gets a `live` assert
  with no matching admit, so it is unprovable (incomplete, not unsound).
- **Trivial accesses** are skipped, following RTE: they are direct
  variable accesses, which never reach the heap.
- **Allocator contracts per type** are written by hand with the macros;
  generating them from a type list would remove even that.
