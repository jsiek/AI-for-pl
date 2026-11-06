# B1 change log (plan Q11)

One entry per change to B1's C code, each with a category: *bug fix*
or *verification refactor* (a behaviour-preserving change made only so
that a tool can verify the code).  The certification diff of `b1.c`
against sglib's expansion must show exactly these changes.

| # | Category | Change | Approved |
|---|----------|--------|----------|
| 1 | bug fix | `DLLIST_COMPARATOR` cannot overflow | owner, 2026-11-05 |
| 2 | verification refactor | `it_next`'s indirect calls in statements of their own | owner, 2026-11-05 |

## 1. Bug fix: `DLLIST_COMPARATOR` overflows (2026-11-05, owner-approved)

**The bug.**  sglib's sample `samples/dllist.c` (vendored unmodified as
`../sglib/dllist.c`) defines

```c
#define DLLIST_COMPARATOR(e1, e2) (e1->i - e2->i)
```

The subtraction overflows `int` when the two values are far apart (for
example `3 - INT_MIN`), which is undefined behaviour.  In practice the
result wraps, gets the wrong sign, and `sglib_dllist_sort` misorders the
list.

**The failing test** (`bugfix/cmp_overflow.sh`, in the M0 image): the
upstream sample built with `gcc -fsanitize=undefined` and run as
`dllist -5 2147483647 -2147483648 3` reports

```
runtime error: signed integer overflow: 3 - -2147483648 cannot be represented in type 'int'
```

and prints `3 2147483647 -2147483648 -5`, unsorted.  With the fix the
same build prints `-2147483648 -5 3 2147483647` with no report.  The
script checks both outcomes.

**The change**, in B1's code only (`gen_in.c`, hence `b1_gen.c` by
`./gen.sh`, and the generated parts of `b1.c` and `b1_frozen.c`; the
vendored `../sglib/dllist.c` stays as upstream wrote it):

```c
#define DLLIST_COMPARATOR(e1, e2) ((e1->i > e2->i) - (e1->i < e2->i))
```

**Why it is correct.**  The new expression is -1, 0 or 1 with the sign
of the mathematical difference `e1->i - e2->i`, and it cannot overflow:
both comparisons are 0 or 1.  sglib uses a comparator's result only
through its sign: every one of the comparator calls in `sglib.h` is
compared with 0 (`< 0`, `<= 0`, `== 0`, `!= 0`, `>= 0`, `> 0`), either
directly or through a variable (`_cc_`, `_c_`, `cmp`) that is only
compared with 0.  The doubly linked list uses `!= 0` (the
`*_if_not_member`, `delete_if_member` and `find_member` searches) and
`< 0` (the merge in `sort`).  So every sglib function gives the same
result with the new comparator whenever the old one did not overflow,
and the right result when it did.

**Proof.**  WP with `-wp-rte` (Alt-Ergo, Z3, CVC5, 10 s) proves every
comparator overflow goal of `find_member` (4), `sort` (4),
`add_if_not_member` (4) and `delete_if_member` (4), all by WP's
simplifier (Qed); with the old comparator the `find_member` and `sort`
ones stayed open (`README.md`, "The comparator's overflow").  Those
functions are not in B1's verified selection; the run is a check of the
fix.  `sort`'s two other overflow goals (line 445, its run length
`_n_ + _n_`) are not the comparator's and stay open.

**Public behaviour.**  Clients see a comparator that orders the same
values as before (when the old one was defined) and is defined on all
values.  No contract mentions it.

## 2. Verification refactor: `it_next`'s subcomparator calls (2026-11-05, owner-approved)

**Why.**  WP 33 proves an indirect call through a function pointer only
when a `calls` annotation names its possible targets, and `calls`
attaches only to a statement.  sglib's `it_next` makes its two calls
inside `while` conditions, where no annotation can reach them
(`../sglib_spec/calls_probe`: "Missing 'calls' for default behavior").

**The change**, in `SGLIB_DEFINE_DL_LIST_FUNCTIONS`'s `it_next` only,
two loops (`refactor/it_next_calls.py`, applied by `gen.sh` to a copy of
sglib.h; the vendored `../sglib/sglib.h` stays as upstream wrote it):

```c
while (ce!=NULL && scp(eq, ce)!=0) ce = ce->previous;
  -> while (ce!=NULL) { if (scp(eq, ce)==0) break; ce = ce->previous; }
while (ce!=NULL && scp(ce, eq)!=0) ce = ce->next;
  -> while (ce!=NULL) { if (scp(ce, eq)==0) break; ce = ce->next; }
```

**Why behaviour is unchanged.**  Both forms do, in order: test `ce`
against NULL and stop if it is; call the comparator (only then, as `&&`
short-circuits); stop if it returned 0; otherwise step and repeat.  The
calls, their arguments and their order, and the final `ce`, are the
same; no other variable is touched.  The call is now `if (scp(..) ==
0)`, so WP's `calls` attaches to it (checked in `calls_probe`).

**Tests** (`refactor/check.sh`, in the M0 image): the refactored sglib.h
differs from the vendored one in exactly these two lines; sglib's
self-test (vendored, unmodified), built under ASan + UBSan against each
header, gives the same output (passes, no report) for seeds 1, 7 and
12345.  Its doubly linked list test iterates with `it_init_on_equal` and
`myListCmp`, so both loops run.  B1's code (`b1_gen.c`, and the code of
`b1.c` and `b1_frozen.c`, equal to it token for token) has the change.
