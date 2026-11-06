# B1 bug-fix log (plan Q11, "Bug fixes")

One entry per change to B1's C code.  The certification diff of `b1.c`
against sglib's expansion must show exactly these changes.

## 1. `DLLIST_COMPARATOR` overflows (2026-11-05, owner-approved)

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
