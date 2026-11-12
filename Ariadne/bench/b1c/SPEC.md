# B1c: what each function requires and ensures (memory safety)

The informal spec of plan Q10's B1c round: B1a's functions and
spec, with a driver that reuses the list after iterating.  It says in English what
the public ACSL contracts of `b1c_frozen.c` say (the frozen spec on
branch `ariadne-templates`, after the owner's decisions of 2026-11-05).
The C code is `b1c.c`: sglib's doubly linked list instantiated at

```c
typedef struct dllist {
  int i;                          /* payload */
  struct dllist *ptr_to_next;     /* "next" link */
  struct dllist *ptr_to_previous; /* "previous" link */
} dllist;
```

plus sglib's iterator struct, four sglib functions, and a driver `b1`.

## What is proved

**Memory safety** of every function under its precondition: no access
through NULL, a dangling (freed) or out-of-bounds pointer, no double
free and no free of a pointer that `malloc` did not return, no read of
an uninitialised variable or field, and no signed overflow or other
undefined behaviour.  Termination and functional correctness (the values
computed) are not required.

## Words used below

* A **node** is a `dllist` block returned by the allocator and not yet
  freed (a *live* node).
* A **whole list** is a finite sequence of distinct nodes `n0, ..., nk-1`
  (k >= 1) whose links are initialised and consistent:
  `n0->ptr_to_previous == NULL`, `nj->ptr_to_previous == nj-1` for
  j > 0, `nj->ptr_to_next == nj+1` for j < k-1, and
  `nk-1->ptr_to_next == NULL`.  `n0` is its **head**.  Only the two link
  fields need be initialised; the payload `i` is not part of the list
  property.
* "`p` is in a whole list" means `p` is one of the nodes of some whole
  list.

## `void sglib_dllist_add(dllist **list, dllist *elem)`

Inserts `elem` just before `*list`.

* **Requires**
  * `list` points to a writable pointer variable that is not itself in
    a heap block (a local or global), and `*list` is initialised;
  * `elem` is a node (live, allocated, pointer to the start of its
    block);
  * `*list` is NULL, or `*list` is any node of a whole list (not
    necessarily its head) that does not contain `elem`.
* **May write** only: `*list`, `elem`'s two links, the old `*list`'s
  `ptr_to_previous`, and, when the old `*list` is not NULL, the
  `ptr_to_next` of the old `*list`'s predecessor.
* **Ensures**
  * `*list` is initialised and equals `elem`, and `elem` is in a whole
    list;
  * if the old `*list` was NULL or a head (its `ptr_to_previous` was
    NULL), then `elem->ptr_to_previous == NULL` (`elem` is the new head).
  * if the old `*list` was node `k` of a whole list `s` (with head `h`),
    the list now is `s` with `elem` inserted at position `k` (before the
    old `*list`), headed by `elem` if `k == 0` and by `h` otherwise
    (owner, 2026-11-10).

## The iterator

```c
struct sglib_dllist_iterator {
  dllist *currentelem, *prevelem, *nextelem;
  int (*subcomparator)(dllist *, dllist *);
  dllist *equalto;
};
```

sglib's iterator starts at a node `p` of a whole list, walks backward
from `p` to the head (through `prevelem`), then forward from `p`'s
successor to the end (through `nextelem`), returning each node once.

**Iterator state** for a whole list `s` = `n0, ..., nk-1` (an iterator
*at* `s` with positions `b`, `f`):

* the nodes of `s` keep their links (they may have been freed by the
  client since, but their link fields are not changed);
* `-1 <= b < f <= k`; `prevelem` is `nb` (NULL when `b == -1`: the
  backward walk is done) and `nextelem` is `nf` (NULL when `f == k`);
* the nodes still to be returned, `n0 .. nb` and `nf .. nk-1`, are live
  (not freed); nodes strictly between `b` and `f` have been returned and
  may have been freed.

**Iterator ok after returning `cur`**: the iterator's `subcomparator`,
`prevelem` and `nextelem` fields are initialised, the iterator is at
some whole list `s` with positions `b`, `f`, and

* if `cur` is NULL, the walk is over: `b == -1` and `f == k`;
* otherwise `cur` is a live node `nc` of `s` with `b < c < f`.

In B1c the set of comparators a client may pass is empty: every
iterator function requires `subcomparator == NULL` (the comparator code
paths are unreachable).

### `dllist *sglib_dllist_it_init_on_equal(struct sglib_dllist_iterator *it, dllist *list, int (*subcomparator)(dllist *, dllist *), dllist *equalto)`

* **Requires**: `it` points to a writable iterator that is not in a heap
  block; `subcomparator == NULL`; `list` is NULL or a node in a whole
  list (any node, not necessarily the head).  `equalto` is arbitrary.
* **May write** only `*it`.
* **Ensures**: the iterator is ok after returning the result (as above),
  and `it->subcomparator == subcomparator`.

### `dllist *sglib_dllist_it_init(struct sglib_dllist_iterator *it, dllist *list)`

* **Requires**: `it` points to a writable iterator not in a heap block;
  `list` is NULL or a node in a whole list.
* **May write** only `*it`.
* **Ensures**: the iterator is ok after returning the result, and
  `it->subcomparator == NULL`.

### `dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it)`

* **Requires**: `it` points to a writable iterator not in a heap block;
  its `subcomparator`, `prevelem` and `nextelem` fields are initialised;
  it is at some whole list `s` with some positions `b`, `f` (iterator
  state above); `it->subcomparator == NULL`.
* **May write** only `*it`.
* **Ensures**: the iterator is ok after returning the result, and
  `it->subcomparator` is unchanged.

So a client may free each node the iterator returns before asking for
the next one.

**The list stays usable, and an iteration covers it.**  The iterator
functions only read the list's nodes and write `*it`, so after an
iteration that freed nothing (or before it ends) the client still has
its whole list, with the same nodes and links, and may pass any of its
nodes to `add` or start another iteration.  An iteration started at any
node `p` of a whole list `s` walks that same list `s`: each node it
returns is a node of `s`, and it returns every node of `s` exactly once
(`p` and its predecessors back to the head, then `p`'s successors to
the end).  A client may interleave `add` with an iteration, or start a
second iteration before the first ends.

## `unsigned b1(const int *input, int n)` (the driver)

1.  Builds a list from `input[0 .. n-1]` with `sglib_dllist_add` (a node
    from `malloc` per element, stopping early if `malloc` returns NULL),
    counting the nodes in `m`.
2.  Walks it once with `sglib_dllist_it_init` / `sglib_dllist_it_next`
    from its head, freeing nothing, adding each payload to an `unsigned`
    sum and recording the node returned at position `m / 2`.
3.  If the walk returned a node, allocates one more node (skipped if
    `malloc` returns NULL), sets its payload to 0, and adds it with
    `*list` set to the recorded middle node, so it is inserted before
    that node.
4.  Iterates again with `sglib_dllist_it_init`, starting from the new
    node (or from the head if none was added), which walks backward to
    the head and then forward to the end, freeing every node returned.
5.  Returns the sum.

* **Requires**: `0 <= n`; `input[0 .. n-1]` is readable and initialised;
  `input` is not in a heap block.
* **Ensures**: nothing beyond memory safety (it returns an `unsigned`).
  (Every node it allocates is freed by the last iteration; stating that
  is optional.)

The allocator may return NULL; `free` must get a pointer `malloc`
returned and has not been freed.

## Frama-C and VST renderings

* **Frama-C/WP** (`b1c_frozen.c`, given): the ACSL contracts of the
  template `../b1a/spec/sglib_dl_list_spec.h` (`SGLIB_DL_LIST_SPEC`,
  `SGLIB_DL_LIST_CONTRACT_ADD`, `_IT_INIT_ON_EQUAL`, `_IT_INIT`,
  `_IT_NEXT`) and the driver's contract.  "Live" is the ghost liveness
  model of the `-ariadne` plugin (`ariadne_alloc_dllist` /
  `ariadne_free_dllist` stand for `malloc` / `free`), and "not in a heap
  block" is `!heap(\base_addr(p))`.  The driver also requires
  `payload_init` (every live node's `i` is initialised), which the ghost
  model needs because it describes all heap nodes at once; under VST's
  ownership this is not needed.
* **VST** (to be written): funspecs in separation logic.  "Live node" is
  ownership of the cell (`data_at` + `malloc_token`); "may write only"
  is the frame of the funspec; a whole list is a representation
  predicate.  `main` calls `b1` on a 4-element global array.  The
  iterator's funspecs must let the client keep using its list
  (see "The list stays usable" above).
