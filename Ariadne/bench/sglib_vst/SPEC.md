# sglib DL list, stage 1: what each function requires and ensures

**DRAFT for the owner's review (plan M6).**  This is the English public
spec of stage 1: `add`, `get_first`, `get_last`, `it_init`,
`it_init_on_equal`, `it_next` and the comparator.  `spec_dllist.v` says
the same in VST funspecs; `REVIEW.md` lists where the two differ and
the questions still open.  It follows the approved client survey
(`../sglib_spec/CLIENT_SURVEY.md`) and the owner's decisions Q1–Q8 of
2026-11-11.

The instance is B1's `dllist` (`dllist.c`):

```c
typedef struct dllist {
  int i;                          /* payload */
  struct dllist *ptr_to_next;     /* "next" link */
  struct dllist *ptr_to_previous; /* "previous" link */
} dllist;
```

## What is proved

**Memory safety** of every function under its precondition: no access
through NULL, a dangling (freed) or out-of-bounds pointer, no double
free and no free of a pointer that `malloc` did not return, no read of
an uninitialised variable or field, and no undefined behaviour.
Termination and functional correctness (the values computed) are not
required.  Sequential use only (Q7).

Each function's spec says what the caller must own before the call
(**Requires**), what it owns again afterwards (**Owns afterwards**), and
what holds then (**Ensures**).  Whatever the caller owns and does not
pass to the function is untouched by it.  There is no condition on
where the caller's variables live: a list head or an iterator may be a
local, a global or a field of a heap block (Q5).

## Words used below

* A **node** is a `dllist` block returned by `malloc` and not yet freed.
  *Owning* a node means having the right to read, write and free it.
* A **whole list** is a finite sequence `s = n0, ..., nk-1` (k >= 0) of
  distinct nodes, all owned, with consistent links:
  `n0->ptr_to_previous == NULL`, `nj->ptr_to_previous == nj-1` for
  j > 0, `nj->ptr_to_next == nj+1` for j < k-1, and
  `nk-1->ptr_to_next == NULL`.  `n0` is its **head**.  The empty
  sequence is the empty list, written as NULL.  The payloads may be
  uninitialised.
* A **segment** `s[lo..hi)` of a whole list `s` is the nodes `nlo ..
  nhi-1`, owned, with the links they have in `s` (the end nodes'
  outer links point at `nlo-1` and `nhi`, which the segment does not
  own).
* "`p` is at `s`, position `j`" means `p` is node `nj` of `s`, or `s`
  is empty and `p` is NULL.
* "the same contents": every node keeps its payload and its two links.

## `void sglib_dllist_add(dllist **list, dllist *elem)`

Inserts `elem` just before `*list`.

* **Requires**
  * `list` points to a writable pointer variable;
  * `*list` is at a whole list `s`, position `j` (any node, not
    necessarily the head; or NULL with `s` empty);
  * `elem` is a node the caller owns on its own, not in `s` (Q8); its
    payload and links may be uninitialised.
* **Owns afterwards**: the pointer variable `*list` and one whole list.
* **Ensures**
  * `*list == elem`;
  * the whole list is `s` with `elem` inserted at position `j`, just
    before the old `*list` (at the end when `s` was empty): the caller's
    old nodes are all still in it, in the same order, with the same
    payloads, and `elem` keeps its payload (owner, 2026-11-10).

## `dllist *sglib_dllist_get_first(dllist *list)`

* **Requires**: `list` is at a whole list `s` (any node, or NULL with
  `s` empty).
* **Owns afterwards**: `s`, with the same contents.
* **Ensures**: the result is the head of `s` (NULL if `s` is empty).

## `dllist *sglib_dllist_get_last(dllist *list)`

* **Requires**: `list` is at a whole list `s`.
* **Owns afterwards**: `s`, with the same contents.
* **Ensures**: the result is the last node of `s` (NULL if `s` is
  empty).

## The comparator (Q6)

A comparator is a function
`int cmp(dllist *a, dllist *b)` passed to `it_init_on_equal`.  Each
program chooses one **comparator state**: a description of memory the
comparators own between calls (a counter, a log), as a predicate on
some state value.  Every comparator the program passes is proved
against this contract:

* **Requires**: read access to the whole of node `a` and the whole of
  node `b` (they may be the iterator's nodes or the `equalto` node;
  their fields may be uninitialised), and the comparator state.
* **Owns afterwards**: read access to `a` and `b`, with the same
  contents, and the comparator state, possibly with a different value.
* **Ensures**: it returns an `int`.

Read access only, so a comparator writes no node, payload included (C4
is out of scope).  It may write its own state.  There is no fixed set
of comparators and no promise about what a comparator computes.

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
successor to the end (through `nextelem`), returning each node once, or
only those the comparator finds equal to `equalto`.  The spec does not
promise that order, nor that every node is returned, nor that NULL
means every node has been returned: those are checked at run time only
(Q4, pattern I10).

**The iterator is borrowing.**  Between calls it owns no node: the
caller keeps the whole list (or what is left of it) and lends the nodes
still to be visited to each `it_next` call, which gives them back.  So
the caller may reuse its list after an iteration, or part-way through
one, and may free each node returned once the iterator has moved past
it.

**Iterator state** for a whole list `s = n0, ..., nk-1` with **window**
`b`, `f`: the iterator struct `*it` is owned by the caller (writable),
all five fields are initialised, `-1 <= b < f <= k`, `prevelem` is
`nb` (NULL when `b == -1`) and `nextelem` is `nf` (NULL when
`f == k`).  The nodes **still to be visited** are the segments
`s[0..b+1)` and `s[f..k)`; the nodes strictly inside the window have
been returned (or skipped).  The iterator state does not own any node.

**Comparator part** of the iterator state: `subcomparator` and
`equalto`.  If `subcomparator` is NULL, nothing more.  Otherwise each
call that may compare needs `subcomparator` to be a comparator proved
against the contract above, read access to the `equalto` node (owned
by the caller on its own: not a node of the list), and the comparator
state; it returns them, the state possibly changed.

**A step** from window `b`, `f` to window `b'`, `f'` returning `r`:
the window only widens (`-1 <= b' <= b`, `f <= f' <= k`,
`b' < f'`), so the nodes still to be visited only shrink, and `r` is NULL or a node that was still to be visited and
is now inside the new window (`r == nc` with `b' < c < f'` and `c <= b`
or `f <= c`).  So a node is returned at most once, and a node returned
is never touched by the iterator again.

### `dllist *sglib_dllist_it_init_on_equal(struct sglib_dllist_iterator *it, dllist *list, int (*subcomparator)(dllist *, dllist *), dllist *equalto)`

* **Requires**
  * `it` points to a writable iterator struct (its contents may be
    uninitialised);
  * `list` is at a whole list `s`, position `j`;
  * `subcomparator` is NULL (and `equalto` is arbitrary), or the
    comparator part above holds for `subcomparator` and `equalto`.
* **Owns afterwards**: `*it`, the whole list `s` with the same contents,
  and the comparator part.
* **Ensures**: `*it` is in iterator state for `s` with some window
  `b`, `f` reached by one step from the window `j`, `j+1` (from `-1`,
  `0` when `s` is empty); the result `r` is that step's result;
  `it->currentelem == r`; `it->subcomparator == subcomparator` and
  `it->equalto == equalto`.

### `dllist *sglib_dllist_it_init(struct sglib_dllist_iterator *it, dllist *list)`

* **Requires**: `it` points to a writable iterator struct; `list` is at
  a whole list `s`, position `j`.
* **Owns afterwards**: `*it` and `s`, with the same contents.
* **Ensures**: as `it_init_on_equal`, with `subcomparator` and `equalto`
  NULL.

### `dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it)`

* **Requires**
  * `*it` is in iterator state for some whole list `s` with window `b`,
    `f` (its `currentelem` is arbitrary);
  * the caller lends the nodes still to be visited, `s[0..b+1)` and
    `s[f..k)`;
  * the comparator part, if `it->subcomparator` is not NULL.
* **Owns afterwards**: `*it`, the same two segments with the same
  contents, and the comparator part.
* **Ensures**: `*it` is in iterator state for `s` with a window `b'`,
  `f'` reached by one step from `b`, `f`, returning the result `r`;
  `it->currentelem == r`; `subcomparator` and `equalto` are unchanged.

So `it_next` may be called again after it returned NULL (I13), and a
client may run two iterators over one list (I9), lending the segments
to each call.

## VST rendering

`spec_dllist.v`: "owns a node" is `data_at Ews t_dl _ n *
malloc_token Ews t_dl n`; a whole list is `whole_list s ps` (node
addresses `s`, payloads `ps`); a segment is `cells s ps lo hi`; the
iterator state is `it_rep`; a step is `iter_step`; the comparator
contract is `cmp_spec Rc`, with the comparator state `Rc : CS -> mpred`
a parameter of the whole spec; the comparator part is `cmp_env`.
"Untouched" is the frame rule.  Partial correctness: termination is not
proved.
