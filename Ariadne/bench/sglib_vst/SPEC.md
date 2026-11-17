# sglib DL list, stage 1: what each function requires and ensures

**Approved by the owner on 2026-11-17 (function-by-function walkthrough); frozen with the client survey.**  (Plan M6.)

Frozen digest: `ee6043a2f971a9f6` (this line excluded; see below)

The digest is computed by `frozen_digest.py` (a SHA-256 prefix over
this file without the digest line, and `spec_dllist.v`); `check.sh`
fails if it changes.

> **Goal (owner, 2026-11-17): memory safety plus leak freedom.**  Every
> postcondition accounts for all memory the function owns at the end,
> and `main` ends owning no heap memory.  Unbounded growth of memory
> that is still held is out of scope; functional correctness is out.
>
> **Minimality rule (owner, 2026-11-17).**
> - A precondition clause holds only what the function body needs: it
>   cites the body lines (`dllist.c:N`) that need it.
> - A postcondition clause holds only what a surveyed client needs to
>   continue safely and leak-free: ownership and shape, not order,
>   positions or values.  It cites the survey patterns
>   (`../sglib_spec/CLIENT_SURVEY.md`), or "leak freedom" with the
>   pattern.
> - **Simplicity exception:** a stronger postcondition or a weaker
>   precondition is allowed when it is simpler than the minimal form;
>   so is a stronger precondition, when it is simpler and no surveyed
>   client needs the weaker one (owner, 2026-11-17, with R8).  Each use
>   is marked **[exception]**, with the minimal alternative and why the
>   chosen form is simpler.  A use that rests on "no surveyed client
>   needs it" is entered in the survey's revisit register
>   (`../sglib_spec/CLIENT_SURVEY.md`).
> - A clause with no citation is removed.
>
> **Leak-freedom check (owner, R10, 2026-11-17).**  No public
> postcondition contains `TT` or an existential over `mpred`, including
> inside the predicates it uses (definitions unfolded);
> `lint/post_lint.py` checks this in `check.sh`.  A client's `main`
> ends with the allocator's state (`mem_mgr gv`) plus its globals.  A
> private helper whose postcondition contains `TT` cannot hide a leak:
> its caller would hold `TT`, which entails no `TT`-free assertion, so
> the caller could not end in a `TT`-free public postcondition.

This is the English public spec of stage 1: `add`, `get_first`,
`get_last`, `it_init`, `it_init_on_equal`, `it_next` and the comparator.
`spec_dllist.v` says the same in VST funspecs.  `REVIEW.md` lists where
the two differ and the questions that are still open.  The instance is
B1's `dllist` (`dllist.c`, with the functions verbatim from sglib):

```c
typedef struct dllist {
  int i;                          /* payload */
  struct dllist *ptr_to_next;     /* "next" link */
  struct dllist *ptr_to_previous; /* "previous" link */
} dllist;
```

## What is proved

**Memory safety:**
- no access through NULL, a dangling (freed) or out-of-bounds pointer;
- no double free, and no free of a pointer that `malloc` did not return;
- no read of an uninitialised variable or field, and no other undefined
  behaviour.

**Leak freedom,** as defined above.

Termination is not required (VST proves partial correctness).  Use is
sequential only (Q7).

Each function's spec says three things:
- what the caller lends or gives (**Requires**);
- what it owns again afterwards (**Owns afterwards**);
- what holds then (**Ensures**).

Memory the caller does not pass is untouched (the frame rule).  There is
no condition on where a variable lives: a list head or an iterator may
be a local, a global or a field of a heap block (Q5).

## Words used below

* A **node** is a `dllist` object.
  - **Owning** a node at a share means holding that share of its three
    fields: a *readable* share to read them, a *writable* share to write
    them as well.
  - No function frees a node, so none needs the node's `malloc` token.
    The client keeps its tokens and frees its nodes itself.
* A **sequence** `s = n0, ..., nk-1` of node addresses, with **contents**
  `vs` (each node's payload and two links).
  - Its **prev links** on `lo..hi` hold when `nj->ptr_to_previous` is
    `nj-1` for each `j` in that range (NULL for `n0`).
  - Its **next links** hold when `nj->ptr_to_next` is `nj+1` (NULL for
    `nk-1`).
  - A **whole list** is a sequence with all its links, and its nodes are
    distinct.  The empty sequence is the empty list (NULL).
* "`p` is at `s`, position `j`" means `p` is node `nj` of `s`, or `s` is
  empty and `p` is NULL.  A caller that passes NULL takes `s` empty and
  keeps its other lists in the frame.
* **The same contents:** every node keeps its payload and both links.

## `void sglib_dllist_add(dllist **list, dllist *elem)`

Inserts `elem` just before `*list`.

**Requires**

| Clause | Needed by |
|---|---|
| `list` points to a pointer variable owned writable, `*list` initialised | `dllist.c:24,31` read it; `:26,37` write it |
| `*list` is at a whole list `s`, position `j` | `:24` tests it; `:31-32` read and write `(*list)->ptr_to_previous` |
| the nodes of `s` owned writable | `:32` writes `*list`'s prev; `:34` writes its predecessor's next |
| `s`'s links are those of a whole list | `:31,33-34`: the old `*list`'s prev is NULL or a node owned writable |
| `elem` owned writable, not in `s`; payload and links may be uninitialised | `:27,30-31` write its links (separation makes it distinct from `s`'s nodes) |

**[exception] the whole list in the precondition.**
- *Minimal:* own only the old `*list`, its predecessor and `elem`, with
  only `*list`'s prev link given.  The client would then rebuild its
  whole list around the three nodes itself.
- *Chosen (owner, R8, 2026-11-17):* the whole list.  It is simpler:
  the re-linking lemma is proved once, in `add`'s proof, rather than in
  every client.  No surveyed client needs the weaker form: every one
  holds a whole list when it calls `add` (A1–A5).  Register entry R8.

**Owns afterwards and Ensures** (form E, owner's decision R9,
2026-11-17)

| Clause | Needed by |
|---|---|
| the pointer variable `*list`, with `*list == elem` | A1–A3, A8: the client adds again through it.  **[exception]** minimal: `*list` is some node of the new list |
| the whole list is `s` with `elem` inserted at position `j` (just before the old `*list`), owned writable, each node keeping its payload | A4 (the client's old nodes are still in one whole list); leak freedom of A1–A4 clients (every node is accounted for); payloads: A4 client 1 and I1 read them.  **[exception]** minimal: a whole list of exactly the old nodes plus `elem`, in some order |

Why the exact form is simpler: it needs no permutation, no pairing of
nodes with payloads and no existential new sequence; `add`'s proof
builds exactly this list anyway; and a client of the minimal form would
recover the positions it needs through permutation lemmas.  The minimal
form is recorded in `REVIEW.md`, section 3.

## `dllist *sglib_dllist_get_first(dllist *list)`

**Requires**

| Clause | Needed by |
|---|---|
| `list` is at a sequence `s`, position `j` | `:44-46` |
| the nodes `n0..nj` owned readable, with their prev links | `:46` reads `ptr_to_previous` from `list` back to NULL |

**Owns afterwards and Ensures**

| Clause | Needed by |
|---|---|
| `n0..nj`, with the same contents | G1, G2, A4 and every client that keeps using the list; leak freedom |
| the result is NULL or a node of `s` | G1, G2: the client walks from the result through nodes it owns; G3 (NULL) |

The result being the head is a position fact.  Minimal is "a node of
`s`".  The exact form ("the head") is not used: it is no simpler
(register entry get-first-head).

## `dllist *sglib_dllist_get_last(dllist *list)`

The mirror image of `get_first`:
- it requires the nodes `nj..nk-1`, owned readable, with their next
  links (`:57-59`);
- it gives the same nodes back with the same contents;
- the result is NULL or a node of `s` (G1, G2, G3).

## The comparator (Q6)

A comparator is a function `int cmp(dllist *a, dllist *b)` passed to
`it_init_on_equal`.
- Each program fixes one **comparator state** per comparator `f`: a
  predicate `Rc gv f`, over the program's globals `gv`, describing the
  memory `f` uses between calls (a counter, a log).  The state's value
  stays hidden inside `Rc gv f` (for example "there is a `k` such that
  the counter holds `k`"); nothing constrains the new state (owner,
  R2, 2026-11-17).
- Every comparator `f` the program passes is proved against the
  contract below for `f`.
- Several comparators may each have their own state.  Comparators that
  share a global have predicates over the same memory; the client
  converts one into the other by entailment between calls.
- sglib's comparator type `int (*)(dllist *, dllist *)` passes no
  context, so a comparator reaches its state through globals (register
  entry cmp-state-globals).  The comparator contract, `it_init_on_equal`
  and `it_next` therefore take the globals (`GLOBALS (gv)`), so that the
  comparator's body can address its state.
- `it_next` calls the comparator as `scp(eq, ce)` in its backward
  walk (`dllist.c:90`) and as `scp(ce, eq)` in its forward walk
  (`:104`), so either argument may be the `equalto` node.
- For this callback the roles swap: `it_next` must establish the
  comparator's precondition, and relies on its postcondition.

**Requires (what the comparator may assume)**

| Clause | Needed by |
|---|---|
| `a` and `b` owned at some readable shares, whatever they are | C1, C3: the comparator reads the payloads.  Any readable share, so it cannot write a node (Q6; C4 out of scope) |
| `a`'s and `b`'s payloads are initialised ints | C1, C3: the comparator computes on them |
| its state `Rc gv f`, and the globals `gv` | C3: the comparator updates a counter in a global |

**[exception] the whole node.**
- *Minimal:* only the payload field.
- *Chosen:* the whole node, which is simpler: `it_next` holds whole
  nodes, so no field splitting is needed.

**Owns afterwards and Ensures (what `it_next` relies on)**

| Clause | Needed by |
|---|---|
| `a` and `b`, with the same contents | `:92,106`: `it_next` follows the links after the call; `it_next`'s own postcondition gives the nodes back unchanged |
| its state `Rc gv f` (the value hidden inside may have changed) | C3 (the client reads the counter afterwards); leak freedom of C3 (the client keeps owning, and finally frees, what the state owns) |
| it returns an initialised `int` | `:90,104` compare it with 0 |

## The iterator

```c
struct sglib_dllist_iterator {
  dllist *currentelem, *prevelem, *nextelem;
  int (*subcomparator)(dllist *, dllist *);
  dllist *equalto;
};
```

**The iterator is borrowing.**
- Between calls it owns no node.
- The caller keeps its list and lends each `it_next` call the nodes
  still to be visited; the call gives them back.
- So the caller may reuse its list after an iteration or part-way
  through one (I3, I6), and may free each node returned (I2).

**Iterator state** for a sequence `s` with **window** `b`, `f`:
- the iterator struct is owned writable;
- `-1 <= b < f <= k`;
- `prevelem` is `nb` (NULL when `b == -1`) and `nextelem` is `nf` (NULL
  when `f == k`);
- `subcomparator` and `equalto` are as given at initialisation;
- `currentelem` is not described: no body reads it and no client needs
  it (register entry currentelem).

The nodes **still to be visited** are `n0..nb` and `nf..nk-1`.  The
nodes inside the window have been returned, or skipped by the
comparator.

**Comparator part:**
- if `subcomparator` is NULL, nothing;
- otherwise:
  - `subcomparator` satisfies the comparator contract;
  - the caller lends the `equalto` node at a readable share, with an int
    payload;
  - the caller passes the globals and lends the comparator's state
    `Rc gv subcomparator` for the call and gets it back after (the iterator never holds it, so two
    live iterators, with the same comparator or different ones, can be
    interleaved);
  - the payloads of the nodes still to be visited are ints.

A node of the list may be lent as `equalto` too, at another share.

### `dllist *sglib_dllist_it_next(struct sglib_dllist_iterator *it)`

**Requires**

| Clause | Needed by |
|---|---|
| `*it` in iterator state for `s` with window `b`, `f` | `:84,86-88,98,100-102` read the fields; `:85,96,99,110,112` write them |
| `n0..nb` owned readable, with their prev links | `:90,92,96` |
| `nf..nk-1` owned readable, with their next links | `:104,106,110` |
| the comparator part | `:90,104` call the comparator |

**Owns afterwards and Ensures**

| Clause | Needed by |
|---|---|
| `*it` in iterator state for `s`, with a window `b'`, `f'`, and the same `subcomparator` and `equalto` | I1, I2, I7, I8, I13: the client calls `it_next` again |
| the lent nodes, with the same contents | I3, I6 (reuse), I9 (the other iterator); leak freedom |
| the comparator part and the comparator's state | I7, I9, C3; leak freedom |
| the window only widens (`-1 <= b' <= b`, `f <= f' <= k`) | I2: the next call is lent only nodes the client has not freed |
| the result is NULL, or a node that was still to be visited and is now inside the window | I1 (the client owns and reads it); I2 (**never returns a node twice**, so the client never frees one twice) |
| NULL means no node is left to visit (`b' == -1`, `f' == k`) (R1, owner 2026-11-17) | leak freedom of I2: at NULL the client has freed every returned node, and none is still to be visited.  With a comparator, no surveyed client needs it; it is stated for both cases as the owner decided R1 |
| without a comparator: exactly the returned node leaves the nodes still to be visited, from either end (**every node returned exactly once**, in no promised order) | leak freedom of I2: no node is skipped, so a client that frees each node returned frees them all (Q4 as amended 2026-11-17) |

With a comparator, skipped nodes are allowed.  The client still owns
them (borrowing), and frees them by a later iteration without a
comparator, as every surveyed comparator client does (I7, C3).

### `dllist *sglib_dllist_it_init_on_equal(struct sglib_dllist_iterator *it, dllist *list, int (*subcomparator)(dllist *, dllist *), dllist *equalto)`

**Requires**

| Clause | Needed by |
|---|---|
| `it` points to an iterator struct owned writable; its contents may be uninitialised | `:70-75` write it (no read before) |
| `list` is at a sequence `s`, position `j` | `:72-75` |
| `n0..nj` owned readable, with their prev links | `:76`: `it_next` walks back from `list` |
| `nj..nk-1` owned readable, with their next links | `:75` reads `list->ptr_to_next`; `:76` `it_next` walks forward |
| `subcomparator` NULL (`equalto` arbitrary), or the comparator part | `:76`: `it_next` calls it |

**Owns afterwards and Ensures**

| Clause | Needed by |
|---|---|
| `*it` in iterator state for `s` with some window `b`, `f`, `subcomparator` and `equalto` as given | I1, I2, I4, I7, I8: the client calls `it_next` |
| the nodes, with the same contents | I3, I6; leak freedom |
| the comparator part and the comparator's state | I7, I9, C3; leak freedom |
| the result is NULL or a node inside the window | I1, I2 (as for `it_next`) |
| NULL means no node is left to visit | leak freedom of I2, I5 |
| without a comparator: the result is the only node inside the window (NULL only for the empty list) | leak freedom of I2 |

The window is not tied to `j`: no client needs to know where the
iteration starts (register entry it-init-start).

### `dllist *sglib_dllist_it_init(struct sglib_dllist_iterator *it, dllist *list)`

As `it_init_on_equal` with `subcomparator` and `equalto` NULL (`:79`).

## VST rendering

`spec_dllist.v`:

| English | Coq |
|---|---|
| owning nodes | `nodes sh s vs lo hi` |
| prev links, next links | `prev_links`, `next_links` (pure facts) |
| a whole list | `whole s vs` |
| iterator state | `it_rep` |
| a step | `iter_step` (`step_any`, plus `step_exact` without a comparator) |
| after initialisation | `init_window` |
| the comparator contract for `f` | `cmp_spec f`, with the states `Rc : globals -> val -> mpred` a parameter of the whole spec |
| the comparator part | `cmp_env`, `cmp_state`, `cmp_payloads` |

"Untouched" is the frame rule.  Leak freedom per function is the absence
of `TT` (and of existentials over `mpred`) in postconditions:
`affine_probe/` shows that VST 2.17 lets a proof drop memory only
through `TT`, and `lint/post_lint.py` enforces the absence (`REVIEW.md`,
section 4).
