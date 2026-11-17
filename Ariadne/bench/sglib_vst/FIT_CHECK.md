# Fit check: the stage-1 spec against the approved client survey

This file lists the funspec clauses of `spec_dllist.v` that a client
relies on, for each of the 23 patterns in
`../sglib_spec/CLIENT_SURVEY.md`: the 14 covered and the 9 stage 1.
- Memory safety plus leak freedom (owner, 2026-11-17).
- `add` is form E (owner, R9, 2026-11-17).
- This is a reading of the spec, not a proof: the clients are proved in
  the next step of M6.

**Result: all 23 patterns are supported, with leak freedom.**
- Every client keeps the `malloc` tokens of its nodes; no library
  function takes them.
- Every client ends by freeing every node with an iteration without a
  comparator, which relies on `step_exact` and `step_any`'s "NULL
  means none left".

## Covered (14)

| Pattern | Clauses relied on |
|---|---|
| A1 add to empty | `add`: `s = []`, `j = 0`; pre `*list == NULL`.  Post: one whole list holding `e` alone (`ins 0 e []`) |
| A2 add at head | `add`, `j = 0`.  Post: the old nodes plus `e`, and `*list == e`, for the next `add` |
| A3 add before a non-head node | `add`, `0 < j`: pre `*list == Znth j s`, `whole s vs`, the nodes writable |
| A5 elem's links uninitialised | `add` pre `data_at sh t_dl (ev, enp) e`, with `ev` and `enp` arbitrary |
| G1 from the head, walk | `get_first` / `get_last`: the result is NULL or in `s`; the nodes come back with the same `vs`, and the client's pure link facts let it walk |
| G3 on NULL | `get_first` / `get_last`, `s = []`: the result is NULL |
| I1 iterate, read, no free | `it_init`: `init_window`, `it_rep`, the nodes back.  `it_next`: the result is in a lent segment, so it is owned and readable |
| I2 iterate and free | `step_any`: the result moved into the window, which only widens (never returned twice; the next call is lent only unfreed nodes); NULL means none left.  `step_exact` without a comparator: no node skipped.  So freeing each result frees every node: leak-free |
| I3 iterate, then reuse | The nodes come back with the same `vs`; the client still holds `whole s vs` |
| I4 start mid-list | `it_init` at any `j`; `init_window` is not tied to `j` |
| I5 empty list | `init_window` with `s = []`: the result is NULL |
| I7 with a comparator | `cmp_env` (`func_ptr' (cmp_spec scp) scp`, `equalto` at a readable share with an int payload), `cmp_state gv scp = Rc gv scp` lent to each `it_init_on_equal` / `it_next` call and given back, and `cmp_payloads`; the comparator is proved against `cmp_spec f`.  Skipped nodes stay the client's; it frees them by a later plain iteration |
| I8 NULL comparator | `cmp_env nullval .. = emp`; `iter_step nullval` includes `step_exact` |
| C1 pure comparator | `cmp_spec f` with `Rc gv f := emp`; the int payloads in its precondition let it compute |

## Stage 1 (9)

| Pattern | Clauses relied on |
|---|---|
| A4 old nodes after add (client 1) | `add` post: exactly the old nodes plus `e`, the payloads kept (`ins j e s`, so `h` is still a node of the list).  Then `get_first(h)`, the walk, and a freeing iteration from `h` |
| A7 several lists (client 2) | Each list is its own `nodes` / `whole`; every funspec frames the others |
| A8 head a global or a heap field (clients 3, 4) | `add` pre `data_at shl (tptr t_dl) _ lp`, any writable `shl`, any `lp` (a global, or `field_at` at a `field_address`); no `!heap` condition (Q5) |
| G2 get_first/get_last from the middle (client 5) | `get_first` / `get_last` at any `j`: the prefix (or suffix) is lent, and the result is in `s` |
| I6 stop part-way, reuse (client 6) | Borrowing as in I3; the iterator struct is reused through `it_rep .. |-- data_at_ sh t_it it` |
| I9 two iterators (client 7) | Two `it_rep`s; between calls the client owns every node and lends each call its iterator's ranges at a readable share (R5: both iterators may hold parts of the share at once).  The inner iteration's `equalto` may be the outer iterator's current node, lent at a split share (R6).  With comparators: the state is lent per call (`cmp_state`), never held by an iterator, so two live iterators with different comparators (`Rc gv f1`, `Rc gv f2`) or with the same one (`Rc gv f`, lent to whichever call comes next) interleave freely |
| I13 it_next after NULL (client 8) | After NULL, the window is `(-1, k)`; the next call borrows nothing and returns NULL (`step_exact`) or something in an empty set, that is NULL.  Memory safe; the client freed every node during the iteration (I2) |
| I14 iterator in heap memory (client 4) | `it_init` takes `data_at_ sh t_it it` at any writable `sh` and any address (Q5) |
| C3 comparator with its own state (client 9) | `cmp_spec f` with `Rc gv f := EX k: int, data_at Ews tint (Vint k) (gv _counter)` (the counter's value hidden; the state is reached through the globals `gv`, which the calls pass, since sglib's comparator type passes no context: register entry cmp-state-globals).  The client lends `Rc gv f` per call and gets it back, so it reads the counter afterwards.  Two comparators with their own states: `Rc gv f` is `if f = gv _cmp1 then (counter 1) else (counter 2)`.  Comparators sharing one global: their predicates describe the same counter, and the client converts `Rc gv f1` into `Rc gv f2` by entailment between calls |

## Not part of this check

- The stage-2 patterns: A6, A9, G4, G5, I11, C2, D1–D4.
- I10: its order part is checked at run time; its coverage part is now
  `step_exact`.
- The out-of-scope patterns: I12, C4, X1, X2.

For stage 2: `it_next` borrows only the links it follows (Q2), so
deleting the current node (I11) needs no change of the iterator state.
