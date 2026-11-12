# Client survey: sglib's doubly linked list (plan M6)

**Approved by the owner on 2026-11-11.**
- The open questions were decided the same day (below).
- One change came with the approval: I13 claims only memory safety.
- The survey is frozen with the M6 spec (plan M6, precondition 3): a
  later spec change must keep every surveyed client provable.
- It contains no funspecs and no proofs.

**Functions in scope** (the owner's decision Q1, below).
- **Stage 1:** the functions the public spec template
  `sglib_dl_list_spec.h` specifies today (frozen digest
  `2febb3fd8ad455cb` on B1):
  - `add`
  - `get_first` and `get_last`
  - `it_init`, `it_init_on_equal` and `it_next`
  - the comparator
- **Stage 2:** `delete`, `delete_if_member`, `add_before`, `add_after`
  and `concat`, then `sort` last.

**Functions out of scope.**  sglib's other DL-list functions, which some
clients use: `find_member`, `is_member`, `len`, `reverse`,
`add_if_not_member` and the macro `SGLIB_DL_LIST_MAP_ON_ELEMENTS`.

**How to read it.**
- Each pattern has an id (A = `add`, G = `get_first`/`get_last`,
  I = iterator, C = comparator, X = use from several threads) and the
  sources it comes from.
- The coverage map puts each pattern in one category: covered by an
  existing proved client; a gap at stage 1 or stage 2, with a new
  client; checked at run time; or out of scope, with the reason.

## Sources

| Id | Source | What it does with the DL list |
|---|---|---|
| S1 | sglib `samples/dllist.c` (`../sglib/dllist.c`) | `add` from an empty list, `sort`, forward walk from `get_first`, backward walk from `get_last`, iterate and free |
| S2 | sglib `samples/selftest.c`, `double_linked_list_test` (`../sglib/selftest.c`) | several lists alive at once; `add`, `concat`, `add_after`, `add_before`, `sort`, `find_member`, `is_member`, `delete`, the `*_if_member` variants, `reverse`; an iterator run in lockstep with a `MAP_ON_ELEMENTS` walk and checked node by node; `it_init_on_equal` with `myListCmp`, counting matches; iterate and free |
| S3 | our self-test drivers: `../selftest/selftest_dl.c:st_ops` (random operation sequences, `rac.sh`) and `../selftest/wp/driver.c:st_iter_equal` (WP) | three lists; `add` before any node; `get_first` and `get_last` from any node; iterate from any node, sometimes stopping early; `it_init_on_equal` with and without a comparator; `reverse`; free the whole list while iterating |
| S4 | B1 driver, `../b1/b1.c:b1` (WP, certified) | build by `add` at the head, walk forward from `get_first`, walk backward from `get_last`, iterate and free |
| S5 | B1a driver, `../b1a/b1a_ref.c:b1` (WP) and `../b1a/b1a.c:b1` (VST) | build, forward walk from the head, iterate and free |
| S6 | B1c driver, `../b1c/b1c_ref.c:b1` (WP) and `../b1c/b1c.c:b1` (VST) | build; iterate without freeing; `add` before a middle node recorded during that walk; iterate again from the new node (backward phase), freeing |
| U1 | denora/denora `src/uid.c` (IRC statistics server) | `add`, then `sort` after every add; `find_member`; `FIND_MEMBER` macro; `delete`; forward walks from `get_first`; the list head is a global variable |
| U2 | MisterDr/S-c-ript `src/Script/Script.c` | `add` at the head; forward walk from `get_first`; iterate and free |
| U3 | SkyRocketToys/Sonix `app/qrcode/src/main_flow/nvram/nvram.c` | `add`; walks from `get_first`; iterate, and inside the loop `delete` the current node and free it; all under a mutex.  It frees `l->data` twice in that loop, a bug in the client. |
| U4 | mexicowilly/Yella `agent/plugin/file/job_queue.c` and `.../platform/freebsd/event_source_freebsd.c` | queue: `concat` at the tail, `get_first` plus `delete` to pop, iterate and free; `add_after`, `delete`.  The list heads are fields of heap-allocated structs, and use is under a mutex. |
| U5 | ly3too/cs162 `hw3/mm_alloc.c` (a student allocator) | `sort`, `delete`, `delete_if_member`, `add_after` |
| U6 | HugoCornelis/heccer `des.c` (an event queue) | `add`, `sort`; pop with `get_first` + `delete` |
| U7 | buckyos/bdt2 `c/src/BDTCore/History/KeyManager.imp.inl` | `add_before`, `add_after`, `delete`, `delete_if_member`; the list heads are struct fields |
| H1 | embench/embench-iot `src/sglib-combined/combined.c` (a benchmark, copied into about 40 other repositories) | `add` 100 nodes, `sort`, walk from `get_first`; never frees |
| H2 | tracer-x/TRACER `.../CUTE/benchmarks/sglib-dllist-cute.c` (a concolic-testing driver, with buggy variants) | random sequences over `add`, `add_before`, `add_after`, the `*_if_member` variants, `delete`, `find_member`, `is_member`, `get_first`, `get_last`, `len`, `sort` |
| R | my review of the API (`../sglib/sglib.h`) | patterns no source shows, but the API allows |

**Open-source users: 7 projects (8 files), U1–U7.** These were found by
GitHub code search for `SGLIB_DEFINE_DL_LIST_FUNCTIONS` on 2026-11-11.
- **What the search returned:** 477 files. Most were copies of `sglib.h`
  itself, of sglib's own samples (S1, S2), or of the embench/BEEBS
  benchmark (H1, about 40 copies; BEEBS's `sglib-dllist` is S1).
- **Users found:** U1–U7 are the only applications found.
  - **None** uses `it_init_on_equal` or `get_last`.
  - Six of the seven use `sort` or `delete` (stage 2).
- **Not searched:** code outside GitHub (other forges, distribution
  packages).

## Usage patterns, by function

### `add`

| Id | Pattern | Sources |
|---|---|---|
| A1 | add to an empty list (`*list == NULL`) | S1–S6, U1, U2, U3, U6, H1, H2 |
| A2 | add at the head, building a list by prepending | S1, S2, S4, S5, S6, U2, H1 |
| A3 | add before a node that is not the head | S3 (`st_ops`, any node), S6 (step 3), H2 |
| A4 | add, then keep using nodes of the old list as before (walk from the old head, iterate from an old node) | S3, S6, R |
| A5 | add a node whose link fields are uninitialised (only the payload written) | S1, S2, S4–S6, U2, H1 |
| A6 | add, then `sort`, `delete`, `find_member`, `concat` on the same list | S1, S2, U1, U3, U6, H1, H2 |
| A7 | several lists alive at once, each built with `add` | S2, S3 |
| A8 | add to a list whose head variable is a global, or a field of a heap-allocated struct | U1 (global), U3 (field of a global struct), U4 and U7 (fields of heap structs) |
| A9 | move a node from one list to another (decided 2026-11-11: `delete`, then `add`) | R (Q8) |

### `get_first` / `get_last`

| Id | Pattern | Sources |
|---|---|---|
| G1 | from the head, then walk forward through `next` (or backward from `get_last` through `previous`), reading payloads | S1, S4, U1, U2, U3, H1 |
| G2 | from a node that is not the head (or not the last) | S3, H2, R |
| G3 | on NULL (the empty list) | S3, S4 (n = 0), H2 |
| G4 | `get_first` then `delete` that node (pop) | U4, U6 |
| G5 | after `sort` (the old head pointer is no longer the head) | S1, S2, H1 |

### Iterator (`it_init`, `it_init_on_equal`, `it_next`)

| Id | Pattern | Sources |
|---|---|---|
| I1 | iterate the whole list, reading payloads, freeing nothing | S2, S3, S6 |
| I2 | iterate and free each node returned | S1, S2, S3, S4, S5, S6, U2, U4 |
| I3 | iterate, then reuse the list (`add`, iterate again) | S3, S6 |
| I4 | start at a node that is not the head (the backward phase runs) | S3, S6 |
| I5 | iterate an empty list (`list == NULL`) | S3, S4 (n = 0) |
| I6 | stop part-way, then reuse the list (and the iterator struct) | S3 (`st_ops` case 5) |
| I7 | `it_init_on_equal` with a comparator: visit only nodes equal to `equalto` | S2, S3 (`st_iter_equal`) |
| I8 | `it_init_on_equal` with a NULL comparator (`it_init` does this internally) | S3, and every `it_init` |
| I9 | two iterators over one list, nested or interleaved | R; S2 interleaves one iterator with a `MAP_ON_ELEMENTS` walk |
| I10 | the iterator visits each node once, in sglib's order, checked against an independent walk | S2 (`assert(ll == _current_element_)`) |
| I11 | delete (unlink) the current node inside the loop, then free it | U3 |
| I12 | add a node to the list while an iteration is in progress | R |
| I13 | `it_next` called again after it returned NULL (memory safety of the call only) | R |
| I14 | the iterator struct lives in heap memory (a field of a malloc'ed struct) | R |

### Comparator

| Id | Pattern | Sources |
|---|---|---|
| C1 | a pure function comparing payload fields, passed as `subcomparator` | S2, S3 (`myListCmp`) |
| C2 | a macro inlined by sglib (`DLLIST_COMPARATOR`), used by `sort` and `find_member` | S1, U1, H1 |
| C3 | a comparator that updates its own state (a counter, a log), not the nodes | R (Q6) |
| C4 | a comparator that writes to the nodes, payload included | R (Q6) |

### Use from several threads

| Id | Pattern | Sources |
|---|---|---|
| X1 | the list used from several threads, with a lock taken around every call | U3, U4 |
| X2 | the list shared between threads without a lock | R (Q7) |

**Count:** 34 patterns:
- 9 for `add`;
- 5 for `get_first`/`get_last`;
- 14 for the iterator;
- 4 for the comparator;
- 2 for use from several threads.

The draft listed 30. A9, C4, X1 and X2 were added with the owner's decisions; the draft's C3 was split into C3 (the comparator's own state) and C4 (writes to nodes).

## Coverage map (scope decided 2026-11-11)

Each pattern is in one of five categories:
- **covered:** an existing proved client;
- **stage 1:** a gap to close while porting the current functions to VST;
- **stage 2:** a gap that needs `delete`, `delete_if_member`, `add_before`, `add_after`, `concat` and `sort`;
- **run time:** checked by step 0, not proved;
- **out of scope,** with the reason.

Where existing clients are proved today:
- **WP and VST:** B1a and B1c (`vst-run1`, `vst-run2`, `vst-b1c`); the older `../../vst/b1/verif_b1.v` proves B1a + B1b with VST.
- **WP only:** `../b1/b1.c:b1` (B1 with `get_first`/`get_last`) and `../selftest/wp/driver.c:st_iter_equal`.
- M6 re-proves every covered pattern with VST's `semax_prog`.

| Pattern | Category | Client |
|---|---|---|
| A1 add to empty | covered | `b1/b1.c:b1`, `b1a/b1a_ref.c:b1`, `b1c/b1c_ref.c:b1` (first iteration of the build loop) |
| A2 add at head | covered | the same three drivers' build loops |
| A3 add before a non-head node | covered | `b1c/b1c_ref.c:b1` step 3 |
| A4 keep using old nodes after add | stage 1 | client 1 |
| A5 elem's links uninitialised | covered | the three drivers (only `l->i` is written before `add`) |
| A6 add then sort/delete/concat | stage 2 | client 10 (`find_member` stays outside both stages; see Q1) |
| A7 several lists at once | stage 1 | client 2 |
| A8 list head a global, or in heap memory | stage 1 | client 3 (global), client 4 (heap) |
| A9 move a node between lists | stage 2 | client 13 |
| G1 from the head, walk | covered | `b1/b1.c:b1` (both walks; VST: `vst/b1/verif_b1.v`) |
| G2 from a non-head node | stage 1 | client 5 |
| G3 on NULL | covered | `b1/b1.c:b1` with n = 0 (WP proves every path) |
| G4 pop: get_first + delete | stage 2 | client 11 |
| G5 after sort | stage 2 | client 10 |
| I1 iterate, read, no free | covered | `b1c/b1c_ref.c:b1` first walk |
| I2 iterate and free | covered | `b1/b1.c:b1`, `b1a/b1a_ref.c:b1`, `b1c/b1c_ref.c:b1` |
| I3 iterate then reuse | covered | `b1c/b1c_ref.c:b1` |
| I4 start mid-list | covered | `b1c/b1c_ref.c:b1` second iteration (from the new node) |
| I5 empty list | covered | the three drivers with n = 0 |
| I6 stop part-way, reuse | stage 1 | client 6 |
| I7 with a comparator | covered | `selftest/wp/driver.c:st_iter_equal` (WP only; to be proved against the new comparator funspec) |
| I8 NULL comparator | covered | every `it_init` call (the three drivers) |
| I9 two iterators | stage 1 | client 7 |
| I10 visits each node once, in order | run time | step 0 with sglib's lockstep check (S2): checked at run time, not proved (Q4) |
| I11 delete the current node in the loop | stage 2 | client 12 |
| I12 add during an iteration | out of scope | Q3: no real user or sample does it; can be reopened if a later target needs it |
| I13 it_next again after NULL | stage 1 | client 8 |
| I14 iterator in heap memory | stage 1 | client 4 |
| C1 pure comparator function | covered | `selftest/wp/driver.c:st_iter_equal` with `myListCmp` (WP only; to be proved against the new comparator funspec) |
| C2 inlined comparator macro | stage 2 | client 10 (used by `sort`) |
| C3 comparator with its own state | stage 1 | client 9 |
| C4 comparator that writes nodes | out of scope | Q6: comparators may not write to nodes |
| X1 locked use from several threads | out of scope for M6 | Q7: compatible with the sequential specs, not proved in M6; a possible later benchmark, with no spec change |
| X2 unlocked sharing between threads | out of scope, permanently | Q7: data races |

**Totals (34 patterns):**

| Category | Count | Patterns |
|---|---|---|
| covered | 14 | A1, A2, A3, A5, G1, G3, I1, I2, I3, I4, I5, I7, I8, C1 |
| stage 1 gap | 9 | A4, A7, A8, G2, I6, I9, I13, I14, C3 |
| stage 2 gap | 6 | A6, A9, G4, G5, I11, C2 |
| run time | 1 | I10 |
| out of scope | 4 | I12, C4, X1 (for M6), X2 (permanently) |

### New clients (each a driver plus `main`, proved with `semax_prog`)

**Stage 1** (the functions specified today):

1. **Old nodes after add (A4).**
   - Build a list of n nodes, keeping the head `h` and a middle node `m`.
   - Add a new node before `m`.
   - Walk forward from `get_first(h)`, summing payloads.
   - Free everything with an iteration started at `h`.
   - This proves that `add` leaves the caller's old nodes in one whole list with the new node inserted.
2. **Several lists (A7).**
   - Build two lists from alternate input values.
   - Iterate the first and add copies of its payloads to the second, so that two lists are alive at once.
   - Free both by iteration.
3. **A global list head (A8).**
   - As B1a's driver, with `the_list` a global variable (as in U1).
   - `main` calls the driver twice.
4. **List head and iterator in heap memory (A8, I14).**
   - A malloc'ed struct holds the list head and an iterator (as U4 and U7 hold their heads).
   - Build the list through `&s->head`, iterate with `&s->it`, and free the nodes and then the struct.
   - Possible because VST's specs drop the "not in a heap block" conditions (Q5).
5. **get_first/get_last from the middle (G2).**
   - Build a list; take a middle node.
   - `get_first(mid)` and walk forward; `get_last(mid)` and walk backward.
   - Free by iteration from `mid`.
6. **Partial iteration (I6).**
   - Build a list; iterate from the head and stop after k nodes.
   - Start a new iteration with the same iterator struct and free every node.
7. **Two iterators (I9).**
   - Build a list.
   - For each node returned by an outer iterator, run an inner iterator over the whole list and count the nodes with the same payload.
   - Then free by iteration.
8. **it_next after the end (I13).**
   - After a complete iteration, call `it_next` once more.
   - The client shows only that this call is memory safe. It makes no
     claim about what the call returns (memory safety only).
9. **A comparator with its own state (C3).**
   - `it_init_on_equal` with a comparator that compares payloads and increments a counter it owns (a static variable, or a struct the client passes).
   - The client's predicate for the comparator's state is "the counter equals k".
   - The client reads the count after the iteration.
   - This exercises the comparator funspec decided under Q6.

**Stage 2** (needs `delete`, `delete_if_member`, `add_before`, `add_after`, `concat`, `sort`):

10. **sort and friends (A6, G5, C2).**
    - Build a list, `sort` it (the comparator is an inlined macro, as in S1), walk from the new head, `delete` one node and free it, `concat` a second list, then iterate and free.
11. **Pop (G4).**
    - Use the list as a queue: `get_first` then `delete` and free, until empty (as U4 and U6).
12. **Iterate and delete (I11).**
    - During an iteration, `delete` and free the current node (as U3 does, without its double free).
13. **Delete then add (A9).**
    - Move every node with an even payload from list 1 to list 2 by `delete` then `add`.
    - Free both lists.

## The owner's decisions (2026-11-11)

The owner decided all eight open questions of the draft on 2026-11-11.

- **Q1 — Functions beyond the current spec: yes, in two stages.**
  - **Stage 1** ports the functions specified today to VST: `add`, `get_first`/`get_last`, `it_init`, `it_init_on_equal`, `it_next`, and the comparator.
  - **Stage 2** adds `delete`, `delete_if_member`, `add_before`, `add_after` and `concat`, then `sort` last.
  - For memory safety, `sort` only has to promise that its result is a whole list of the same nodes.
  - `find_member`, `is_member`, `len`, `reverse`, `add_if_not_member` and `MAP_ON_ELEMENTS` are in neither stage.
- **Q2 — Delete the current node during an iteration: yes, at stage 2.**
  - A client may delete and free the current node.
  - The iterator's state constrains only the links it will follow: previous links on the part still to be walked backward, next links on the part still to be walked forward.
  - Deleting a node not yet visited stays forbidden.
- **Q3 — Add during an iteration: out of scope.**
  - No real user or sample does it; the pattern came only from our review of the API.
  - It can be reopened if a later target needs it.
- **Q4 — Iterator order and coverage: out of scope for the proofs.**
  - The project's goal is memory safety, not functional correctness.
  - Step 0 checks order and coverage at run time with sglib's lockstep check: I10 is checked at run time, not proved.
- **Q5 — List heads and iterators in heap memory: allowed.**
  - The VST specs drop every "not in a heap block" condition.
  - Ownership separates the head cell from the nodes.
- **Q6 — Comparators.**
  - **Dropped:** the fixed comparator set `(n, f1, ..., fn)` and `cmp_reads`.
  - `subcomparator` is NULL or a function proved against the comparator funspec. That funspec:
    - takes read access to the two whole nodes and returns them unchanged;
    - returns an int;
    - may update its own state, described by a predicate the client chooses (sglib passes it through).
  - Comparators that write to nodes, payload included, are out of scope.
- **Q7 — Concurrency: M6 is sequential only.**
  - M6 has sequential funspecs and sequential clients.
  - Clients that take a lock around every call (U3, U4) are compatible with these specs but are not proved in M6. A concurrent client could be a later benchmark, with no spec change.
  - Clients that share the list between threads without a lock are permanently out of scope: they have data races.
- **Q8 — Moving a node between lists: forbidden by `add`.**
  - `add`'s `elem` must be a node the client owns on its own, not part of any list. In VST this follows from ownership.
  - A node moves between lists by `delete` then `add`; client 13 covers that at stage 2.

## Notes on the current spec (digest `2febb3fd8ad455cb`, not changed here)

The notes are about the frozen ACSL spec. The decisions above settle each one for the VST spec.

1. **Heap-resident list heads and iterators** (`!heap` preconditions).
   - Not supported by the ACSL spec.
   - **Resolved for VST by Q5:** the VST specs drop these conditions, and client 4 covers them.
2. **No order or coverage guarantee for the iterator.**
   - **Resolved by Q4:** it stays out of the proofs on purpose, and step 0 checks it at run time. sglib's lockstep self-test (S2) remains provable only for its safety part.
3. **Comparators: a declared finite set, read-only.**
   - **Resolved for VST by Q6:**
     - The set and `cmp_reads` are dropped.
     - Any function proved against the comparator funspec is allowed, including one with its own state (client 9).
     - Writes to nodes stay out of scope.
4. **`in_old_list` quantifies over every whole list holding `*list`.**
   - In VST, `add`'s funspec names the caller's list directly (both VST runs did). Q8 makes `elem` a separately owned node.
   - The runtime check (step 0) is a property of the checker functions of M6 precondition 2.
5. **No spec for the other DL-list functions.**
   - **Resolved by Q1:** they come into scope at stage 2 (`find_member` and the rest excepted).
6. **ACSL-only parts** (`payload_init`, the ghost liveness model).
   - Gone under VST: liveness is ownership.
