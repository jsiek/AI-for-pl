# Client survey: sglib's doubly linked list (plan M6, draft for approval)

**Status: draft, 2026-11-11.  Not approved.**  Plan M6, precondition 3:
the owner approves this survey together with the public spec, and it is
then frozen with the spec.  A later spec change must keep every
surveyed client provable.  This draft contains no funspecs and no
proofs.

**Functions in scope.**  These are the functions the public spec template
`sglib_dl_list_spec.h` specifies (frozen digest `2febb3fd8ad455cb` on
B1):

- `add`
- `get_first` and `get_last`
- `it_init`, `it_init_on_equal` and `it_next`
- the comparator contract (`SGLIB_DL_LIST_CONTRACT_COMPARATOR`)

**Functions out of scope.**  sglib's other DL-list functions have no
spec yet, but the clients below use them: `sort`, `delete`,
`delete_if_member`, `add_before`, `add_after`, `add_if_not_member`,
`concat`, `find_member`, `is_member`, `len`, `reverse`, and the macro
`SGLIB_DL_LIST_MAP_ON_ELEMENTS`.  Whether they come into scope is open
question Q1.

**How to read it.**
- Each pattern has an id (A = `add`, G = `get_first`/`get_last`,
  I = iterator, C = comparator) and the sources it comes from.
- The coverage map says which existing client already proves the
  pattern (WP today; M6 re-proves it with VST's `semax_prog`), or GAP
  with a sketch of a new client.

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
  - Six of the seven use `sort` or `delete`, which are out of scope.
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
| I13 | `it_next` again after it returned NULL | R |
| I14 | the iterator struct lives in heap memory (a field of a malloc'ed struct) | R |

### Comparator

| Id | Pattern | Sources |
|---|---|---|
| C1 | a pure function comparing payload fields, passed as `subcomparator` | S2, S3 (`myListCmp`) |
| C2 | a macro inlined by sglib (`DLLIST_COMPARATOR`), used by `sort` and `find_member` | S1, U1, H1 |
| C3 | a comparator with side effects (counting, logging) or one that writes nodes | R |

**Count:** 30 patterns: 8 for `add`, 5 for `get_first`/`get_last`, 14 for the iterator and 3 for the comparator. Three of them (A6, G4, G5) mainly concern functions outside the scope.

## Coverage map

Each pattern is mapped to an existing client (file:function, and how it is proved today), or to **GAP** with a sketch of a new client to be proved with `semax_prog` (Q11 rule 1).
- **Proved by both WP and VST:** B1a and B1c (`vst-run1`, `vst-run2`, `vst-b1c`); the older `../../vst/b1/verif_b1.v` proves B1a + B1b.
- **WP only:** `../b1/b1.c:b1` (B1 with `get_first`/`get_last`) and `../selftest/wp/driver.c:st_iter_equal`.

| Pattern | Covered by | |
|---|---|---|
| A1 add to empty | `b1/b1.c:b1`, `b1a/b1a_ref.c:b1`, `b1c/b1c_ref.c:b1` (first iteration of the build loop) | covered |
| A2 add at head | the same three drivers' build loops | covered |
| A3 add before a non-head node | `b1c/b1c_ref.c:b1` step 3 | covered |
| A4 keep using old nodes after add | **GAP** | sketch 1 |
| A5 elem's links uninitialised | the three drivers (only `l->i` is written before `add`) | covered |
| A6 add then sort/delete/find | **GAP** if Q1 brings those functions into scope; otherwise out of scope | sketch 2 |
| A7 several lists at once | **GAP** | sketch 3 |
| A8 list head a global or a heap field | global: **GAP** (all three drivers keep the head in a local); heap field: not supported by the current spec (see Notes) | sketch 4 |
| G1 from the head, walk | `b1/b1.c:b1` (both walks) | covered (WP; VST: `vst/b1/verif_b1.v`) |
| G2 from a non-head node | **GAP** (B1 calls them only with the head) | sketch 5 |
| G3 on NULL | `b1/b1.c:b1` with n = 0 (WP proves every path) | covered |
| G4 pop: get_first + delete | out of scope (delete) | Q1 |
| G5 after sort | out of scope (sort) | Q1 |
| I1 iterate, read, no free | `b1c/b1c_ref.c:b1` first walk | covered |
| I2 iterate and free | `b1/b1.c:b1`, `b1a/b1a_ref.c:b1`, `b1c/b1c_ref.c:b1` | covered |
| I3 iterate then reuse | `b1c/b1c_ref.c:b1` | covered |
| I4 start mid-list | `b1c/b1c_ref.c:b1` second iteration (from the new node) | covered |
| I5 empty list | the three drivers with n = 0 | covered |
| I6 stop part-way, reuse | **GAP** | sketch 6 |
| I7 with a comparator | `selftest/wp/driver.c:st_iter_equal` | covered (WP only) |
| I8 NULL comparator | every `it_init` call (the three drivers) | covered |
| I9 two iterators | **GAP** | sketch 7 |
| I10 visits each node once, in order | **GAP**, and not expressible in the current spec (see Notes) | Q4 |
| I11 delete the current node in the loop | out of scope (delete) | Q2 |
| I12 add during an iteration | **GAP** | sketch 8, Q3 |
| I13 it_next after NULL | **GAP** (a one-line extension of any driver) | sketch 9 |
| I14 iterator in heap memory | not supported by the current spec (see Notes) | Q5 |
| C1 pure comparator function | `selftest/wp/driver.c:st_iter_equal` with `myListCmp` | covered (WP only) |
| C2 inlined comparator macro | out of scope (used only by sort/find) | Q1 |
| C3 comparator with side effects | not supported by the current spec | Q6 |

**Totals (30 patterns):**
- **Covered: 14** (A1, A2, A3, A5, G1, G3, I1, I2, I3, I4, I5, I7, I8, C1). I7 and C1 are proved by WP only so far; G1 by WP and by the older VST proof of B1.
- **Gaps with a sketch: 8** (A4, A7, A8 for a global head, G2, I6, I9, I12, I13). A6 becomes a ninth if Q1 brings `sort`/`delete` into scope.
- **Out of scope or open questions: 8** (A6, G4, G5, I10, I11, I14, C2, C3). A8 for a head in heap memory is also listed under Notes.

### Sketches of new clients (each a `b1`-style driver plus `main`, proved with `semax_prog`)

1. **Old nodes after add (A4).**
   - Build a list of n nodes, keeping the head `h` and a middle node `m`.
   - Add a new node before `m`.
   - Walk forward from `get_first(h)`, summing payloads, then free everything with an iteration started at `h`.
   - This proves that `add` leaves the caller's old nodes in one whole list with the new node inserted: the anchoring added on 2026-11-10.
2. **add, then the out-of-scope functions (A6).** Only if Q1 brings them in.
   - Build a list, `sort` it, `find_member` a value, `delete` it, then iterate and free.
   - This is sglib's own sample (S1) plus the self-test's delete loop (S2).
3. **Several lists (A7).**
   - Build two lists from alternate input values.
   - Iterate the first and add copies of its payloads to the second, so that two lists are alive at once.
   - Free both by iteration.
   - The proof must keep the two lists separate.
4. **A global list head (A8).**
   - As B1a's driver, with `the_list` a global variable (as in U1), and `main` calling the driver twice.
5. **get_first/get_last from the middle (G2).**
   - Build a list; take a middle node.
   - `get_first(mid)` and walk forward; `get_last(mid)` and walk backward.
   - Free by iteration from `mid`.
6. **Partial iteration (I6).**
   - Build a list; iterate from the head and stop after k nodes.
   - Then start a new iteration with the same iterator struct and free every node.
7. **Two iterators (I9).**
   - Build a list.
   - For each node `x` returned by an outer iterator, run an inner iterator over the whole list and count the nodes with the same payload (`it_init_on_equal` with a comparator, or a plain inner loop).
   - Then free by iteration.
   - This shows that two iterators can read the same list at once.
8. **add during an iteration (I12).**
   - Iterate from the head. When the current node's payload is even, add a new node before it.
   - Then free all by a new iteration.
   - Whether the new node is visited by the running iteration is a spec question (Q3).
9. **it_next after the end (I13).**
   - Any driver; after the loop ends, call `it_next` once more and require NULL.

## Open questions for the owner

- **Q1 — Functions beyond the current spec.**
  - Six of the seven open-source users (U1, U3–U7) rely on `sort`, `delete`, `delete_if_member`, `add_before`, `add_after` or `concat`. So does sglib's own sample (`sort`).
  - Do these come into M6's public spec? If not, patterns A6, G4, G5, I11 and C2 stay out of scope.
- **Q2 — Delete the current node during an iteration (U3).**
  - Safe in sglib today: the iterator has already moved past the current node.
  - It needs `delete` in the spec and an iterator spec that survives an unlink.
- **Q3 — add during an iteration (I12).**
  - In scope?
  - If so, must the spec say whether the new node is visited? That depends on where it lands relative to the iterator's two positions.
- **Q4 — Order and coverage (I10).**
  - "Visits every node once, in sglib's order" is a functional property, not memory safety. It was not added on 2026-11-08.
  - sglib's self-test checks it. In scope for M6, or left to runtime tests?
- **Q5 — List heads and iterators in heap memory (A8, I14).**
  - The current spec requires the cell holding `*list` and the iterator struct not to be heap blocks (`!heap(\base_addr(..))`, from the ACSL liveness model).
  - Real users keep list heads in malloc'ed structs (U4, U7).
  - Under VST's ownership this restriction may not be needed. Should M6's spec allow it?
- **Q6 — Comparators.**
  - The current contract allows only comparators that read the fields `cmp_reads` names and write nothing.
  - Are comparators with side effects (C3: counting, logging) or ones that write nodes out of scope?
  - Is the finite set of allowed comparators (the template parameter `cmps`) still wanted under VST, where a funspec on a function pointer could replace it?
- **Q7 — Concurrency.**
  - U3 and U4 use the list under a mutex from several threads.
  - Out of scope for M6 (sequential clients only)?
- **Q8 — Moving a node between lists.**
  - `add` with an `elem` that is still a node of another list breaks that other list.
  - Should the spec forbid it (elem not in any live list), or leave it to the client?

## Notes on the current spec (digest `2febb3fd8ad455cb`, not changed here)

1. **Heap-resident list heads and iterators are not supported (A8, I14).**
   - `add` requires `!heap(\base_addr(list))`; the iterator functions require `!heap(\base_addr(it))`.
   - So the head stored in a field of a malloc'ed struct (U4, U7), or an iterator inside a heap object, cannot be proved.
2. **No order or coverage guarantee for the iterator (I10).**
   - `iter_ok` says each returned node is a live node of the list, between the two walks. It does not say every node is returned exactly once, or in which order.
   - So sglib's lockstep self-test (S2) cannot be proved; its safety part can.
3. **Comparators: a declared finite set, read-only (C3).**
   - The comparator set is a template parameter (`cmps`), and the comparator contract forbids writes.
   - Comparators with side effects, or any function pointer outside the set, are not supported.
4. **add over all whole lists holding `*list`.**
   - `in_old_list` quantifies over every whole list holding the old `*list`. That is the one list (lemma `dll_shared` in B1c).
   - It is not checked at run time (step 0 lists it).
5. **No spec for the other DL-list functions (Q1).** Most real clients use `sort` or `delete`.
6. **ACSL-only parts.**
   - The driver's `payload_init` precondition and the ghost liveness model (`live`, `dead`, `__heap`) belong to the WP pipeline.
   - Under VST, liveness is ownership; M6 restates the spec as funspecs plus `SPEC.md`.
