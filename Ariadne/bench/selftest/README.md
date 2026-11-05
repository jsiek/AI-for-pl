# sglib's self-test (`../sglib/selftest.c`)

sglib's own test program, vendored unmodified (`../sglib/README.md`).
It runs eight tests (arrays, lists, hashed list, doubly linked list,
sorted list, red-black tree), ten passes each, on 1000 random values,
and checks every result with `assert`.  Plan Q12 uses its doubly linked
list test as a second client of B1's contracts.

```bash
./check.sh        # seed 1; ./check.sh 7 for seed 7.  Needs the M0 image.
./rac.sh          # the DL-list test against B1's public contracts (~80 s)
```

## Fixed seed

`main` calls `srandom(time(NULL))`.  The file stays unmodified: it is
linked with `seed.c` under `-Wl,--wrap=time`, so its call to `time`
goes to `__wrap_time`, which returns the seed (`SELFTEST_SEED`, default
1).  `check.sh` checks in the binary that the call goes to
`__wrap_time`.

## Result

| Build | Seeds | Result |
|-------|-------|--------|
| gcc 12, `-fsanitize=address,undefined -fno-sanitize-recover=all`, LeakSanitizer on | 1, 7, 12345 | passes: exit 0, no sanitizer report, no failed `assert` (about 2 s) |

## Against B1's public contracts (`rac.sh`, plan Q12)

`selftest_dl.c` includes `selftest.c` unmodified and instantiates the
spec template (`../sglib_spec`) at selftest's parameters:
`SGLIB_DL_LIST_SPEC(DoubleLinkedList, previous, next)` and the six
`SGLIB_DL_LIST_CONTRACT_*` macros (add's payload field: `n`), each on a
prototype after the function's definition (Frama-C merges it into the
definition).  The comparator `myListCmp` is not a template parameter
(`../sglib_spec/README.md`).  The instantiation type is
`DoubleLinkedList`, the typedef of `struct MyIntList` that selftest.c
passes to `SGLIB_DEFINE_DL_LIST_FUNCTIONS`.  `main` seeds `srandom` and
runs `double_linked_list_test` once.  `malloc`/`free` of selftest.c go
through `st_malloc`/`st_free`, which keep the allocation registry (the
liveness model's runtime meaning) and write a node's padding, as B1's
allocator does.

B1's RAC pipeline then runs unchanged in kind: `acsl_expand.py`,
`gen_twins.py` (now skipping overloads among the libc's own logic, which
`<string.h>` brings in), `gen_rac.py --name selftest_dl --no-harness`
(24 contract clauses: 13 kept, 11 rewritten with witnesses; 6 dropped,
all `assigns`), then E-ACSL with RTE (`-rte-initialized @all`).
`eacsl_collect.c` replaces E-ACSL's assertion function so that every
failed check is counted and the run goes on.

**Result (seed 1).**  ASan + UBSan: the test passes.  E-ACSL: the test
runs to the end; no RTE check fails (no undefined behaviour and no read
of uninitialised memory in the test or in sglib); 12 distinct contract
checks fail, 10023 times in all:

| Function | Clause | Fails | Cause |
|----------|--------|-------|-------|
| `add` | requires `live_dll(\null, *list, s) && !mem(elem, s)` | 2997 of 3000 calls | `all_init`: the nodes' `color`, `left_ptr`, `right_ptr` (the RB-tree fields of `struct MyIntList`) are never written by the DL-list test |
| `add` | ensures `live_dll(\null, *list, s)` | 3000 of 3000 | the same; it fails even on the 3 calls whose precondition holds (adding to an empty list), because `elem_init` asks only for `n` while `all_init` asks for every field |
| `get_first` | requires `list == \null \|\| in_live_list(list)`; ensures `heads_list` | 7 of 7 | `all_init`, as above |
| `it_init` | requires `live_dll(\null, list, s)` | 1 call (2 counted with uninitialised nodes) | `list` is not the head: after `sglib_DoubleLinkedList_reverse(&list)`, `list` is the last node (reverse does not move `*list`) |
| `it_init_on_equal` | requires `live_dll(\null, list, s)` | 2 (1 direct, 1 from `it_init`) | the same |
| `it_init_on_equal` | requires `subcomparator == \null` | 1 | the test passes `myListCmp` |
| `it_next` | requires `it->subcomparator == \null` | 1 | the same |
| `it_next` | requires (the iterator's two states) | 1001 | the walk starts at the last node, so `it_next` runs the backward phase (`prevelem` not NULL and not the head), which the contract does not describe |
| `it_init`, `it_init_on_equal`, `it_next` | ensures `iter_ok` | 1, 2, 1000 | `iter_ok` says the backward walk is done (`prevelem == \null`), false while it runs |

(Counts are from the diagnostic run with every node zero-filled at
allocation, `zero`, except the `add` / `get_first` rows; with the nodes
as the test leaves them, the iterator counts double, since `all_init`
also fails there.)

The two probes isolate `all_init`: one `add` of a fresh node to an empty
list fails its postcondition when only `n` is written (`probe`), and
passes every check when all fields are written (`probefull`).  With
every node zero-filled (`zero`), all `add` and `get_first` failures go
away and only the iterator rows remain.

**Reading.**  Every failing precondition marks a contract too strong
for this client; no failure points to a bug in sglib (the self-test's
own asserts pass, and so do ASan, UBSan and every RTE check).  The
failing postconditions are of two kinds: `add`'s, where the contract
pair is inconsistent for a node type with more fields than the payload
and the links (a precondition-respecting call cannot meet the
postcondition), and the iterator's, which follow from preconditions that
already failed.  The other sglib functions the test calls (`concat`,
`add_before`, `add_after`, `delete`, `find_member`, `is_member`,
`sort`, `reverse`, `len`, the `*_if_not_member` and `delete_if_member`
variants) have no contract in B1 and are not checked; `get_last` is
specified but the test does not call it.

Changes to the public contracts proposed for the owner (Q11; not made):

1. `all_init` (and so `live_dll`, `in_live_list`, `iter_ok`) should not
   require fields the list code never reads or writes.  Either restrict
   it to the payload and the two links (a template parameter listing
   the payload fields), or make `add`'s `elem_init` require every field
   but the links.  The first is weaker for clients and keeps B1's
   instantiation (payload `i`) equivalent.
2. `add`, `it_init`, `it_init_on_equal`: accept any node of a whole live
   list (`in_live_list`), not only its head, as sglib does
   (`get_first` / `get_last` already do).
3. `it_init_on_equal` / `it_next`: specify the subcomparator case
   (calls through a function pointer: a contract on the comparator,
   plan Q12), and `iter_ok`: describe the backward phase too
   (`prevelem` a node of the same list).
