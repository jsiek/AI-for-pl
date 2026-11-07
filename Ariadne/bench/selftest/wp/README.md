# The self-test's instantiation, for WP (plan Q12, decision 3)

B1 passes no subcomparator, so the iterator's comparator path is proved
here, on the self-test's instantiation of the doubly linked list:
`DoubleLinkedList` (selftest.c's typedef of `struct MyIntList`),
`previous`, `next`, comparator `myListCmp`, `cmp_reads` = `st_cmp_reads`
(`\initialized(&p->n)`), comparator set `(1, myListCmp)`.

```bash
python3 -I gen_wp.py   # writes st_wp.c (and st_gen.c, st_gen_in.c)
./run.sh               # WP: functions, then lemmas
./check.sh             # gen_wp.py, run.sh, and two mutants
```

`gen_wp.py` expands sglib's macros at these parameters (with B1's
verification refactor #1, `../../b1/refactor`), takes B1's annotated
sglib functions from `../../b1/b1.c`, renames them, and checks that the
renamed code, annotations stripped, equals the expansion token for
token.  `st_wp.c` is that code with the spec, myListCmp's comparator
contract, and our `driver.c` (`st_iter_equal`: iterate over the nodes
equal to `*te` with `myListCmp`).  The Coq scripts are B1's, copied by
`run.sh` under this instance's goal names; they apply unchanged.

**Result** (WP with Alt-Ergo, Z3, CVC5 and the Coq scripts, `-ariadne`,
`-wp-rte -rte-initialized @all`): 446 / 446 goals (431 function goals
of the six sglib functions, `myListCmp` and the driver, and 15 lemmas):
Qed 281, Alt-Ergo 141, CVC5 9, Z3 6, Coq 9.  Among them, `it_next`'s two
indirect calls: the call-point goals
(`typed_sglib_DoubleLinkedList_it_next_call_point_myListCmp_s689`,
`..._s712_part1`, `_part2`) and myListCmp's preconditions at each call.

**Mutants** (`check.sh`), each rejected only at the iterator call:

| Mutant | Rejected by |
|--------|-------------|
| `othercmp`: the driver passes `otherCmp`, a comparator with the right contract but outside the set | `it_init_on_equal`'s precondition `SGLIB_DL_LIST_SUBCMP_OK` (`..._requires_2`) |
| `noeqinit`: the driver no longer requires `te->n` initialised | `it_init_on_equal`'s precondition `cmp_reads(equalto)` (`..._requires_3`) |
