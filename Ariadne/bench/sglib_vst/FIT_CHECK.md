# Fit check: the stage-1 spec against the approved client survey

For each of the survey's 14 covered and 9 stage-1 patterns
(`../sglib_spec/CLIENT_SURVEY.md`), the funspec clauses of
`spec_dllist.v` a client relies on.  This is a reading of the spec, not
a proof: the clients are proved in the next step of M6.

**Result:** all 23 patterns are supported.  One needs a choice by the
owner to be proved as the survey's drivers state it: **I2** (marked
below, and question R1 in `REVIEW.md`).

## Covered (14)

| Pattern | Clauses relied on |
|---|---|
| A1 add to empty | `add_spec` with `s = []`, `j = 0` (`at_node`): pre `*list == Znth_or_null [] 0 = NULL`; post `*list == e`, `whole_list [e] [ev]` |
| A2 add at head | `add_spec`, `j = 0`: post `whole_list (e :: s) (ev :: ps)` (`ins 0`) |
| A3 add before a non-head node | `add_spec`, `0 < j < Zlength s`: pre `*list == Znth j s`; post `whole_list (ins j e s) (ins j ev ps)` |
| A5 elem's links uninitialised | `add_spec` pre `data_at Ews t_dl (ev, enp) e` with `enp` (and `ev`) arbitrary, `Vundef` included |
| G1 from the head, walk | `get_first_spec` / `get_last_spec` with `j = 0` / `j = Zlength s - 1`: result `Znth_or_null s 0` / `Znth_or_null s (Zlength s - 1)`; post `whole_list s ps`, which the client unfolds (`cells`) to follow the links |
| G3 on NULL | `get_first_spec` / `get_last_spec` with `s = []`: result `NULL` |
| I1 iterate, read, no free | `it_init_spec`: post `whole_list s ps`, `it_rep`, `init_step`; `it_next_spec`: the lent segments come back; `iter_step`'s `r = Znth c s` with `c` in a segment the client owns, so it can read `r->i` |
| I2 iterate and free | `iter_step`: `r = Znth c s` with `c` now inside the window, so the client may free `cell c` and lend only `cells 0 (b'+1)` and `cells f' len` next time. **Flag (R1):** with no promise that NULL ends the walk (Q4), the client cannot show that it freed every node, so a driver whose postcondition owns nothing else (as B1/B1a/B1c's) must allow leftover nodes in its postcondition |
| I3 iterate, then reuse | `it_init_spec` / `it_next_spec` return `whole_list s ps` / both segments unchanged (borrowing); the client reassembles `whole_list s ps` and calls `add` (`add_spec`) or `it_init` again |
| I4 start mid-list | `it_init_spec` with `0 < j`: `init_step` from window `(j, j+1)` |
| I5 empty list | `it_init_spec` with `s = []`: `init_step` from `(-1, 0)` forces `r = NULL` |
| I7 with a comparator | `it_init_on_equal_spec` / `it_next_spec` with `cmp_env scp eq sheq veq st` = `func_ptr' (cmp_spec Rc) scp * data_at sheq t_dl veq eq * Rc st`; the comparator is proved against `cmp_spec Rc` |
| I8 NULL comparator | `cmp_env nullval _ _ _ _ = emp`; `it_init_spec` (it_init passes NULL) |
| C1 pure comparator | `cmp_spec` with `Rc := fun _ => emp` |

## Stage 1 (9)

| Pattern | Clauses relied on |
|---|---|
| A4 old nodes after add (client 1) | `add_spec` post `whole_list (ins j e s) (ins j ev ps)`: the old nodes, in order, with `e` at `j` (anchored add), so `get_first(h)` and `it_init(h)` apply with `h`'s new position |
| A7 several lists (client 2) | each list is its own `whole_list`; every funspec frames the others |
| A8 head a global / heap field (clients 3, 4) | `add_spec` pre `data_at sh (tptr t_dl) _ lp` with any writable `sh` and any `lp`: a global (`gv _the_list`) or a field of a heap struct (`field_at` split to `data_at` at `field_address`); no `!heap` condition (Q5) |
| G2 get_first/get_last from the middle (client 5) | `get_first_spec` / `get_last_spec` with any `j` (`at_node s j`): result anchored to `s` |
| I6 stop part-way, reuse (client 6) | borrowing as in I3; the iterator struct is reused through `it_rep ... |-- data_at_ sh t_it it` (`data_at_data_at_`), which `it_init_spec` requires |
| I9 two iterators (client 7) | two `it_rep`s; between calls the client owns every node and lends `cells 0 (b+1)` and `cells f len` of the iterator it calls (the inner iterator's segments are the whole list) |
| I13 it_next after NULL (client 8) | `iter_step` keeps `-1 <= b' < f' <= Zlength s`, which is `it_next_spec`'s precondition; the client lends the (possibly empty) segments again |
| I14 iterator in heap memory (client 4) | `it_init_spec` / `it_next_spec` take `data_at_ sh t_it it` / `it_rep sh it ...` with any writable `sh` at any address (Q5) |
| C3 comparator with its own state (client 9) | `cmp_spec Rc` with the program's `Rc`, e.g. `CS := (globals * Z)` and `Rc (gv, k) := data_at Ews tint (Vint (Int.repr k)) (gv _counter)`; `cmp_env` lends `Rc st` and returns `Rc st'`.  The client knows nothing about the count afterwards (memory safety only), and can read it |

## Not part of this check

Stage-2 patterns (A6, A9, G4, G5, I11, C2, D1–D4), I10 (run time) and
the out-of-scope ones (I12, C4, X1, X2).  Note for stage 2 (Q2): the
iterator's precondition here lends whole segments with both links
(`cells`); deleting the current node rewrites the links of its
neighbours, so I11 needs the weaker iterator state of Q2 (question R4).
