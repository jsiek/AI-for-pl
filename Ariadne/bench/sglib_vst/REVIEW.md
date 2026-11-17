# Review notes: funspecs against the English, and open questions

For the owner's review of the stage-1 draft (`SPEC.md`,
`spec_dllist.v`).  Section 1 lists every place where the Coq says more
or less than the English.  Section 2 is the unanchored-postcondition
review (plan Q11, rule 2) done by hand on each funspec.  Section 3
lists the decisions still open, as questions; the draft takes the
option marked *(draft)* only so that it compiles.

## 1. Where the Coq and the English differ

1. **Payloads.**  The Coq tracks payloads (`ps`): `add` ends with
   `whole_list (ins j e s) (ins j ev ps)`, and every other function
   returns the nodes with the same payloads.  The English says "the
   same contents" and "keeps its payload", so they agree; but this is
   functional information beyond memory safety (a client may use it,
   for example to know that a payload it wrote is still there).
2. **Full ownership at `Ews`.**  A node is `data_at Ews` +
   `malloc_token Ews`.  The English says "owns"; the Coq fixes the
   share to `Ews`, so a client with only part of a node (a read share)
   cannot call any function.  (Question R5.)
3. **`malloc_token`.**  Every node of a list, and `add`'s `elem`, must
   come from `malloc` (English: "a node is a block returned by
   `malloc`").  A list of static or stack nodes is not supported.
   (Question R3.)
4. **"Distinct nodes"** in the English is not a separate clause in the
   Coq: it follows from the separate `cell`s.
5. **The iterator's `currentelem`.**  The Coq's `it_rep` fixes
   `currentelem == r` after every call; the English says so too.
   `it_next`'s precondition leaves it arbitrary (`cur`).
6. **The comparator writes no node.**  `cmp_spec` quantifies over any
   readable shares `sha`, `shb`; a comparator proved against it must
   work for read-only shares, so it cannot write a node, not even
   temporarily.  The English says "read access", which is the same.
   The comparator may not free or keep a node either (the postcondition
   gives both back).
7. **The comparator state is fixed per program.**  The Coq takes
   `CS : Type` and `Rc : CS -> mpred` as Section parameters, so every
   funspec is `... Rc`: one state predicate per program, chosen by the
   client, with the value `st` varying.  The English says "each program
   chooses one comparator state".  (Question R2.)
8. **`equalto` is lent at any readable share**, its fields may be
   uninitialised, and it must not be a node of the list being iterated:
   the list's nodes are owned at `Ews` by `cells`, and the client cannot
   also lend a share of one of them.  The English says "owned by the
   caller on its own: not a node of the list".  (Question R6.)
9. **No condition on `equalto` when `subcomparator` is NULL** (`cmp_env
   nullval ... = emp`), as in the English and in B1c.
10. **Iteration step and the empty window.**  `iter_step` does not say
    that NULL means no node is left to visit (Q4: no coverage).  The
    English says the same.  sglib does in fact return NULL only when
    `b' = -1` and `f' = Zlength s`.  (Question R1.)
11. **A node is returned at most once.**  `iter_step` puts the returned
    node inside the new window, so a later step cannot return it.  This
    is more than "memory safety only", but a client that frees returned
    nodes needs it.  The English says it ("a node is returned at most
    once").
12. **Termination.**  VST proves partial correctness; the English says
    termination is not required.  A function that loops forever (for
    example `get_first` on a cyclic list) is excluded by the
    precondition, not by the proof.
13. **Where variables live.**  The Coq has no `!heap` condition; the
    English says so (Q5).
14. **What "writable iterator" means.**  `it_init` requires
    `data_at_ sh t_it it` with `writable_share sh`, and leaves all five
    fields initialised (`it_rep`); `it_next` requires them initialised.

## 2. Unanchored-postcondition review (Q11, rule 2), by hand

`harness/spec_lint.py` reads ACSL, so the check was done by reading each
VST postcondition for an existential, or a returned value, tied to no
parameter or `WITH` value.

| Funspec | Existentials / results | Anchored to |
|---|---|---|
| `add_spec` | none | `lp`, `e`, `ev`, `s`, `ps`, `j` (the result list is `ins j e s`) |
| `get_first_spec` | result | `Znth_or_null s 0` |
| `get_last_spec` | result | `Znth_or_null s (Zlength s - 1)` |
| `it_init_on_equal_spec` | `b`, `f`, `r`, `st'` | `b`, `f`, `r` by `init_step s j`; `whole_list s ps` returned. **`st'` is tied to nothing** (see below) |
| `it_init_spec` | `b`, `f`, `r` | `init_step s j`; `whole_list s ps` |
| `it_next_spec` | `b'`, `f'`, `r`, `st'` | `b'`, `f'`, `r` by `iter_step s b f`; both segments of `s`, `ps` returned. **`st'` is tied to nothing** |
| `cmp_spec` | `r`, `st'` | the nodes come back with `va`, `vb`. **`r` and `st'` are tied to nothing** |

The three unanchored items are the comparator's state and result.  They
are unanchored by design under Q6 (the spec makes no promise about what
a comparator computes or how its state changes), and only the client's
own `Rc` constrains `st'`.  (Question R2 asks whether that is what the
owner wants.)

## 3. Open questions for the owner

* **R1. Does NULL from the iterator mean that no node is left to
  visit?**  The draft says no (Q4 read strictly: no coverage).
  Consequence: a client that iterates and frees each node (I2) cannot
  prove that it freed all of them, so its postcondition must allow
  leftover nodes; B1, B1a and B1c's drivers, whose postconditions own
  nothing, would not re-verify as stated.  The alternative adds
  `r = NULL -> b' = -1 /\ f' = Zlength s` to `iter_step` (true of
  sglib; it says nothing about order or which nodes the comparator
  skips).
* **R2. The comparator state: one predicate per program, or per
  iteration?**  The draft makes `Rc : CS -> mpred` a parameter of the
  whole spec, so a program with two kinds of comparator state combines
  them in one `CS`.  The alternative puts the predicate in each
  iteration's `WITH`.  VST 2.17's `WITH` (`NDmk_funspec`) refuses an
  `mpred` there (coqc: universe inconsistency, checked with a probe
  file), so that needs dependent funspecs (`mk_funspec` with an `Mpred`
  type tree) and hand-written non-expansiveness proofs.
  Also: should the comparator's postcondition say anything about the
  new state (for example "the state changes only through the client's
  own update relation")?
* **R3. Must every node come from `malloc`?**  The draft requires a
  `malloc_token` for each node and for `add`'s `elem`.  None of the
  survey's clients puts a static or stack node in a list; dropping the
  token would allow it but then no stage-2 client could free a node
  returned by `delete` without proving where it came from.
* **R4. Stage 2 compatibility of the iterator.**  Q2 (stage 2) says the
  iterator state constrains only the links it will follow.  The draft's
  `it_next` borrows whole segments with both links.  Should stage 1
  already use the weaker state (only `ptr_to_previous` on `s[0..b+1)`
  and only `ptr_to_next` on `s[f..k)`), so that stage-1 clients need not
  be re-proved at stage 2?  If stage 2 changes what `it_next` borrows
  and gives back, the stage-1 client proofs that use it must be redone;
  using the weaker state now avoids that, at the price of a more complex
  stage-1 spec (clients must convert between whole segments and
  one-link segments).
* **R5. Shares.**  Should the functions that only read (`get_first`,
  `get_last`, the iterator) accept a list owned at any readable share,
  rather than `Ews`?  No survey pattern needs it (sequential use, Q7).
* **R6. May `equalto` be a node of the iterated list?**  The draft says
  no (it is lent separately).  The survey's I7 clients pass a stack
  key, so they fit.  Allowing it needs the list predicate to be split by
  shares.
* **R7. Parameterisation (Q12).**  The draft is the `dllist` instance
  (see `README.md` for what parameterising would take).  Is that
  acceptable for the review, with the generic version later?
