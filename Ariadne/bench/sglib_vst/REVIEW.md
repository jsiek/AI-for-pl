# Review notes: funspecs against the English, and open questions

These notes are for the owner's review of the stage-1 draft (`SPEC.md`,
`spec_dllist.v`).  The draft follows the owner's two decisions of
2026-11-17:
- the goal is memory safety plus leak freedom;
- public specs are minimal relative to the client survey, with the
  simplicity exception.

The sections:
1. where the Coq says more or less than the English;
2. the unanchored-postcondition review (Q11, rule 2);
3. every use of the simplicity exception, with both options;
4. the VST affinity check and how to enforce leak freedom;
5. the questions: which ones the rules now settle, and which are open.

## 1. Where the Coq and the English differ

1. **Contents.**  The Coq describes a list by its addresses `s` and its
   contents `vs` (payload and both links per node).
   - Ownership is `nodes sh s vs lo hi`; the links are pure facts
     (`prev_links`, `next_links`, `whole`).
   - "The same contents" in the English is "the same `vs`" in the Coq.
   - The client keeps the link facts it knows, because they are pure.
2. **"Distinct nodes"** is not a clause in the Coq: it follows from
   separation.
3. **NULL `list`.**  `at_node s j` with `s = []`, `j = 0`.  A caller
   passing NULL picks the empty sequence and keeps its lists in the
   frame.  `get_first`'s range is `0 .. min(j+1, k)` so that the empty
   case owns nothing.
4. **No `malloc_token`** anywhere: no function frees.  Static or stack
   nodes may be put in a list; the client keeps the tokens of its heap
   nodes in order to free them.
5. **`currentelem`** is existential in `it_rep`: it is neither read nor
   promised.  The English says "not described".
6. **The comparator writes no node, not even temporarily.**  `cmp_spec`
   quantifies over every readable share, so a comparator proved against
   it must also work at a read-only share.
7. **The comparator state is fixed per program** (`CS`, `Rc` are Section
   parameters).  The English says "each program chooses one".  (R2)
8. **`step_exact` allows either end of the window.**  sglib always takes
   the backward end first; the Coq does not promise that (no order).
   The English says "from either end".
9. **`step_any`'s "NULL means none left"** is stated for both cases,
   with and without a comparator (R1 as the owner decided).  Only the
   case without a comparator is needed by a surveyed client.
10. **The comparator's payload condition is new.**  The first draft gave
    comparators nodes with arbitrary payloads.  The survey's comparators
    (C1 `myListCmp`, C3) compute on payloads, so they could not have been
    proved against it.  `cmp_spec` now requires int payloads, and
    `it_next` / `it_init_on_equal` ask for them when a comparator is
    passed (`cmp_payloads`, `cmp_env`).
11. **Termination** is not proved (VST proves partial correctness).  A
    cyclic chain is excluded by the link facts, not by the proof.

## 2. Unanchored-postcondition review (Q11, rule 2), by hand

`harness/spec_lint.py` reads ACSL, so each VST postcondition was read
by hand for an existential, or a result, that is tied to no input.

| Funspec | Existentials / results | Anchored to |
|---|---|---|
| `add_spec` | `vs'` | `whole (ins j e s) vs'`; payloads `ins j ev` of the old ones |
| `get_first_spec`, `get_last_spec` | `r` | `r` NULL or in `s`; the nodes are returned with the same `vs` |
| `it_init_on_equal_spec`, `it_init_spec` | `b`, `f`, `r`, `st'` | `init_window scp s`; **`st'` is tied to nothing** |
| `it_next_spec` | `b'`, `f'`, `r`, `st'` | `iter_step scp s b f`; **`st'` is tied to nothing** |
| `cmp_spec` | `r`, `st'` | the nodes come back unchanged; **`r` and `st'` are tied to nothing** |

The comparator's result and state are unanchored by design (Q6): the
spec makes no promise about what a comparator computes.  Only the
client's `Rc` constrains `st'`.

## 3. Uses of the simplicity exception

For each, *minimal* is what the rule asks for and *chosen* is the
draft's form.

1. **`add`'s postcondition: form E (owner, R9, 2026-11-17).**
   - *Chosen (E, `add_spec`, in `Gprog`):* `s` with `elem` inserted at
     position `j`, and `*list == elem`.
   - *Recorded alternative (M, the minimal form; it type-checked in the
     draft of e4edd591 and was removed from `spec_dllist.v` with the
     decision):* a whole list made of exactly the old nodes plus `elem`
     in some order, with `*list` some node of it:

     ```coq
     POST [ tvoid ]
       EX s': list val, EX vs': list node_v, EX l': val,
       PROP (whole s' vs';
             Permutation (combine (e :: s) (ev :: map pay vs))
                         (combine s' (map pay vs'));
             In l' s')
       RETURN ()
       SEP (data_at shl (tptr t_dl) l' lp;
            nodes sh s' vs' 0 (Zlength s')).
     ```
   - Why E is simpler:
     - it has no `Permutation`, no `combine` and no new existential
       sequence;
     - the body proof builds this list anyway;
     - a client of M must recover positions through `Permutation_in`
       and the `combine` lemmas.
   - Both account for every node, so both are leak-free.
2. **`add`'s precondition: the whole list.**
   - *Minimal:* the old `*list`, its predecessor and `elem`, with only
     `*list`'s prev link.
   - *Chosen:* the whole list.  It is simpler: every client holds a
     whole list at the call, and the re-linking lemma is proved once,
     inside `add`, rather than in every client.
   - A stronger precondition: allowed by the exception as the owner
     widened it with R8 (2026-11-17): simpler, and no surveyed client
     needs the weaker one.  Register entry R8 in the survey.
3. **The comparator's precondition: the whole node.**
   - *Minimal:* the payload field only.
   - *Chosen:* the whole node at a readable share.  It is simpler:
     `it_next` holds whole nodes, so no field splitting is needed.
   - For a callback the comparator's precondition is the library's
     promise, so a bigger one is the "stronger postcondition" case.
4. **"NULL means none left" with a comparator.**
   - *Minimal:* only without a comparator.
   - *Chosen:* both cases, as the owner decided R1.  It is simpler: one
     clause.
5. **Payloads kept.**
   - "Each node keeps its payload" is a value fact, but it is the frame
     of fields that the functions do not write.
   - *Minimal alternative:* the list predicate owns only the two link
     fields, and the client keeps the payload fields itself.  Every
     client would then split nodes into fields.
   - *Chosen:* whole nodes, with "the same contents".

`get_first` / `get_last` use the minimal result ("NULL or a node of
`s`"), not "the head" or "the last node": the exact form is no simpler.

## 4. Is VST 2.17 affine?  Enforcing leak freedom

**Result: no.  A proof cannot drop owned memory, except through `TT` in
a postcondition.**  The evidence is `affine_probe/verif_probe.v`, run by
`check.sh` step 5 with Rocq 9.0.1 `coqc` and VST 2.17.

- **The probe.**  It has two empty C functions:
  - `drop_int` takes `data_at Ews tint _ p` and its postcondition owns
    nothing;
  - `drop_node` takes `data_at_ Ews t_node p * malloc_token Ews t_node
    p` and its postcondition owns nothing.
- **What Floyd leaves.**  After `start_function. forward.` the remaining
  goals are `data_at Ews tint _ p |-- emp` and
  `data_at_ Ews t_node p * malloc_token Ews t_node p |-- emp`.
  `entailer!` and `cancel` do not close them; the probe records this
  with `Fail`.
- **Why they are false.**  VST's `emp` (msl/predicates_sl.v line 111)
  holds only of a world that extends an identity element, and a
  `data_at` at share `Ews` is not one.
- **The `TT` variants.**  With `SEP(TT)` as the postcondition, the same
  two bodies are proved by `start_function. forward.`, through
  `sepcon_TT : P |-- P * TT` (msl/log_normalize.v line 796).

So leak freedom per function is not free.  It holds exactly when no
postcondition contains `TT` or another absorbing predicate (for example
`EX R: mpred, R`, if the universe check allowed it).  VST's usual `main`
postcondition is `SEP(TT)`, and so is B1c's.  The b1 drivers'
postconditions in vst-b1c own nothing on the heap (`mem_mgr` and the
input array), so b1 itself is already leak-free.

Options for the owner (R10):
- **(a) A postcondition lint.**  No `TT`, and no existential over
  `mpred`, in any funspec postcondition, public or client.  `main`'s
  postcondition is fixed to `mem_mgr gv` plus the global variables
  `main_pre` gave it.  This is cheap and syntactic, and it lives in the
  guardrails next to the `Admitted` lint; but it relies on the lint
  recognising every absorbing form.
- **(b) An allocation counter.**  Library specs for `malloc` and `free`
  over `mem_mgr_n gv n` count live blocks (`malloc`: `n` to `n+1`;
  `free`: `n` to `n-1`), and `main`'s postcondition requires
  `mem_mgr_n gv 0`.  A leak is then caught even if `TT` hides the
  memory, because the counter is exact.  The cost: two trusted library
  specs to review, and every client threads `n`.
- **(c) Both:** (b) as the check, (a) as an early warning.

## 5. Questions

**Decided by the owner (2026-11-17):**
- **R8.** `add` requires the whole list; the simplicity exception now
  also allows a stronger precondition when it is simpler and no
  surveyed client needs the weaker one (register entry R8).
- **R9.** `add`'s postcondition is form E (exact position,
  `*list == elem`); M is recorded in section 3.

**Settled by the rules (no owner action needed unless you disagree):**
- **R1. Does NULL mean that no node is left?**  Yes: the owner decided
  this on 2026-11-17 (leak freedom).  It is in `step_any` and
  `init_window`.  Coverage without a comparator is in `step_exact`
  (Q4 amended in the survey).
- **R3. Must every node come from `malloc`?**  No.  No function needs a
  `malloc_token`, so the spec has none.  The client keeps its tokens.
- **R4. Q2's weaker iterator state at stage 1?**  Yes.  `it_next`
  borrows only the links it follows (prev links on `n0..nb`, next links
  on `nf..`), as minimality requires, and this is already compatible
  with stage 2's delete-the-current-node (I11).
- **R5. Readable shares for the read-only functions?**  Yes.
  `get_first`, `get_last` and the iterator take any readable share;
  `add` takes a writable one.
- **R6. May `equalto` be a node of the list?**  Yes.  With readable
  shares, the client splits that node's share and lends one part as
  `equalto`.

**Still open (the owner decides):**
- **R2. The comparator state: one per program, or chosen per
  iteration?**
  - The draft makes `Rc : CS -> mpred` a parameter of the whole spec.
  - Per iteration needs dependent funspecs: VST 2.17's `WITH`
    (`NDmk_funspec`) refuses an `mpred` (coqc: universe inconsistency,
    probed during this draft).
  - Should the comparator's postcondition say anything about the new
    state?
- **R7. Parameterisation (Q12).**  The draft is the `dllist` instance.
  Is that acceptable now, with the generic version later?  `README.md`
  says what the generic version would take.
- **R10. How to enforce leak freedom:** (a), (b) or (c) of section 4.
