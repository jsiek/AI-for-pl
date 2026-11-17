# sglib DL list: stage-1 VST public spec (plan M6, draft)

The public spec of sglib's doubly linked list for plan M6, stage 1
(`add`, `get_first`, `get_last`, `it_init`, `it_init_on_equal`,
`it_next` and the comparator), drafted for the owner's review.

**Why a new directory.**  `../sglib_spec/` holds the Frama-C/ACSL
template (`sglib_dl_list_spec.h`) and the client survey, both frozen;
VST is the sole backend from M6 on (2026-11-10), so the VST spec gets
its own directory next to it rather than mixing two backends' public
specs.  The name follows `sglib_spec`: the library, then the backend.

## Files

| File | What |
|---|---|
| `SPEC.md` | the English spec: words used, then Requires / Owns afterwards / Ensures per function |
| `spec_dllist.v` | the VST funspecs and representation predicates (whole list, segments, iterator state, comparator contract); bodies `Admitted` (type check only) |
| `REVIEW.md` | where the Coq says more or less than the English, the unanchored-postcondition review, and the owner's open questions (R1–R7) |
| `FIT_CHECK.md` | the 14 covered and 9 stage-1 survey patterns, each with the clauses a client relies on |
| `make_dllist.py` | writes `dllist.c`: B1's `dllist` instance, the six functions verbatim from `../b1/b1_gen.c` |
| `dllist.c` | generated; clightgen turns it into `dllist.v` (not committed) |
| `check.sh` | the compile check (below) |

## Compile check

```
./check.sh
```

regenerates `dllist.c`, runs CompCert 3.18's `clightgen` and Rocq
9.0.1's `coqc` with VST 2.17 (docker image `ariadne-vst:dev`, through
`../../vst/run.sh`), and checks that `spec_dllist.v` compiles with
exactly six `Admitted` (the `semax_body` statements, which only check
that each funspec fits its function's C type).  No body is proved yet.

## Parameterisation (Q12)

The draft is the `dllist` instance.  Making it generic over the
struct and field names is not cheap enough for a draft:

* a Section over the `compspecs`, the struct's identifier and the two
  link fields' identifiers, with hypotheses that the struct has those
  fields at pointer type;
* `cell` rewritten with `field_at` on the two links plus a
  `data_at`-of-the-rest predicate for the payload fields (sglib's nodes
  may have any payload fields), instead of one `data_at` of a fixed
  triple;
* the iterator struct's type and field names as further parameters
  (sglib names it `struct sglib_<type>_iterator`);
* each client and each body proof instantiates the Section with the
  clightgen output of its own instance.

The English spec is already generic (it names only the two links).
