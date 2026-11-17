# sglib DL list: stage-1 VST public spec (plan M6, draft)

The public spec of sglib's doubly linked list for plan M6, stage 1
(`add`, `get_first`, `get_last`, `it_init`, `it_init_on_equal`,
`it_next` and the comparator), drafted for the owner's review, under
the owner's rules of 2026-11-17: the goal is memory safety plus leak
freedom, and public specs are minimal relative to the client survey
(every clause cited in `SPEC.md`).

**Why a new directory.**  `../sglib_spec/` holds the Frama-C/ACSL
template (`sglib_dl_list_spec.h`) and the client survey, both frozen;
VST is the sole backend from M6 on (2026-11-10), so the VST spec gets
its own directory next to it rather than mixing two backends' public
specs.  The name follows `sglib_spec`: the library, then the backend.

## Files

| File | What |
|---|---|
| `SPEC.md` | the English spec: words used, then Requires / Owns afterwards / Ensures per function, each clause with its citation |
| `spec_dllist.v` | the VST funspecs and representation predicates (nodes, link facts, iterator state, comparator contract); `add` in the position-exact form (owner, R9); bodies `Admitted` (type check only) |
| `REVIEW.md` | Coq vs English, the unanchored-postcondition review, the simplicity exceptions with both options, the VST affinity result and leak-freedom enforcement options, and the questions (settled and open) |
| `FIT_CHECK.md` | the 14 covered and 9 stage-1 survey patterns, each with the clauses a client relies on |
| `affine_probe/` | `probe.c`, `verif_probe.v`: VST 2.17 drops owned memory only through `TT` in a postcondition |
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
exactly six `Admitted` (the `semax_body` statements, one per
function, which only check that each funspec fits its function's C
type), and runs the affinity probe.  No
body is proved yet.

## Parameterisation (Q12)

The draft is the `dllist` instance.  Making it generic over the
struct and field names is not cheap enough for a draft:

* a Section over the `compspecs`, the struct's identifier and the two
  link fields' identifiers, with hypotheses that the struct has those
  fields at pointer type;
* `nodes` and the link accessors `nxt` / `prv` rewritten over the
  struct's reptype with `field_at`-style projections for the two links
  (sglib's nodes may have any payload fields), instead of a fixed
  triple, and the comparator's int-payload condition replaced by a
  client-chosen node predicate;
* the iterator struct's type and field names as further parameters
  (sglib names it `struct sglib_<type>_iterator`);
* each client and each body proof instantiates the Section with the
  clightgen output of its own instance.

The English spec is already generic (it names only the two links).
