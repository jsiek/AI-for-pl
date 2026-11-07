# νF₁ᶜ — single-entry boundaries with CancelId and Sink

A mechanization of the design in
`../strong-rep-nu/notes/CancelIdSketch.md`, which modifies νF₁
(`../strong-rep-nu/notes/SingleEntrySketch.md`):

* every boundary `[ s , α ] M ⟨ c ⟩` has one scope entry, which reveals
  (`⁺`) or hides (`⁻`) one representation cell `α`;
* terms are typed at runtime (representation) types, and named types
  appear only in annotations;
* `idᶜ` is untyped, and conversions mention no variables;
* the boundary rules are Id, Cancel-□, CancelId and Sink, with no
  Cancel.

`make check` type-checks `All.agda` with `--safe` and checks for
postulates and holes.

## Files

| file | contents |
|---|---|
| `Types.agda` | `Ty`, one syntax for named and runtime types; renaming |
| `Ctx.agda` | the store, one named flag per cell, name lookup, spelling `Φ ⊢ A ⇝ R`, runtime well-formedness |
| `Terms.agda` | signs, conversions, terms; conversion and term typing |
| `Reduction.agda` | values (`Fun`, `Sealed`), allocation shift, substitution, TyBeta's `_•⟶_`, the step relation, runs |
| `Progress.agda` | the progress theorem (proof in `proof/Progress.agda`) |
| `Examples.agda` | the sketch's 5c: typed, and run to `3` in 12 steps |

## Representation choices

* **Names are flags.**  Under the sketch's naming condition a
  representation variable keeps one name for its whole life, so a name
  map is determined by which cells are named.  A context is a store plus
  one flag per cell.  A name `X` in an annotation is the `X`-th named
  cell, newest first (`_∋ⁿ_↦_`).  A scope entry sets one flag.  Two
  consequences:
  * well-namedness holds by construction;
  * entries for different cells commute on the nose, so Sink moves its
    layer without re-indexing anything.  The positional re-indexing in
    the sketch's §4 is needed only when entries carry name positions,
    as in `strong-rep-nu`.
* **Conversions are typed against the store only.**  They read payloads,
  never flags, so a boundary's conversion is typed at its exterior's
  store, and TyBeta's instantiating conversion keeps its derivation.
* **`Λ N` is a value for every body**, with no reduction under `Λ`.
  The sketch writes `ΛX. V`; this changes nothing in the progress
  argument.
* **Beta under `Λ`.**  A copy of the argument that crosses a `Λ` is
  wrapped in `[ ⁻ , 0 ] … ⟨ idᶜ ⟩`, `strong-rep-nu`'s `crossΛᴹ`, so its
  holes keep their scope map.  In 5c this adds one Sink and one Id to
  the sketch's trace.
* **No primitive operators yet**: only `ℕ` and `𝔹` constants, so there
  is no Delta rule.

## Status

Done: the definitions, progress (`proof/Progress.agda`), and example 5c.

Next:

1. Preservation: substitution and allocation-weakening lemmas, flag
   commutation for Sink, and the refinement lemma for TyBeta
   (abstract `Λ` cell to payload).
2. Determinism.
3. Color preservation, stated over the named flags.
4. The rest of the sketch's examples (5a, 5b, 5d, 5e), and an `Eval`.
