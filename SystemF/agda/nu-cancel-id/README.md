# νF₁ᶜ — single-entry boundaries with CancelId and Sink

A mechanization of the design in
`../strong-rep-nu/notes/CancelIdSketch.md`, which modifies νF₁
(`../strong-rep-nu/notes/SingleEntrySketch.md`):

* every boundary `[ s , α ] M ⟨ c ⟩` has one scope entry, which reveals
  (`⁺`) or hides (`⁻`) one representation cell `α`;
* terms are typed at NAMED types, each read in its own context; only
  conversions are typed at runtime (representation) types;
* `idᶜ` is untyped, and conversions mention no variables;
* the boundary rules are Id, Cancel-□, CancelId, Sink (a hide moves
  below a seal), Swap (a hide moves below a reveal of another cell) and
  Push (an unseal moves through a reveal of another cell), with no
  Cancel.  This is the second version (the note's §8); the first sank
  reveals too and needed runtime types.

`make check` type-checks `All.agda` with `--safe` and checks for
postulates and holes.

## Files

| file | contents |
|---|---|
| `Types.agda` | `Ty`, one syntax for named and runtime types; renaming |
| `Ctx.agda` | the store, one named flag per cell, name lookup, spelling `Φ ⊢ A ⇝ R`, runtime well-formedness |
| `Terms.agda` | signs, conversions, terms; conversion typing (runtime types) and term typing (named types) |
| `Reduction.agda` | values (`Fun`, `Sealed`), allocation shift, substitution, TyBeta's `_•⟶_`, the step relation, runs |
| `Progress.agda` | the progress theorem (proof in `proof/Progress.agda`) |
| `Preservation.agda` | preservation for a step and for a run (proof in `proof/Preservation.agda`) |
| `TypeSafety.agda` | every term a well-typed term reaches is a value or steps |
| `Examples.agda` | the sketch's 5b and 5c: typed, run (11 and 12 steps), and their results typed by preservation |
| `proof/Types.agda` | renaming congruence and fusion |
| `proof/Flags.agda` | flag update, names, spelling (functional, injective, re-readable with more names), spelling after inserting a cell |
| `proof/Weaken.agda` | typing after inserting an unnamed cell (allocation, `crossΛ`) and after refining an abstract cell (TyBeta) |
| `proof/Subst.agda` | Beta's substitution, with `crossΛ` under `Λ` |

## Representation choices

* **Names are flags.**  Under the sketch's naming condition a
  representation variable keeps one name for its whole life, so a name
  map is determined by which cells are named.  A context is a store plus
  one flag per cell.  A name `X` in an annotation is the `X`-th named
  cell, newest first (`_∋ⁿ_↦_`).  A scope entry sets one flag.  Two
  consequences:
  * well-namedness holds by construction;
  * entries for different cells commute on the nose, so Sink, Swap and
    Push move layers without re-indexing anything.  The positional
    re-indexing in the sketch's §4 is needed only when entries carry
    name positions, as in `strong-rep-nu`.
* **A boundary reads its two types in two contexts.**  `⊢[]` spells the
  interior type with the interior flags and the exterior type with the
  exterior flags, and types the conversion between the two spellings,
  as the paper's `c : ε(Δ)(A) ⇒ Δ(B)`.  Progress needs only that
  spelling is functional.
* **Conversions are typed against the store only.**  They read payloads,
  never flags, so a boundary's conversion is typed at its exterior's
  store, and TyBeta's instantiating conversion keeps its derivation.
  `idᶜ` has no well-formedness premise: every type at a boundary is a
  spelling, so it is well formed already.
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

Done:
* the definitions;
* progress (`proof/Progress.agda`), preservation
  (`proof/Preservation.agda`) and type safety, with `--safe` and no
  postulates;
* examples 5b and 5c, whose every state is typed by preservation.

How preservation goes for the boundary rules:
* **CancelId and Cancel-□**: the two entries restore the exterior flags
  (`setFlag-twice`, `setFlag-idem`), and the body's type and the result
  type spell the same runtime type there, so they are the same named
  type (`⇝-inj`).
* **Sink, Swap and Push**: entries on different cells commute
  (`setFlag-comm`), so the moved body is typed as before.  The moved
  layer needs a named type in its new exterior.  That context has every
  name of the context the type was read in before (`hide-⊆`,
  `reveal-⊆`), so the type can be re-read there (`reread`).
* **TyBeta**: the `Λ`'s abstract cell becomes the allocated cell, with
  its payload (`⊑-⊢`); each layer's entry moves past the new cell.
* **Allocation inside a frame**: the siblings, a ν's conversion and a
  boundary's spellings are weakened by an unnamed cell (`ins-⊢`,
  `ins-conv`, `ins-⇝`); named types do not change.

Next:
1. Determinism.
2. Color preservation, stated over the named flags.
3. The rest of the sketch's examples (5a, 5d, 5e), and an `Eval`.
