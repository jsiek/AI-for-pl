# Digest: Siek & Chen, "Parameterized Cast Calculi and Reusable Meta-theory
# for Gradually Typed Lambda Calculi" (JFP 31(e30), 2021) — read 2026-09-04

PDF: `strong/parameterized-cast-calculi-and-reusable-meta-theory-for-gradually-typed-lambda-calculi.pdf`.
Why we read it: Jeremy pointed at it during Decision 6 — reveals/conceals
are analogous to casts, and the paper's ACTIVE/INERT classification is the
principled version of the value-vs-reduction-rule choices we were making ad
hoc.

## The framework (§3, pp. 11–17)

`PreCastStruct` classifies casts `c : A ⇒ B` by two predicates:

- **Inert c** — a cast that, wrapped around a value, FORMS A VALUE
  (`Vcast : Value V → Inert c → Value (V ⟨ c ⟩)`).  Inert casts are
  consumed at their USE sites by decomposition rules:
  `(fun-cast)  V⟨c⟩ · W −→ (V · W⟨dom c⟩)⟨cod c⟩`   (Cross c, Inert c)
  with `dom`/`cod` splitting a cross cast (same head constructor on both
  sides) into its parts.
- **Active c** — a cast that REDUCES when it meetss a value:
  `(cast)  V⟨c⟩ −→ applyCast V c a`   (a : Active c)
  and `V⟨c⟩` with active `c` is NOT a value.

Coherence fields, all used by Progress (Thm 14):
- `ActiveOrInert : ∀ c → Active c ⊎ Inert c` (total classification);
- `InertCross→ : (c : A ⇒ B→C) → Inert c → Cross c × (A ≡ A₁→A₂)` — an
  inert cast at a FUNCTION target must be decomposable (plus ×/+ analogs);
- `baseNotInert : (c : A ⇒ b) → ¬ Inert c` — a cast to a BASE type is
  never inert (so canonical forms at base type are constants);
- `applyCast` (in `CastStruct`) must be defined (total) on all active
  casts applied to values.

The incoherent combinations Jeremy named are violations of these fields:
a function-target cast that is a value WITHOUT (fun-cast) breaks Progress
via InertCross→; (fun-cast) on a cast that is NOT a value overlaps with
(cast)/ξ and breaks determinism.  Eight instantiations in §5/§7 differ
exactly in where they draw Active/Inert (e.g. eager calculi make
function-to-function casts active — applyCast eta-expands; lazy calculi
make them inert and rely on (fun-cast)).

## The mapping to strong/ boundaries

| paper | strong/ |
|---|---|
| cast `c : A ⇒ B` | boundary `⟪ Θ , B₀ ⟫`; source = `substᵗ (γᵇ Θ) B₀`, target = `substᵗ (ρᵇ Θ) B₀` (ours also moves the CONTEXT: `intOf Δ Θ` — a generalization the paper's casts don't need) |
| `V⟨c⟩` value former (their fig. 9 "wrap" variant) | `V ⟪ Θ , B₀ ⟫`, `V-⟪⟫` |
| `(fun-cast)` with `dom`/`cod` | **Peel**: `dom c = ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫`, `cod c = ⟪ Θ , B₂ ⟫` |
| `Cross c` at → | the face is SYNTACTICALLY `B₁ ⇒ B₂` (decomposable) |
| ∀-target analog | TyWrap (Λ body) / TyPeel (wrapper body) |
| `(cast)`/`applyCast` on actives | the collapse steps: merge of a variable-faced nesting; dropping an identity-faced boundary |
| `Vcast` requires `Inert` | THE MISSING DISCIPLINE: our `V-⟪⟫` takes any face — which is how Merge/Drop∅ became value-LHS rules and broke determinism (§9j, §9k) |
| `ActiveOrInert` total | Progress's wrapper case analysis |
| `InertCross→` | "an inert boundary at a function-type target has a syntactic ⇒ face" — the lemma that variable-faced-with-arrow-reading wrappers must be ACTIVE |
| `baseNotInert` | a boundary whose face is a base type is never inert (its two faces are equal — droppable) |
| `applyCast` totality | THE CRUX LEMMA: MergeOK derivable at every well-typed variable-faced nesting (three instances already discharged: a-/p-/e-MergeOK, CancelProbe) |

## What the framework decides for Decision 6

Classify a wrapper by its SYNTACTIC face B₀ (+ slot kind — all decidable):
- `B₁ ⇒ B₂` / `∀ B` face: **inert** (cross) — value; eliminated by
  Peel/TyWrap/TyPeel.  (§9d's cx nesting: inert, peeled at use — never
  needs merging.)
- `` ` X `` face, X a REVEAL slot of Θ (ρ reads it to the rep): **active**
  — applyCast = the collapse (Merge's action on the top pair); not a
  value.  The rv families α/β1/β2 live here, and all three probe
  instances carry fully discharged MergeOK.
- `` ` X `` face, X a CONCEAL slot or ambient (ρ reads it to an abstract
  variable): **inert** — the sealed values (`5 ⟪ ↓X:=ℕ , X ⟫`); no
  elimination exists or is needed (an abstract-typed term cannot be
  eliminated — applications require a syntactic arrow).
- base face (`ℕ`/`𝔹`): **active** — the two faces are identical; drop the
  boundary (this also collapses the residual `3 ⟪ ↑W:=ℕ , ℕ ⟫` towers
  from peel runs to bare numerals) — our `baseNotInert`.
- `Θ ≡ ∅` needs no special case: classified by its face like any other.

Determinism comes out FOR FREE: active wrappers are not values, so the
(cast)-style rules never fire on a value; Peel requires the syntactic ⇒
face (inert) and is disjoint from everything; values-don't-step and `det`
become provable.  The standalone-vs-folded debate DISSOLVES: standalone
collapse rules are fine once `V-⟪⟫` requires Inert — Jeremy's face-type
restriction was the right instinct, and `Vcast`-requires-`Inert` is the
missing half that §9k demanded.

Obligations the install must discharge (the paper's coherence fields):
1. ActiveOrInert: the classification is total + decidable (syntactic).
2. InertCross→/∀ analogs: a well-typed inert wrapper eliminated at ⇒/∀
   has the syntactic face (typing gives this: `⊢·` needs a syntactic
   arrow; the variable-faced arrow-reading wrappers are active by the
   classification).
3. applyCast totality on actives = the MergeOK-derivability lemma at
   well-typed variable-faced nestings (+ the trivial base/∅ drops); plus
   "active single variable-faced wrapper with non-wrapper body is
   untypeable" (canon-var / no-abstract-value territory).
4. det + values-don't-step, now provable.
