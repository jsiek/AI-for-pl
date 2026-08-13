M5 `allv-∀` spine fuel bound blocker

Date: 2026-08-13

RESOLVED / DIAGNOSIS RETRACTED (2026-08-13)

The size calculation below is correct, but the claimed recursive call does
not follow from it.  The checked witness `d` is a function consistency, so
`d [ ＇ zero ]ᶜ` is inert and applying it to a value immediately constructs
another value.  `M5AllFuelBoundScratch.agda` now checks both facts.

The live theorem `proof.Consistency.ext-safe` proves the general invariant:

  d : extᵐ ν ⊢ B₀ ∼ B₁
  NonVar B₁
  zero ∈ᵗ B₁
  --------------------------------
  GenSafe d

Thus the `allv-∀` branch exposes a `GenSafe` administration spine.
Function, universal, and generated cases are inert.  Only `safe-inst`
continues with structural value instantiation.  The next surface should
normalize that spine using a combined administration rank; this note no
longer recommends a separate arbitrary-cast fuel.

Blocked step

The first non-Λ package producer must descend through the catalog post

  ((V′ ⦂∀ B₀ [ ＇ zero ]) ⟨ d [ ＇ zero ]ᶜ ⟩) ↑ reveal

before `InstPostCatalogPackageAt.at-spine-descent` can return a value.  Once
the inner type application reaches a value, the intended route applies the
existing extra-cast worker to `d [ ＇ zero ]ᶜ`.

The current package receives only

  c<fuel : castSize ((inst c′) B′≢★) < fuel

and `FuelStepSurface.smaller-extra` can supply the needed worker only after
proving

  suc (castSize (d [ ＇ zero ]ᶜ)) < fuel.

That implication is false.

Checked counterexample

`M5AllFuelBoundScratch.agda` checks the following finite instance at an
empty outer environment:

  B₀ = ＇0 ⇒ `∀ ★
  B₁ = ＇0 ⇒ ★
  B′ = ★ ⇒ ★

  d  : extᵐ μ₀  ⊢ B₀ ∼ B₁
  c′ : instᵐ μ₀ ⊢ B₁ ∼ ⇑ᵗ B′

The stored universal body cast uses identity on the domain and injects
`` `∀ ★ `` into `★` on the codomain.  The instantiation body cast projects
`★` to the bound variable on the domain and is identity on the codomain.
The scratch proves definitionally:

  castSize d = 5
  castSize (d after allocation and fresh-variable opening) = 5
  castSize c′ = 4
  castSize ((inst c′) B′≢★) = 5.

Thus the minimal admitted fuel is `6`:

  castSize ((inst c′) B′≢★) < 6,

but requesting an extra-cast worker for the spine cast would require

  suc (castSize d) < 6,

that is, `6 < 6`.  The scratch contains proofs both that the outer bound
holds and that the spine bound is impossible.

Consequence

The semantic plan already called for descent well-founded on target wrapper
depth, but the live Def surface carries only the residual-column cast fuel.
The four non-Λ producers therefore cannot be implemented by calling
`FuelStepSurface.smaller-extra` from their spine descent.  Adding one fixed
unit of fuel at the public M6 entry is not yet justified: nested target
wrappers can expose further casts, and the current statement does not record
the corresponding decrease.

Recommended next statement

Add a separate, explicit target-spine descent budget (or an equivalent
lexicographic accessibility witness) whose first component decreases when a
target `∀`, `gen`, reveal, or conceal wrapper is peeled and whose second
component uses `castSize` inside an exposed cast.  Keep the existing M6
column fuel for residual casts.  State and check the combined descent surface
before changing `InstInversionPackage` or any proof worker.

No term-imprecision relation change is indicated by this blocker.
