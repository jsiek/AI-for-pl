NS-4 stage 1j opened-target endpoints
======================================

Status
------

Tripwire fired during the statement-first direct route.  No live Agda code was
changed for this route.


Endpoint statements
-------------------

The strict target-head cases need target-universal opening for an arbitrary
source endpoint `Aₛ : Ty Δᴸ`.

For a parent witness

`p : Aₛ ⊑ᵂ⟨ W ⟩ `∀ B`

and the right-only fresh bind produced by the peel

`ins : TargetInsert wk↪ᵗ π W W₁`

with

`follows : targetStoreʷ W₁ ≡ applyStores (bind (＇ X) ∷ []) (targetStoreʷ W)`

the required endpoints are:

1. `opened-target-cast`

   `Aₛ ⊑ᵂ⟨ W ⟩ C [ ＇ X ]ᵗ`

   for `allv-∀` when the target constructor carries
   `d : extᵐ μ ⊢ B ∼ C`.

2. `opened-target-inner`

   `Aₛ ⊑ᵂ⟨ W₁ ⟩ B`

   for `allv-reveal` and `allv-conceal`.

3. `opened-target-final`

   `Aₛ ⊑ᵂ⟨ W₁ ⟩ replaceTy zero (⇑ᵗ (＇ X)) B`

   for the generated reveal frame in `allv-reveal` and `allv-conceal`.


Direct route case table and failure
-----------------------------------

The relation at `Aₛ ⊑ᵂ⟨ W ⟩ `∀ B` expands to

`impEnvʷ W ⊢ embedᴸ W Aₛ ⊑ embedᴿ W (`∀ B)`.

The constructors whose right endpoint can be a universal are:

- matched `∀⊑∀`, with source shape `embedᴸ W Aₛ = `∀ A`.
  This is the tripwire case.

- source-only `∀⊑`, when its arbitrary right endpoint is itself universal.
  This also descends through a source universal and therefore has the same
  opened-target-only shape as the matched case.

- `bot-elim`, with source shape `embedᴸ W Aₛ = `∀ (＇ zero)` and target shape
  `embedᴿ W (`∀ B) = `∀ ★`.  This case cannot produce the requested
  arbitrary opened endpoint either; it only explains a universal-to-dynamic
  or universal-to-`∀ ★` boundary.

The minimal failing matched witness is:

`Aₛ = `∀ (＇ zero)`

`B = ＇ zero`

`p = ∀⊑∀ X⊑X : Aₛ ⊑ᵂ⟨ W ⟩ `∀ B`

For `q₁`, after a right-only bind by `＇ X`, the wanted endpoint is:

`q₁ : `∀ (＇ zero) ⊑ᵂ⟨ W₁ ⟩ ＇ zero`

The only possible constructor is the source-only opening rule `∀⊑`.  Its
premise must have the shape:

`instᵐ (impEnvʷ W₁) ⊢ ＇ zero ⊑ ⇑ᵗ (＇ zero)`

which reduces to:

`instᵐ (impEnvʷ W₁) ⊢ ＇ zero ⊑ ＇ (suc zero)`.

The only variable-to-variable imprecision constructor is `X⊑X`, so this would
require:

`zero ≡ suc zero`

or an equivalent shared-center/source-side opening fact.  The strict peel only
provides a right-only target extension:

`impEnvʷ W₁ = instᵐ (impEnvʷ W)` at the canonical bind,

so the fresh center has mark `X⊑★`, not the precise `X⊑X` mark or shared
source/target binder split needed to replay the matched premise.

The same obstruction appears for the other endpoint conclusions:

- `qCast : `∀ (＇ zero) ⊑ᵂ⟨ W ⟩ (＇ zero) [ ＇ X ]ᵗ`
  needs the `∀⊑` premise
  `instᵐ (impEnvʷ W) ⊢ ＇ zero ⊑ ⇑ᵗ (＇ X)`.
- `q₂ : `∀ (＇ zero) ⊑ᵂ⟨ W₁ ⟩ replaceTy zero (⇑ᵗ (＇ X)) (＇ zero)`
  needs the `∀⊑` premise
  `instᵐ (impEnvʷ W₁) ⊢ ＇ zero ⊑ ⇑ᵗ (⇑ᵗ (＇ X))`.

Both reduce to a source binder variable on the left and a shifted target
runtime variable on the right, so neither can be built from the right-only
bind facts.


Tripwire watch
--------------

The direct route must not require any of the following:

- a precise fresh mark `X⊑X` for the right-only bind;
- a shared fresh center split;
- reversing a source-side OPE.

The failing constructor case is the matched `∀⊑∀` parent witness above.  The
mark arithmetic requires a precise/shared fresh variable relation, while the
right-only bind provides only the fresh dynamic mark:

`instᵐ μ zero = X⊑★`.


SUPERSEDED-BY-VIEW-DISPATCH postscript, 2026-08-14
--------------------------------------------------

This tripwire is not resolved by a stronger generic opened-endpoint theorem.
The generic route is abandoned.

The replacement surface is view-dispatched: the opened obligations are now
owned by the source/target derivation core for each strict target head.  The
checked contract module is:

`GTSFImp/proof/DGG/Catchup/StructuralStrictViewSurfaceDef.agda`

It states one child-continuation surface per strict target family:

- `StructuralΛStrictSurfaceᵀ`
- `StructuralAllCastStrictSurfaceᵀ`
- `StructuralGenStrictSurfaceᵀ`
- `StructuralRevealStrictSurfaceᵀ`
- `StructuralConcealStrictSurfaceᵀ`

Each surface receives the parent relation core, the caller's post-plan and
target-frame chain, and the peeled child target package.  It returns the child
endpoint, child post-plan, child relation, and child chain that the worker
needs.  The missing precise/shared mark is therefore no longer requested from
bare type-level endpoint data.
