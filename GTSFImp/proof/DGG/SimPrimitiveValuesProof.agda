module proof.DGG.SimPrimitiveValuesProof where

-- File Charter:
--   * Proves value/value simulation for primitive delta reduction.
--   * Uses canonical forms and term-imprecision inversion to identify both
--     target operands with their related source constants.
--   * Performs the matching target delta step with synchronized keep changes.

open import Primitives using (κℕ; κ𝔹; δ-add; δ-and)
open import CastTerms using ($; _⊕[_]_)
open import Reduction
  using
    ( keep
    ; pure-step
    ; δ-⊕
    ; _—→[_]⟨_⟩_
    ; _∎[]
    )
  renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
open import proof.DGG.Parked.ParkedWorldDef
  using
    ( evolve-refl
    ; evolve-keepᴸ
    ; evolve-keepᴿ
    )
open import proof.DGG.SimPrimitiveValuesDef
  using (SimPrimitiveValuesᵀ)
open import proof.TypeSafety.Progress
  using
    ( canonical-ℕ
    ; canonical-𝔹
    ; nv-const
    ; bv-const
    )


sim-primitive-values : SimPrimitiveValuesᵀ
sim-primitive-values parked L⊑V′ M⊑M′ r vV′ vM′ δ-add
    with canonical-ℕ vV′ (CTI2T.target-typing² L⊑V′)
       | canonical-ℕ vM′ (CTI2T.target-typing² M⊑M′)
sim-primitive-values parked L⊑V′ M⊑M′ r vV′ vM′ δ-add
    | nv-const refl | nv-const refl
    with L⊑V′ | M⊑M′
sim-primitive-values parked L⊑V′ M⊑M′ r vV′ vM′ δ-add
    | nv-const refl | nv-const refl
    | CTI2.κ⊑κ² ._ p | CTI2.κ⊑κ² ._ q =
  _ , keep ∷ˢ []ˢ , _ , _ , _ , r ,
  $ _ ⊕[ _ ] $ _
    —→[ keep ]⟨ pure-step (δ-⊕ δ-add) ⟩
  $ _ ∎[] ,
  evolve-keepᴸ (evolve-keepᴿ evolve-refl) ,
  CTI2.κ⊑κ² _ r
sim-primitive-values parked L⊑V′ M⊑M′ r vV′ vM′ δ-and
    with canonical-𝔹 vV′ (CTI2T.target-typing² L⊑V′)
       | canonical-𝔹 vM′ (CTI2T.target-typing² M⊑M′)
sim-primitive-values parked L⊑V′ M⊑M′ r vV′ vM′ δ-and
    | bv-const refl | bv-const refl
    with L⊑V′ | M⊑M′
sim-primitive-values parked L⊑V′ M⊑M′ r vV′ vM′ δ-and
    | bv-const refl | bv-const refl
    | CTI2.κ⊑κ² ._ p | CTI2.κ⊑κ² ._ q =
  _ , keep ∷ˢ []ˢ , _ , _ , _ , r ,
  $ _ ⊕[ _ ] $ _
    —→[ keep ]⟨ pure-step (δ-⊕ δ-and) ⟩
  $ _ ∎[] ,
  evolve-keepᴸ (evolve-keepᴿ evolve-refl) ,
  CTI2.κ⊑κ² _ r
