module
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastIndexBodyViewProof
  where

-- File Charter:
--   * Proves that one-step transport of a source-only polymorphic index
--     produces the corresponding source-only body view.
--   * Preserves the body's imprecision shape through the transported outer
--     `ν` index.
--   * Contains no reduction, catch-up assembly, or term-imprecision
--     construction.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋)
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ν
  )
open import NuReduction using (StoreChange)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)
open import Types using (Ty; TyCtx; `∀; occurs)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; sourceChanges
  ; sourceNuBody
  ; sourceNuIndexEquality
  ; sourceNuOccurs
  ; sourceNuSafe
  ; transportShapeCoherent
  ; transportSourceNu
  ; transportSourceNuType
  ; transportType
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (shape-subst-source)
open import proof.Core.Properties.ReductionProperties using
  (applyTys-∀)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastIndexBodyViewDef
  using
  ( SourceNuCastIndexBodyView
  ; source-nu-cast-index-body-view-reindex
  ; source-only-index-body
  )


private
  ν-shape-injective : ∀ {s t} → νˢ s ≡ νˢ t → s ≡ t
  ν-shape-injective refl = refl


transport-source-nu-cast-index-body-view :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M N′ : Term} {A B C D : Ty} {χ : StoreChange}
    (result : WeakOneStepResult ρ M N′ A B χ)
    (coherence : WeakOneStepTypeCoherence result)
    (safe : NonVar C)
    (occ : occurs zero C ≡ true)
    (q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ) →
  Σ[ body-shape ∈ ImprecisionShape ]
    SourceNuCastIndexBodyView
      (transportSourceNuType result safe occ q) body-shape
    × body-shape ≡ ⌊ q ⌋
transport-source-nu-cast-index-body-view
    {C = C} result coherence safe occ q =
  ⌊ sourceNuBody final-index ⌋ , final-view , body-shape-eq
  where
  final-index = transportSourceNu result safe occ q

  final-view =
    source-nu-cast-index-body-view-reindex
      (sym (sourceNuIndexEquality final-index))
      (source-only-index-body
        {{safe = sourceNuSafe final-index}}
        {occ = sourceNuOccurs final-index}
        (sourceNuBody final-index))

  body-shape-eq =
    ν-shape-injective
      (trans
        (sym (cong ⌊_⌋ (sourceNuIndexEquality final-index)))
        (trans
          (shape-subst-source
            (applyTys-∀ (sourceChanges result) C)
            (transportType result (ν safe occ q)))
          (transportShapeCoherent coherence (ν safe occ q))))
