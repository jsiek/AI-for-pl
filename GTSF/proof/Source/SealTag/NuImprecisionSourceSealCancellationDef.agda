module proof.Source.SealTag.NuImprecisionSourceSealCancellationDef where

-- File Charter:
--   * Defines exact-world cancellation of a terminal source seal.
--   * Exposes world coherence and source-store well-formedness explicitly.
--   * Contains no implementation or simulation dependency.

open import Coercions using (seal)
open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ)
open import NuTerms using
  (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyVar; ＇_)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


SourceSealCancellationᵀ : Set₁
SourceSealCancellationᵀ =
  ∀ {Φ Δᴸ Δᴿ} {V W : Term} {B X Y : Ty} {α : TyVar}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ ＇ α ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  Value V →
  Value W →
  No• W →
  (α , X) ∈ leftStoreⁱ ρ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⟨ seal Y α ⟩ ⊑ W ⦂ ＇ α ⊑ B ∶ p →
  (q : Φ ∣ Δᴸ ⊢ X ⊑ B ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ X ⊑ B ∶ q
