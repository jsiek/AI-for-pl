module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootDef
  where

-- File Charter:
--   * Defines ordinary world-coherent resumption of the eager target
--     `fun-untag-gen` narrowing root.
--   * Matches the corresponding active-root record field and returns the
--     existing complete catch-up carrier directly.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import CastImprecisionShape using (narrowing; _⊢ᶜ_⦂_)
open import Coercions using
  (Coercion; ModeEnv; gen; _？; _︔_)
open import Data.List using ([])
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; ★; _⇒_; `∀)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightTargetNarrowFunUntagGenRootᵀ : Set₁
WorldCoherentRightTargetNarrowFunUntagGenRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A C : Ty} {s : Coercion} {μ : ModeEnv}
    {sequence-shape untag-shape gen-shape : ImprecisionShape}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK
    (M′ ⟨ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s ⟩) →
  Value V →
  No• V →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s ∶ ★ ⊒ `∀ C →
  narrowing ⊢ᶜ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s
    ⦂ sequence-shape →
  ⌊ q ⌋ ； sequence-shape ≋ ⌊ p ⌋ →
  narrowing ⊢ᶜ (★ ⇒ ★) ？ ⦂ untag-shape →
  ⌊ r ⌋ ； untag-shape ≋ ⌊ p ⌋ →
  narrowing ⊢ᶜ gen (★ ⇒ ★) s ⦂ gen-shape →
  ⌊ q ⌋ ； gen-shape ≋ ⌊ r ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ ★ ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V}
    {M′ = M′ ⟨ ((★ ⇒ ★) ？) ︔ gen (★ ⇒ ★) s ⟩}
    {ρ = ρ⁺} q
