module proof.NuCore.Relations.NuImprecisionMatchedLiftInvariantsDef where

-- File Charter:
--   * Defines preservation of the three exact-world invariants across a
--     matched store lift.
--   * Exposes coherence, source-name exclusivity, and left-store Wf together.
--   * Contains no implementation, postulate, hole, permissive option, term
--     imprecision, or simulation import.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_)

open import Imprecision using (_ˣ⊑ˣ_; ⇑ᵢ)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


MatchedLiftInvariantsᵀ : Set₁
MatchedLiftInvariantsᵀ =
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  WorldCoherent ρ′ ×
  SourceNameExclusive ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ×
  StoreWf (suc Δᴸ) (leftStoreⁱ ρ′)
