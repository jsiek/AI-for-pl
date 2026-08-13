module LR-narrow.UniversalInstantiation where

-- File Charter:
--   * Exposes elimination of structurally related universal values.
--   * Observes matching type applications before their paired allocation.
--   * Requires successful returns to factor through that paired extension.
--   * Delegates existential endpoint-body bookkeeping to the proof module.

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; Σ-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import CastTerms
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
import proof.LR-narrow.UniversalInstantiation as Proof

related-universal-instantiation : ∀
    {Δᴾ Δᴵ Δᶜ} {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ}
    {fresh : SemanticAtom
      (pairedBindCore (core W) Rᴾ Rᴵ) Fin.zero}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑∀ p) (suc k) Vᴵ Vᴾ
  → Σ[ Bᴾ ∈ Ty (suc Δᴾ) ]
    Σ[ Bᴵ ∈ Ty (suc Δᴵ) ]
      (embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Aᴾ)
      × (embedImprecise (core W) (`∀ Bᴵ) ≡ `∀ Aᴵ)
      × ((s : Bᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Bᴵ [ Rᴵ ]ᵗ)
        → let bound = pairedBindWorld W Rᴾ Rᴵ fresh
              step = future-paired (future-refl {W = W}) r fresh
          in ComputationsRelated W (PostBindValueRelation step s)
               (suc k) (Vᴵ ⦂∀ Bᴵ [ Rᴵ ])
                 (Vᴾ ⦂∀ Bᴾ [ Rᴾ ]))
related-universal-instantiation {W = W} {p = p} {r = r}
    {fresh = fresh} {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} =
  Proof.related-universal-instantiation {W = W} {p = p} {r = r}
    {fresh = fresh} {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
