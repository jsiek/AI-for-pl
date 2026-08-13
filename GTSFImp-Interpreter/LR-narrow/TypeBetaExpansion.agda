module LR-narrow.TypeBetaExpansion where

-- File Charter:
--   * Exposes matching type-beta expansion for related computations.
--   * Exposes the canonical empty atom used for administrative allocation.
--   * Delegates evaluator and trace proofs to the proof namespace.

open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin

open import Types
open import Conversion using (〖_,_↑_〗)
open import CastTerms
import Imprecision
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
import proof.LR-narrow.TypeBetaExpansion as Proof

empty-paired-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ)
  → SemanticAtom (pairedBindCore (core W) Aᴾ Aᴵ) Fin.zero
empty-paired-atom = Proof.empty-paired-atom

paired-step : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
    (fresh : SemanticAtom (pairedBindCore (core W) Aᴾ Aᴵ) Fin.zero)
  → Future W (pairedBindWorld W Aᴾ Aᴵ fresh)
paired-step = Proof.paired-step

related-type-beta-expand : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) Imprecision.⊢ Aᴾ ⊑ Aᴵ}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ}
    {fresh : SemanticAtom (pairedBindCore (core W) Rᴾ Rᴵ) Fin.zero}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)} {k : ℕ}
  → Value Vᴵ
  → Value Vᴾ
  → ComputationsRelated (pairedBindWorld W Rᴾ Rᴵ fresh)
      (FutureValueRelation
        (liftCenterImprecision (paired-step W r fresh) p)) k
      (Vᴵ ↑ 〖 Fin.zero , ⇑ᵗ Rᴵ ↑ Bᴵ 〗)
      (Vᴾ ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ Bᴾ 〗)
  → ComputationsRelated W (FutureValueRelation p) (suc k)
      ((Λ Vᴵ) ⦂∀ Bᴵ [ Rᴵ ]) ((Λ Vᴾ) ⦂∀ Bᴾ [ Rᴾ ])
related-type-beta-expand {W = W} {p = p} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ}
    {r = r} {fresh = fresh} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Vᴾ = Vᴾ} {Vᴵ = Vᴵ} {k = k} =
  Proof.related-type-beta-expand {W = W} {p = p}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {r = r} {fresh = fresh}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Vᴾ = Vᴾ} {Vᴵ = Vᴵ} {k = k}
