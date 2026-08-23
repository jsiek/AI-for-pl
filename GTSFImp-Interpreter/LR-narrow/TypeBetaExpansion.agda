module LR-narrow.TypeBetaExpansion where

-- File Charter:
--   * Exposes matching and precise-only type-beta expansion.
--   * Exposes paired and precise-only world steps chosen by type application.
--   * Delegates evaluator and trace proofs to the proof namespace.

open import Data.Nat using (ℕ; suc)
import Data.Fin as Fin

open import Types
open import Conversion using (〖_,_↑_〗)
open import CastTerms
import Imprecision
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
import proof.LR-narrow.TypeBetaExpansion as Proof

paired-step : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    (r : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
  → Future W (pairedBindWorld W Aᴾ Aᴵ r)
paired-step = Proof.paired-step

precise-step : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) {Aᴾ : Ty Δᴾ}
    (r★ : impEnv (core W) I.⊢ embedPrecise (core W) Aᴾ ⊑ ★)
  → Future W (preciseBindWorld W Aᴾ r★)
precise-step = Proof.precise-step

related-type-beta-expand : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ}
    {Aᴾ Aᴵ : Ty Δᶜ}
    {p : impEnv (core W) Imprecision.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)} {k : ℕ}
  → Value Vᴵ
  → Value Vᴾ
  → ComputationsRelated (pairedBindWorld W Rᴾ Rᴵ r)
      (FutureValueRelation
        (liftCenterImprecision (paired-step W r) p)) k
      (Vᴵ ↑ 〖 Fin.zero , ⇑ᵗ Rᴵ ↑ Bᴵ 〗)
      (Vᴾ ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ Bᴾ 〗)
  → ComputationsRelated W
      (PostBindValueRelation (paired-step W r) p)
      (suc k)
      ((Λ Vᴵ) ⦂∀ Bᴵ [ Rᴵ ]) ((Λ Vᴾ) ⦂∀ Bᴾ [ Rᴾ ])
related-type-beta-expand {W = W} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ}
    {r = r} {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Vᴾ = Vᴾ} {Vᴵ = Vᴵ} {k = k} =
  Proof.related-type-beta-expand {W = W}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {r = r} {p = p}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Vᴾ = Vᴾ} {Vᴵ = Vᴵ} {k = k}

related-precise-type-beta-expand : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Rᴾ : Ty Δᴾ}
    {r★ : impEnv (core W) I.⊢ embedPrecise (core W) Rᴾ ⊑ ★}
    {Aᴾ Aᴵ : Ty Δᶜ}
    {p : impEnv (core W) Imprecision.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Vᴾ : Term (suc Δᴾ)}
    {Mᴵ : Term Δᴵ} {k : ℕ}
  → Value Vᴾ
  → ComputationsRelated (preciseBindWorld W Rᴾ r★)
      (FutureValueRelation
        (liftCenterImprecision (precise-step W r★) p)) k
      Mᴵ (Vᴾ ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ Bᴾ 〗)
  → ComputationsRelated W
      (PostBindValueRelation (precise-step W r★) p) k
      Mᴵ ((Λ Vᴾ) ⦂∀ Bᴾ [ Rᴾ ])
related-precise-type-beta-expand {W = W} {Rᴾ = Rᴾ}
    {p = p} {Bᴾ = Bᴾ} {Vᴾ = Vᴾ}
    {Mᴵ = Mᴵ} {k = k} =
  Proof.related-precise-type-beta-expand {W = W} {Rᴾ = Rᴾ}
    {p = p} {Bᴾ = Bᴾ} {Vᴾ = Vᴾ}
    {Mᴵ = Mᴵ} {k = k}
