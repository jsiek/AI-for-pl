module proof.PreservationWkImp where

-- File Charter:
--   * Seal-context weakening for PolyConvert imprecision typing.
--   * Proves the `wk-⊑` preservation obligation and a flipped `wk-⊒` helper.
--   * Depends only on the top-level imprecision definition and type
--     well-formedness weakening.

open import Data.Nat using (_≤_)

open import Types
open import proof.TypeProperties using (WfTy-weakenˢ)
open import Imprecision

wk-⊑ :
  ∀ {Ψ Ψ′ Γᵢ p A B} →
  Ψ ≤ Ψ′ →
  Ψ ∣ Γᵢ ⊢ p ⦂ A ⊑ B →
  Ψ′ ∣ Γᵢ ⊢ p ⦂ A ⊑ B
wk-⊑ Ψ≤Ψ′ ⊑-★★ = ⊑-★★
wk-⊑ Ψ≤Ψ′ (⊑-★ν xν) = ⊑-★ν xν
wk-⊑ Ψ≤Ψ′ (⊑-★ g p⊢) = ⊑-★ g (wk-⊑ Ψ≤Ψ′ p⊢)
wk-⊑ Ψ≤Ψ′ (⊑-＇ x∈) = ⊑-＇ x∈
wk-⊑ Ψ≤Ψ′ (⊑-｀ wfα) = ⊑-｀ (WfTy-weakenˢ wfα Ψ≤Ψ′)
wk-⊑ Ψ≤Ψ′ ⊑-‵ = ⊑-‵
wk-⊑ Ψ≤Ψ′ (⊑-⇒ p⊢ q⊢) =
  ⊑-⇒ (wk-⊑ Ψ≤Ψ′ p⊢) (wk-⊑ Ψ≤Ψ′ q⊢)
wk-⊑ Ψ≤Ψ′ (⊑-∀ p⊢) = ⊑-∀ (wk-⊑ Ψ≤Ψ′ p⊢)
wk-⊑ Ψ≤Ψ′ (⊑-ν wfB occ p⊢) =
  ⊑-ν (WfTy-weakenˢ wfB Ψ≤Ψ′) occ (wk-⊑ Ψ≤Ψ′ p⊢)

wk-⊒ :
  ∀ {Ψ Ψ′ Γᵢ p A B} →
  Ψ ≤ Ψ′ →
  Ψ ∣ Γᵢ ⊢ p ⦂ A ⊒ B →
  Ψ′ ∣ Γᵢ ⊢ p ⦂ A ⊒ B
wk-⊒ = wk-⊑
