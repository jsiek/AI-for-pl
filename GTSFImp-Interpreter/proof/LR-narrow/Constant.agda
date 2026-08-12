module proof.LR-narrow.Constant where

-- File Charter:
--   * Proves compatibility of identical natural and Boolean constants.
--   * Constructs their typed endpoint and positive-index base observations.
--   * Delegates evaluator reasoning to the immediate-return theorem.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import Primitives
open import CastTerms
import Imprecision as I
import proof.DGG.CastTermImprecision2 as CTI
open import LR-narrow.World
open import LR-narrow.LogicalRelation
open import LR-narrow.TermRelation
open import LR-narrow.ImmediateReturn

constant-endpoints : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (κ : Const)
    {p : constTy {Δᴾ} κ ⊑ᵂ⟨ core W ⟩ constTy {Δᴵ} κ}
  → TypedEndpoints W p ($ κ) ($ κ)
constant-endpoints (κℕ n) {p = I.ι⊑ι} =
  typed-endpoints (‵ `ℕ) (‵ `ℕ) refl refl ($ (κℕ n)) ($ (κℕ n))
    (⊢$ (κℕ n)) (⊢$ (κℕ n))
constant-endpoints (κ𝔹 b) {p = I.ι⊑ι} =
  typed-endpoints (‵ `𝔹) (‵ `𝔹) refl refl
    ($ (κ𝔹 b)) ($ (κ𝔹 b)) (⊢$ (κ𝔹 b)) (⊢$ (κ𝔹 b))

constant-values-related : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (k : ℕ) (κ : Const)
    {p : constTy {Δᴾ} κ ⊑ᵂ⟨ core W ⟩ constTy {Δᴵ} κ}
  → ValueImprecision W p k ($ κ) ($ κ)
constant-values-related zero κ = constant-endpoints κ
constant-values-related (suc k) (κℕ n) {p = I.ι⊑ι} =
  constant-endpoints (κℕ n) , same-natural n
constant-values-related (suc k) (κ𝔹 b) {p = I.ι⊑ι} =
  constant-endpoints (κ𝔹 b) , same-boolean b

constant-compatible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)} (κ : Const)
    {p : constTy {Δᴾ} κ ⊑ᵂ⟨ core W ⟩ constTy {Δᴵ} κ}
  → CompiledTermRelation {W = W} p k Γ ($ κ) ($ κ)
constant-compatible {k = k} κ γ =
  related-values-return ($ κ) ($ κ)
    (λ j j≤k → constant-values-related j κ)
