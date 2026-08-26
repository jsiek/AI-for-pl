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
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open import LR-narrow.World
open import LR-narrow.LogicalRelation
open import LR-narrow.TermRelation
open import LR-narrow.ImmediateReturn
import proof.LR-narrow.Closure as ClosureProof

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
constant-values-related zero (κℕ n) {p = I.ι⊑ι} =
  constant-endpoints (κℕ n)
constant-values-related zero (κ𝔹 b) {p = I.ι⊑ι} =
  constant-endpoints (κ𝔹 b)
constant-values-related (suc k) (κℕ n) {p = I.ι⊑ι} =
  constant-endpoints (κℕ n) , same-natural n
constant-values-related (suc k) (κ𝔹 b) {p = I.ι⊑ι} =
  constant-endpoints (κ𝔹 b) , same-boolean b

constant-values-related-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (k : ℕ) (κ : Const)
    {p : constTy {Δᴾ} κ ⊑ᵂ⟨ core W ⟩ constTy {Δᴵ} κ}
  → ValueImprecision W′ (liftCenterImprecision W≼W′ p) k
      ($ κ) ($ κ)
constant-values-related-future W≼W′ k (κℕ n) {p = I.ι⊑ι} =
  ClosureProof.value-imprecision-reindex
    (liftCenterImprecision W≼W′ I.ι⊑ι) I.ι⊑ι
    (liftCenterTy-constant W≼W′ (κℕ n))
    (liftCenterTy-constant W≼W′ (κℕ n))
    (constant-values-related {W = _} k (κℕ n))
constant-values-related-future W≼W′ k (κ𝔹 b) {p = I.ι⊑ι} =
  ClosureProof.value-imprecision-reindex
    (liftCenterImprecision W≼W′ I.ι⊑ι) I.ι⊑ι
    (liftCenterTy-constant W≼W′ (κ𝔹 b))
    (liftCenterTy-constant W≼W′ (κ𝔹 b))
    (constant-values-related {W = _} k (κ𝔹 b))

constant-compatible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)} (κ : Const)
    {p : constTy {Δᴾ} κ ⊑ᵂ⟨ core W ⟩ constTy {Δᴵ} κ}
  → CompiledTermRelation {W = W} p k Γ ($ κ) ($ κ)
constant-compatible {k = k} (κℕ n) {p = I.ι⊑ι} W′ W≼W′ γ
    rewrite liftImpreciseTerm-constant W≼W′ (κℕ n)
          | liftPreciseTerm-constant W≼W′ (κℕ n) =
  related-values-return ($ (κℕ n)) ($ (κℕ n))
    (λ j j≤k → constant-values-related-future W≼W′ j (κℕ n))
constant-compatible {k = k} (κ𝔹 b) {p = I.ι⊑ι} W′ W≼W′ γ
    rewrite liftImpreciseTerm-constant W≼W′ (κ𝔹 b)
          | liftPreciseTerm-constant W≼W′ (κ𝔹 b) =
  related-values-return ($ (κ𝔹 b)) ($ (κ𝔹 b))
    (λ j j≤k → constant-values-related-future W≼W′ j (κ𝔹 b))
