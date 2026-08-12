module LR-narrow.Examples.Cambridge26.CheckedNarrowing where

-- File Charter:
--   * Checks an explicitly supplied coercion against both endpoint types.
--   * Pairs the resulting coercion typing with an explicit `Narrowing` shape.
--   * Keeps the Cambridge rendition independent of coercion compilation and
--     therefore of every small-step reduction module.

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary using (yes; no)

open import Coercions using
  (Coercion; ModeEnv; id-onlyᵈ; _∣_∣_⊢_∶_=⇒_)
open import NarrowWiden using (Narrowing; _∣_∣_⊢_∶_⊒_)
open import TypeCheck using
  (IsJust; coercion-checkᵐ; fromJust)
open import Types using (Store; Ty; TyCtx; _≟Ty_)

coercion-check-expectᵐ :
    (μ : ModeEnv)
  → (Δ : TyCtx)
  → (Σ : Store)
  → (c : Coercion)
  → (A B : Ty)
  → Maybe (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B)
coercion-check-expectᵐ μ Δ Σ c A B with coercion-checkᵐ μ Δ Σ c
coercion-check-expectᵐ μ Δ Σ c A B | nothing = nothing
coercion-check-expectᵐ μ Δ Σ c A B | just (A′ , B′ , c⊢)
    with A ≟Ty A′ | B ≟Ty B′
coercion-check-expectᵐ μ Δ Σ c A B | just (A′ , B′ , c⊢)
    | yes A≡A′ | yes B≡B′ =
  just
    (subst (λ B₀ → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B₀) (sym B≡B′)
      (subst (λ A₀ → μ ∣ Δ ∣ Σ ⊢ c ∶ A₀ =⇒ B′)
        (sym A≡A′) c⊢))
coercion-check-expectᵐ μ Δ Σ c A B | just (A′ , B′ , c⊢)
    | yes A≡A′ | no B≢B′ = nothing
coercion-check-expectᵐ μ Δ Σ c A B | just (A′ , B′ , c⊢)
    | no A≢A′ | yes B≡B′ = nothing
coercion-check-expectᵐ μ Δ Σ c A B | just (A′ , B′ , c⊢)
    | no A≢A′ | no B≢B′ = nothing

checked-narrowing : ∀ {c A B}
  → (shape : Narrowing c)
  → IsJust (coercion-check-expectᵐ id-onlyᵈ zero [] c A B)
  → id-onlyᵈ ∣ zero ∣ [] ⊢ c ∶ A ⊒ B
checked-narrowing {c} {A} {B} shape checked =
  fromJust (coercion-check-expectᵐ id-onlyᵈ zero [] c A B) checked ,
  shape
