module proof.LR-narrow.Lambda where

-- File Charter:
--   * Constructs related lambda computations from their function-elimination
--     obligations.
--   * Builds the related closing substitution needed by a function body.
--   * Derives endpoint typing from cast-term imprecision and closes it under
--     future worlds.
--   * Isolates the remaining beta/body bridge needed by the fundamental case.

open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (n≤1+n; ≤-trans)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; sym)
  renaming (subst to subst≡)

open import Types
open import CastTerms
import Imprecision as I
import proof.DGG.CastTermImprecision2 as CTI
open CTI using (_∣_⊢²_⊑_∶_)
import proof.DGG.CastTermImprecision2Typing as CTIT
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation
open import LR-narrow.ImmediateReturn
import proof.LR-narrow.Closure as ClosureProof

related-function-body-substitution : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁ : TyCtx}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂ : TyCtx}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {k j : ℕ} {Γ : ContextImprecision W₀} {Aᴾ Aᴵ}
    (W₀≼W₁ : Future W₀ W₁) (p : Aᴾ ⊑ᵂ⟨ core W₀ ⟩ Aᴵ)
  → RelatedClosingSubstitutions W₁ k
      (liftContextImprecision W₀≼W₁ Γ)
  → (W₁≼W₂ : Future W₁ W₂)
  → {Uᴵ : Term Δᴵ₂} {Uᴾ : Term Δᴾ₂}
  → suc j ≤ k
  → ValueImprecision W₂
      (liftCenterImprecision W₁≼W₂
        (liftCenterImprecision W₀≼W₁ p)) (suc j) Uᴵ Uᴾ
  → RelatedClosingSubstitutions W₂ j
      (liftContextImprecision (future-trans W₀≼W₁ W₁≼W₂)
        (context-imp Aᴾ Aᴵ p ∷ Γ))
related-function-body-substitution {W₀ = W₀} {W₂ = W₂}
    {j = j} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} W₀≼W₁ p γ W₁≼W₂
    {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} sj≤k argument =
  related-closing-bind W₀≼W₂ p argument-at-index tail
  where
  W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂

  j≤k = ≤-trans (n≤1+n j) sj≤k

  tail = related-closing-trans W₀≼W₁ W₁≼W₂
    (related-closing-future W₁≼W₂
      (related-closing-downward j≤k γ))

  composite = liftCenterImprecision W₀≼W₂ p
  sequential = liftCenterImprecision W₁≼W₂
    (liftCenterImprecision W₀≼W₁ p)

  argument-at-index : ∀ i → i ≤ j →
      ValueImprecision W₂ composite i Uᴵ Uᴾ
  argument-at-index i i≤j =
    ClosureProof.value-imprecision-reindex composite sequential
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂
        (embedPrecise (core W₀) Aᴾ))
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂
        (embedImprecise (core W₀) Aᴵ))
      (value-imprecision-downward-to
        (≤-trans i≤j (n≤1+n j)) argument)

lambda-compatible : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ} {Nᴾ : Term Δᴾ} {Nᴵ : Term Δᴵ}
  → forgetWorld W ∣ (CTI.ctx-imp Aᴾ Aᴵ p ∷ Γ)
      ⊢² Nᴾ ⊑ Nᴵ ∶ q
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′ (compiledContext W Γ)))
      (j : ℕ)
    → j ≤ k
    → FunctionsRelated W′ (liftCenterImprecision W≼W′ p)
        (liftCenterImprecision W≼W′ q) j
        (close (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W≼W′ (ƛ Nᴵ)))
        (close (preciseClosingSubstitution γ)
          (liftPreciseTerm W≼W′ (ƛ Nᴾ))))
  → CompiledTermRelation {W = W} (I.⇒⊑⇒ p q) k Γ
      (ƛ Nᴾ) (ƛ Nᴵ)
lambda-compatible {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {W = W} {k = k} {Γ = Γ} {p = p} {q = q}
    {Nᴾ = Nᴾ} {Nᴵ = Nᴵ} body functions W′ W≼W′ γ =
  related-values-return (imprecise-value endpoints)
    (precise-value endpoints) related
  where
  precise-γ = preciseClosingSubstitution γ
  imprecise-γ = impreciseClosingSubstitution γ

  lambda-imprecision = CTI.ƛ⊑ƛ² body

  precise-lambda-typing = precise-open-typing-future W≼W′
    (CTIT.source-typing² lambda-imprecision)

  precise-lambda-typing′ =
    subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
      (sym (compiled-precise-context-future W≼W′ Γ))
      precise-lambda-typing

  imprecise-lambda-typing = imprecise-open-typing-future W≼W′
    (CTIT.target-typing² lambda-imprecision)

  imprecise-lambda-typing′ =
    subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
      (sym (compiled-imprecise-context-future W≼W′ Γ))
      imprecise-lambda-typing

  endpoints : TypedEndpoints W′
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p q))
      (close imprecise-γ (liftImpreciseTerm W≼W′ (ƛ Nᴵ)))
      (close precise-γ (liftPreciseTerm W≼W′ (ƛ Nᴾ)))
  endpoints = typed-endpoints
    (liftImpreciseTy W≼W′ (Aᴵ ⇒ Bᴵ))
    (liftPreciseTy W≼W′ (Aᴾ ⇒ Bᴾ))
    (embedImprecise-lift W≼W′ (Aᴵ ⇒ Bᴵ))
    (embedPrecise-lift W≼W′ (Aᴾ ⇒ Bᴾ))
    (close-preserves-value imprecise-γ
      (ClosureProof.imprecise-value-future W≼W′ (ƛ Nᴵ)))
    (close-preserves-value precise-γ
      (ClosureProof.precise-value-future W≼W′ (ƛ Nᴾ)))
    (close-preserves-typing imprecise-γ imprecise-lambda-typing′)
    (close-preserves-typing precise-γ precise-lambda-typing′)

  explicit-arrow = I.⇒⊑⇒ (liftCenterImprecision W≼W′ p)
    (liftCenterImprecision W≼W′ q)

  explicit-endpoints : TypedEndpoints W′ explicit-arrow
      (close imprecise-γ (liftImpreciseTerm W≼W′ (ƛ Nᴵ)))
      (close precise-γ (liftPreciseTerm W≼W′ (ƛ Nᴾ)))
  explicit-endpoints = ClosureProof.value-imprecision-reindex
    explicit-arrow (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p q)) {k = zero}
    (sym (liftCenterTy-arrow W≼W′
      (embedPrecise (core W) Aᴾ) (embedPrecise (core W) Bᴾ)))
    (sym (liftCenterTy-arrow W≼W′
      (embedImprecise (core W) Aᴵ) (embedImprecise (core W) Bᴵ)))
    endpoints

  related : ∀ j → j ≤ k →
      FutureValueRelation
        (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p q))
        W′ future-refl j
        (close imprecise-γ (liftImpreciseTerm W≼W′ (ƛ Nᴵ)))
        (close precise-γ (liftPreciseTerm W≼W′ (ƛ Nᴾ)))
  related zero j≤k = endpoints
  related (suc j) j≤k = ClosureProof.value-imprecision-reindex
    (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p q)) explicit-arrow
    (liftCenterTy-arrow W≼W′
      (embedPrecise (core W) Aᴾ) (embedPrecise (core W) Bᴾ))
    (liftCenterTy-arrow W≼W′
      (embedImprecise (core W) Aᴵ) (embedImprecise (core W) Bᴵ))
    (explicit-endpoints ,
      functions W′ W≼W′ γ j (≤-trans (n≤1+n j) j≤k))
