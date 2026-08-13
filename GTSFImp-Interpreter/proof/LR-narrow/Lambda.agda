module proof.LR-narrow.Lambda where

-- File Charter:
--   * Constructs related lambda computations from their function-elimination
--     obligations.
--   * Builds the related closing substitution needed by a function body.
--   * Derives endpoint typing from cast-term imprecision and closes it under
--     future worlds.
--   * Completes the beta/body bridge and body-driven lambda introduction.

open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤-trans)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
  renaming (subst to subst≡)

open import Types
open import CastTerms
open import proof.TermInTermSubst using (subst-cong)
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
import proof.LR-narrow.ClosingSubstitution as ClosingProof
open import proof.LR-narrow.BetaExpansion using (related-beta-expand)

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

functions-related-from-body : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ} {Nᴾ : Term Δᴾ} {Nᴵ : Term Δᴵ}
  → (∀ i → i ≤ k → CompiledTermRelation {W = W} q i
      (CTI.ctx-imp Aᴾ Aᴵ p ∷ Γ) Nᴾ Nᴵ)
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
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
        (liftPreciseTerm W≼W′ (ƛ Nᴾ)))
functions-related-from-body body-related W≼W′ γ zero j≤k = tt
functions-related-from-body {W = W} {k} {Γ} {p} {q} {Nᴾ} {Nᴵ}
    body-related {W′ = W′} W≼W′ γ (suc j) sj≤k = head , tail
  where
  j≤k = ≤-trans (n≤1+n j) sj≤k

  tail = functions-related-from-body body-related W≼W′ γ j j≤k

  head : ∀ {Δᴾ″ Δᴵ″ Δᶜ″}
      (W″ : World Δᴾ″ Δᴵ″ Δᶜ″)
      (W′≼W″ : Future W′ W″)
      {Uᴵ : Term Δᴵ″} {Uᴾ : Term Δᴾ″}
    → ValueImprecision W″
        (liftCenterImprecision W′≼W″
          (liftCenterImprecision W≼W′ p)) (suc j) Uᴵ Uᴾ
    → ComputationsRelated W″
        (FutureValueRelation
          (liftCenterImprecision W′≼W″
            (liftCenterImprecision W≼W′ q))) (suc j)
        (liftImpreciseTerm W′≼W″
          (close (impreciseClosingSubstitution γ)
            (liftImpreciseTerm W≼W′ (ƛ Nᴵ))) · Uᴵ)
        (liftPreciseTerm W′≼W″
          (close (preciseClosingSubstitution γ)
            (liftPreciseTerm W≼W′ (ƛ Nᴾ))) · Uᴾ)
  head W″ W′≼W″ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument =
    ClosureProof.computations-related-reindex q-composite q-sequential
      (liftCenterTy-trans W≼W′ W′≼W″
        (embedPrecise (core W) _))
      (liftCenterTy-trans W≼W′ W′≼W″
        (embedImprecise (core W) _))
      (cong (λ F → F · Uᴵ) (sym imprecise-lambda-eq))
      (cong (λ F → F · Uᴾ) (sym precise-lambda-eq))
      (related-beta-expand vUᴵ vUᴾ body-contracta)
    where
    W≼W″ = future-trans W≼W′ W′≼W″

    p-composite = liftCenterImprecision W≼W″ p
    p-sequential = liftCenterImprecision W′≼W″
      (liftCenterImprecision W≼W′ p)
    p-local = liftLocalImprecision W≼W″ p

    q-composite = liftCenterImprecision W≼W″ q
    q-sequential = liftCenterImprecision W′≼W″
      (liftCenterImprecision W≼W′ q)

    argument-at-index : ∀ i → i ≤ j →
        ValueImprecision W″ p-composite i Uᴵ Uᴾ
    argument-at-index i i≤j =
      ClosureProof.value-imprecision-reindex p-composite p-sequential
        (liftCenterTy-trans W≼W′ W′≼W″
          (embedPrecise (core W) _))
        (liftCenterTy-trans W≼W′ W′≼W″
          (embedImprecise (core W) _))
        (value-imprecision-downward-to
          (≤-trans i≤j (n≤1+n j)) argument)

    γ-down = related-closing-downward j≤k γ
    γ-future = related-closing-future W′≼W″ γ-down
    γ-tail = related-closing-trans W≼W′ W′≼W″ γ-future

    γ-body = related-function-body-substitution W≼W′ p γ W′≼W″
      sj≤k argument

    γᴵ-tail = impreciseClosingSubstitution γ-tail
    γᴾ-tail = preciseClosingSubstitution γ-tail

    γᴵ-body = impreciseClosingSubstitution γ-body
    γᴾ-body = preciseClosingSubstitution γ-body

    argument-at-j = argument-at-index j ≤-refl
    argument-local-at-j = ClosureProof.value-imprecision-center→local
      W≼W″ p argument-at-j
    argument-endpoints = value-imprecision-endpoints
      {Aᴾ = embedPrecise (core W″) (liftPreciseTy W≼W″ _)}
      {Aᴵ = embedImprecise (core W″) (liftImpreciseTy W≼W″ _)}
      {W = W″} {p = p-local} argument-local-at-j
    vUᴵ = imprecise-value argument-endpoints
    vUᴾ = precise-value argument-endpoints
    Uᴵ⊢ = imprecise-endpoint-typing
      {Aᴾ = liftPreciseTy W≼W″ _} {Aᴵ = liftImpreciseTy W≼W″ _}
      {W = W″} {p = p-local} argument-local-at-j
    Uᴾ⊢ = precise-endpoint-typing
      {Aᴾ = liftPreciseTy W≼W″ _} {Aᴵ = liftImpreciseTy W≼W″ _}
      {W = W″} {p = p-local} argument-local-at-j

    bodyᴵ = CastTerms.subst (exts (closingSubstitution γᴵ-tail))
      (liftImpreciseTerm W≼W″ Nᴵ)
    bodyᴾ = CastTerms.subst (exts (closingSubstitution γᴾ-tail))
      (liftPreciseTerm W≼W″ Nᴾ)

    imprecise-contract-eq : close γᴵ-body
        (liftImpreciseTerm W≼W″ Nᴵ) ≡ bodyᴵ [ Uᴵ ]
    imprecise-contract-eq = sym (beta-close-cons
      {V = Uᴵ} {N = liftImpreciseTerm W≼W″ Nᴵ}
      vUᴵ Uᴵ⊢ γᴵ-tail)

    precise-contract-eq : close γᴾ-body
        (liftPreciseTerm W≼W″ Nᴾ) ≡ bodyᴾ [ Uᴾ ]
    precise-contract-eq = sym (beta-close-cons
      {V = Uᴾ} {N = liftPreciseTerm W≼W″ Nᴾ}
      vUᴾ Uᴾ⊢ γᴾ-tail)

    body-related-at-j = body-related j j≤k W″ W≼W″ γ-body

    body-contracta = ClosureProof.computations-related-reindex
      q-composite q-composite refl refl imprecise-contract-eq
      precise-contract-eq body-related-at-j

    imprecise-tail-env-eq : ∀ x →
        closingSubstitution (imprecise-closing-future W′≼W″
          (impreciseClosingSubstitution γ)) x
        ≡ closingSubstitution γᴵ-tail x
    imprecise-tail-env-eq x =
      trans
        (ClosingProof.imprecise-closing-future-lookup W′≼W″
          (impreciseClosingSubstitution γ) x)
        (sym (trans
          (ClosingProof.imprecise-related-trans-lookup
            W≼W′ W′≼W″ γ-future x)
          (trans
            (ClosingProof.imprecise-related-future-lookup
              W′≼W″ γ-down x)
            (cong (liftImpreciseTerm W′≼W″)
              (ClosingProof.imprecise-related-downward-lookup
                j≤k γ x)))))

    precise-tail-env-eq : ∀ x →
        closingSubstitution (precise-closing-future W′≼W″
          (preciseClosingSubstitution γ)) x
        ≡ closingSubstitution γᴾ-tail x
    precise-tail-env-eq x =
      trans
        (ClosingProof.precise-closing-future-lookup W′≼W″
          (preciseClosingSubstitution γ) x)
        (sym (trans
          (ClosingProof.precise-related-trans-lookup
            W≼W′ W′≼W″ γ-future x)
          (trans
            (ClosingProof.precise-related-future-lookup
              W′≼W″ γ-down x)
            (cong (liftPreciseTerm W′≼W″)
              (ClosingProof.precise-related-downward-lookup
                j≤k γ x)))))

    imprecise-lift-lambda : liftImpreciseTerm W≼W″ (ƛ Nᴵ)
      ≡ ƛ liftImpreciseTerm W≼W″ Nᴵ
    imprecise-lift-lambda = liftImpreciseTerm-lambda W≼W″ Nᴵ

    precise-lift-lambda : liftPreciseTerm W≼W″ (ƛ Nᴾ)
      ≡ ƛ liftPreciseTerm W≼W″ Nᴾ
    precise-lift-lambda = liftPreciseTerm-lambda W≼W″ Nᴾ

    imprecise-lambda-close : close γᴵ-tail
        (liftImpreciseTerm W≼W″ (ƛ Nᴵ)) ≡ ƛ bodyᴵ
    imprecise-lambda-close rewrite imprecise-lift-lambda = refl

    precise-lambda-close : close γᴾ-tail
        (liftPreciseTerm W≼W″ (ƛ Nᴾ)) ≡ ƛ bodyᴾ
    precise-lambda-close rewrite precise-lift-lambda = refl

    imprecise-lambda-eq : liftImpreciseTerm W′≼W″
        (close (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W≼W′ (ƛ Nᴵ))) ≡ ƛ bodyᴵ
    imprecise-lambda-eq =
      trans
        (imprecise-close-future W′≼W″
          (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W≼W′ (ƛ Nᴵ)))
        (trans
          (cong (close (imprecise-closing-future W′≼W″
            (impreciseClosingSubstitution γ)))
            (sym (liftImpreciseTerm-trans W≼W′ W′≼W″ (ƛ Nᴵ))))
          (trans
            (subst-cong imprecise-tail-env-eq
              (liftImpreciseTerm W≼W″ (ƛ Nᴵ)))
            imprecise-lambda-close))

    precise-lambda-eq : liftPreciseTerm W′≼W″
        (close (preciseClosingSubstitution γ)
          (liftPreciseTerm W≼W′ (ƛ Nᴾ))) ≡ ƛ bodyᴾ
    precise-lambda-eq =
      trans
        (precise-close-future W′≼W″ (preciseClosingSubstitution γ)
          (liftPreciseTerm W≼W′ (ƛ Nᴾ)))
        (trans
          (cong (close (precise-closing-future W′≼W″
            (preciseClosingSubstitution γ)))
            (sym (liftPreciseTerm-trans W≼W′ W′≼W″ (ƛ Nᴾ))))
          (trans
            (subst-cong precise-tail-env-eq
              (liftPreciseTerm W≼W″ (ƛ Nᴾ)))
            precise-lambda-close))

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

lambda-compatible-from-body : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ} {Nᴾ : Term Δᴾ} {Nᴵ : Term Δᴵ}
  → forgetWorld W ∣ (CTI.ctx-imp Aᴾ Aᴵ p ∷ Γ)
      ⊢² Nᴾ ⊑ Nᴵ ∶ q
  → (∀ i → i ≤ k → CompiledTermRelation {W = W} q i
      (CTI.ctx-imp Aᴾ Aᴵ p ∷ Γ) Nᴾ Nᴵ)
  → CompiledTermRelation {W = W} (I.⇒⊑⇒ p q) k Γ
      (ƛ Nᴾ) (ƛ Nᴵ)
lambda-compatible-from-body body body-related =
  lambda-compatible body
    (λ W′ W≼W′ γ j j≤k →
      functions-related-from-body body-related W≼W′ γ j j≤k)
