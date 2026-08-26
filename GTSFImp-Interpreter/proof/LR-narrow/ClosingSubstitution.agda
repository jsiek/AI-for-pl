module proof.LR-narrow.ClosingSubstitution where

-- File Charter:
--   * Proves lookup and typing for closing substitutions.
--   * Projects related substitutions to their typed endpoint substitutions.
--   * Proves lookup and future-world transport for related substitutions.
--   * Proves endpoint projection coherence under index and future transport.
--   * Supplies proof terms re-exported by the public properties module.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
  renaming (subst to subst≡)

open import Types
open import TyStore
import TermCtx as T
open import CastTerms
import Consistency as C
import Imprecision as I
open import proof.LR-narrow.TermSubstitution using
  (SubstWf; typing-subst; subst-preserves-Value; subst-cong;
   subst-rename; subst-id; single-subst-exts; subst-renameᵗᵐ)
open import proof.TypeInTermSubst using
  (renameᵗᵐ-preserves-Value; typing-shiftᵗ-bind)
open import proof.ImprecisionConsistency using
  (renameᵗ-injective; toRenameᵗ-injective)
open import LR-narrow.World
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using
  (value-imprecision-downward; value-imprecision-future)
open import LR-narrow.ClosingSubstitution
import proof.LR-narrow.Closure as ClosureProof

------------------------------------------------------------------------
-- Every value-relation witness contains typed endpoints
------------------------------------------------------------------------

value-imprecision-endpoints : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {k : ℕ} {Vᴵ Vᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → TypedEndpoints W p Vᴵ Vᴾ
value-imprecision-endpoints = ClosureProof.value-imprecision-endpoints

precise-endpoint-typing : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Vᴾ Vᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ} {k : ℕ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ⟨ Δᴾ , preciseStore (core W) , [] ⟩ ⊢ Vᴾ ⦂ Aᴾ
precise-endpoint-typing {W = W} related =
  subst≡ (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective
      (toRenameᵗ-injective (preciseEmbedding (core W)))
      (preciseEmbedded endpoints))
    (precise-typed endpoints)
  where
  endpoints = value-imprecision-endpoints related

imprecise-endpoint-typing : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Vᴾ Vᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ} {k : ℕ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ⟨ Δᴵ , impreciseStore (core W) , [] ⟩ ⊢ Vᴵ ⦂ Aᴵ
imprecise-endpoint-typing {W = W} related =
  subst≡ (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W)))
      (impreciseEmbedded endpoints))
    (imprecise-typed endpoints)
  where
  endpoints = value-imprecision-endpoints related

------------------------------------------------------------------------
-- Lookup and closing preserve valuehood and typing
------------------------------------------------------------------------

closing-lookup-value : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} {x A}
    (γ : ClosingSubstitution Σ Γ)
  → Γ T.∋ x ⦂ A
  → Value (lookupClosing γ x)
closing-lookup-value (closing-cons vV V⊢ γ) T.Z = vV
closing-lookup-value (closing-cons vV V⊢ γ) (T.S x∈) =
  closing-lookup-value γ x∈

closing-lookup-typing : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} {x A}
    (γ : ClosingSubstitution Σ Γ)
  → Γ T.∋ x ⦂ A
  → ⟨ Δ , Σ , [] ⟩ ⊢ lookupClosing γ x ⦂ A
closing-lookup-typing (closing-cons vV V⊢ γ) T.Z = V⊢
closing-lookup-typing (closing-cons vV V⊢ γ) (T.S x∈) =
  closing-lookup-typing γ x∈

closing-substitution-wf : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} (γ : ClosingSubstitution Σ Γ)
  → SubstWf Δ Σ Γ [] (closingSubstitution γ)
closing-substitution-wf γ = closing-lookup-typing γ

close-universal : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} (γ : ClosingSubstitution Σ Γ) N
  → close γ (Λ N) ≡ Λ (closeTypeBody γ N)
close-universal γ N = refl

close-type-body-preserves-value : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} (γ : ClosingSubstitution Σ Γ) {V}
  → Value V
  → Value (closeTypeBody γ V)
close-type-body-preserves-value γ =
  subst-preserves-Value (liftˢ (closingSubstitution γ))

close-preserves-value : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} (γ : ClosingSubstitution Σ Γ) {V}
  → Value V
  → Value (close γ V)
close-preserves-value γ = subst-preserves-Value (closingSubstitution γ)

close-preserves-typing : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} (γ : ClosingSubstitution Σ Γ) {M A}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ , Σ , [] ⟩ ⊢ close γ M ⦂ A
close-preserves-typing γ = typing-subst (closing-substitution-wf γ)

beta-close-cons : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} {A : Ty Δ} {V N : Term Δ}
    (vV : Value V)
    (V⊢ : ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ A)
    (γ : ClosingSubstitution Σ Γ)
  → (CastTerms.subst (exts (closingSubstitution γ)) N) [ V ]
    ≡ close (closing-cons vV V⊢ γ) N
beta-close-cons {V = V} {N} vV V⊢ γ =
  trans (single-subst-exts (closingSubstitution γ) N V)
    (subst-cong env-eq N)
  where
  env-eq : ∀ x
    → CastTerms.subst (singleSub V)
        (exts (closingSubstitution γ) x)
      ≡ closingSubstitution (closing-cons vV V⊢ γ) x
  env-eq zero = refl
  env-eq (suc x) =
    trans (subst-rename (singleSub V) suc (lookupClosing γ x))
      (subst-id (lookupClosing γ x))

precise-open-typing-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴾ} {M : Term Δᴾ} {A : Ty Δᴾ}
    (W≼W′ : Future W W′)
  → ⟨ Δᴾ , preciseStore (core W) , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δᴾ′ , preciseStore (core W′) ,
        liftPreciseContext W≼W′ Γ ⟩
      ⊢ liftPreciseTerm W≼W′ M ⦂ liftPreciseTy W≼W′ A
precise-open-typing-future {Γ = Γ} future-refl M⊢ =
  subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
    (sym (liftPreciseContext-refl Γ)) M⊢
precise-open-typing-future {Γ = Γ}
    (future-paired W≼W′ related) M⊢ =
  subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
    (sym (liftPreciseContext-paired W≼W′ Γ))
    (typing-shiftᵗ-bind (precise-open-typing-future W≼W′ M⊢))
precise-open-typing-future {Γ = Γ}
    (future-precise W≼W′ r★) M⊢ =
  subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
    (sym (liftPreciseContext-precise W≼W′ Γ))
    (typing-shiftᵗ-bind (precise-open-typing-future W≼W′ M⊢))
precise-open-typing-future {Γ = Γ}
    (future-imprecise W≼W′) M⊢ =
  subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
    (sym (liftPreciseContext-imprecise W≼W′ Γ))
    (precise-open-typing-future W≼W′ M⊢)

imprecise-open-typing-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴵ} {M : Term Δᴵ} {A : Ty Δᴵ}
    (W≼W′ : Future W W′)
  → ⟨ Δᴵ , impreciseStore (core W) , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δᴵ′ , impreciseStore (core W′) ,
        liftImpreciseContext W≼W′ Γ ⟩
      ⊢ liftImpreciseTerm W≼W′ M ⦂ liftImpreciseTy W≼W′ A
imprecise-open-typing-future {Γ = Γ} future-refl M⊢ =
  subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
    (sym (liftImpreciseContext-refl Γ)) M⊢
imprecise-open-typing-future {Γ = Γ}
    (future-paired W≼W′ related) M⊢ =
  subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
    (sym (liftImpreciseContext-paired W≼W′ Γ))
    (typing-shiftᵗ-bind (imprecise-open-typing-future W≼W′ M⊢))
imprecise-open-typing-future {Γ = Γ}
    (future-precise W≼W′ r★) M⊢ =
  subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
    (sym (liftImpreciseContext-precise W≼W′ Γ))
    (imprecise-open-typing-future W≼W′ M⊢)
imprecise-open-typing-future {Γ = Γ}
    (future-imprecise W≼W′) M⊢ =
  subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
    (sym (liftImpreciseContext-imprecise W≼W′ Γ))
    (typing-shiftᵗ-bind (imprecise-open-typing-future W≼W′ M⊢))

------------------------------------------------------------------------
-- Endpoint projections and related lookup
------------------------------------------------------------------------

preciseClosingSubstitution : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : ContextImprecision W}
  → RelatedClosingSubstitutions W k Γ
  → ClosingSubstitution (preciseStore (core W)) (preciseContext Γ)
preciseClosingSubstitution related-empty = closing-empty
preciseClosingSubstitution {k = k} (related-cons p related γ) =
  closing-cons (precise-value endpoints)
    (precise-endpoint-typing (related k ≤-refl))
    (preciseClosingSubstitution γ)
  where
  endpoints = value-imprecision-endpoints (related k ≤-refl)

impreciseClosingSubstitution : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : ContextImprecision W}
  → RelatedClosingSubstitutions W k Γ
  → ClosingSubstitution (impreciseStore (core W)) (impreciseContext Γ)
impreciseClosingSubstitution related-empty = closing-empty
impreciseClosingSubstitution {k = k} (related-cons p related γ) =
  closing-cons (imprecise-value endpoints)
    (imprecise-endpoint-typing (related k ≤-refl))
    (impreciseClosingSubstitution γ)
  where
  endpoints = value-imprecision-endpoints (related k ≤-refl)

related-closing-lookup : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : ContextImprecision W} {x Aᴾ Aᴵ p}
    (x∈ : Γ ∋ᴿ x ⦂ context-imp Aᴾ Aᴵ p)
    (γ : RelatedClosingSubstitutions W k Γ)
  → (∀ j → j ≤ k → ValueImprecision W p j
        (lookupClosing (impreciseClosingSubstitution γ) x)
        (lookupClosing (preciseClosingSubstitution γ) x))
related-closing-lookup Zᴿ (related-cons p related γ) = related
related-closing-lookup (Sᴿ x∈) (related-cons p related γ) =
  related-closing-lookup x∈ γ

lift-context-lookup : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : ContextImprecision W} {x Aᴾ Aᴵ p}
    (W≼W′ : Future W W′)
  → Γ ∋ᴿ x ⦂ context-imp Aᴾ Aᴵ p
  → liftContextImprecision W≼W′ Γ ∋ᴿ x ⦂
      context-imp (liftPreciseTy W≼W′ Aᴾ)
        (liftImpreciseTy W≼W′ Aᴵ) (liftLocalImprecision W≼W′ p)
lift-context-lookup W≼W′ Zᴿ = Zᴿ
lift-context-lookup W≼W′ (Sᴿ x∈) =
  Sᴿ (lift-context-lookup W≼W′ x∈)

related-closing-downward : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {j k : ℕ}
    {Γ : ContextImprecision W}
  → j ≤ k
  → RelatedClosingSubstitutions W k Γ
  → RelatedClosingSubstitutions W j Γ
related-closing-downward j≤k related-empty = related-empty
related-closing-downward j≤k (related-cons p related γ) =
  related-cons p (λ i i≤j → related i (≤-trans i≤j j≤k))
    (related-closing-downward j≤k γ)

related-closing-bind : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {k : ℕ} {Γ : ContextImprecision W} {Aᴾ Aᴵ}
    (W≼W′ : Future W W′) (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
    {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
  → (∀ j → j ≤ k →
      ValueImprecision W′ (liftCenterImprecision W≼W′ p) j Vᴵ Vᴾ)
  → RelatedClosingSubstitutions W′ k
      (liftContextImprecision W≼W′ Γ)
  → RelatedClosingSubstitutions W′ k
      (liftContextImprecision W≼W′
        (context-imp Aᴾ Aᴵ p ∷ Γ))
related-closing-bind W≼W′ p related γ =
  related-cons (liftLocalImprecision W≼W′ p)
    (λ j j≤k → ClosureProof.value-imprecision-center→local W≼W′ p
      (related j j≤k)) γ

related-closing-trans : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁ : TyCtx}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂ : TyCtx}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {k : ℕ} {Γ : ContextImprecision W₀}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
  → RelatedClosingSubstitutions W₂ k
      (liftContextImprecision W₁≼W₂
        (liftContextImprecision W₀≼W₁ Γ))
  → RelatedClosingSubstitutions W₂ k
      (liftContextImprecision (future-trans W₀≼W₁ W₁≼W₂) Γ)
related-closing-trans {Γ = []} W₀≼W₁ W₁≼W₂ related-empty =
  related-empty
related-closing-trans {W₂ = W₂} {k = k}
    {Γ = context-imp Aᴾ Aᴵ p ∷ Γ} W₀≼W₁ W₁≼W₂
    (related-cons {Vᴾ = Vᴾ} {Vᴵ = Vᴵ} sequential related γ) =
  related-cons composite related′
    (related-closing-trans W₀≼W₁ W₁≼W₂ γ)
  where
  W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂
  composite = liftLocalImprecision W₀≼W₂ p
  related′ : ∀ i → i ≤ k → ValueImprecision W₂ composite i Vᴵ Vᴾ
  related′ i i≤k =
    ClosureProof.value-imprecision-reindex composite sequential
      (cong (embedPrecise (core W₂))
        (liftPreciseTy-trans W₀≼W₁ W₁≼W₂ Aᴾ))
      (cong (embedImprecise (core W₂))
        (liftImpreciseTy-trans W₀≼W₁ W₁≼W₂ Aᴵ))
      (related i i≤k)

------------------------------------------------------------------------
-- Future transport
------------------------------------------------------------------------

shiftClosingBind : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} {B : Ty Δ}
  → ClosingSubstitution Σ Γ
  → ClosingSubstitution (store-bind Σ B) (T.⇑ᶜ Γ)
shiftClosingBind closing-empty = closing-empty
shiftClosingBind (closing-cons vV V⊢ γ) =
  closing-cons (renameᵗᵐ-preserves-Value C.wk↪ᵗ vV)
    (typing-shiftᵗ-bind V⊢) (shiftClosingBind γ)

lookupClosing-subst : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ Γ′ : T.TermCtx Δ}
    (eq : Γ ≡ Γ′) (γ : ClosingSubstitution Σ Γ) x
  → lookupClosing (subst≡ (ClosingSubstitution Σ) eq γ) x
    ≡ lookupClosing γ x
lookupClosing-subst refl γ x = refl

lookup-shiftClosingBind : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {Γ : T.TermCtx Δ} {B : Ty Δ}
    (γ : ClosingSubstitution Σ Γ) x
  → lookupClosing (shiftClosingBind {B = B} γ) x
    ≡ ⇑ᵗᵐ (lookupClosing γ x)
lookup-shiftClosingBind closing-empty x = refl
lookup-shiftClosingBind (closing-cons vV V⊢ γ) zero = refl
lookup-shiftClosingBind (closing-cons vV V⊢ γ) (suc x) =
  lookup-shiftClosingBind γ x

precise-closing-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴾ} (W≼W′ : Future W W′)
  → ClosingSubstitution (preciseStore (core W)) Γ
  → ClosingSubstitution (preciseStore (core W′))
      (liftPreciseContext W≼W′ Γ)
precise-closing-future future-refl closing-empty = closing-empty
precise-closing-future future-refl (closing-cons vV V⊢ γ) =
  closing-cons vV V⊢ (precise-closing-future future-refl γ)
precise-closing-future
    {Γ = Γ} (future-paired {Aᴾ = Bᴾ} W≼W′ related) γ =
  subst≡ (ClosingSubstitution _)
    (sym (liftPreciseContext-paired W≼W′ Γ))
    (shiftClosingBind {B = Bᴾ} (precise-closing-future W≼W′ γ))
precise-closing-future
    {Γ = Γ} (future-precise {Aᴾ = Bᴾ} W≼W′ r★) γ =
  subst≡ (ClosingSubstitution _)
    (sym (liftPreciseContext-precise W≼W′ Γ))
    (shiftClosingBind {B = Bᴾ} (precise-closing-future W≼W′ γ))
precise-closing-future {Γ = Γ} (future-imprecise W≼W′) γ =
  subst≡ (ClosingSubstitution _)
    (sym (liftPreciseContext-imprecise W≼W′ Γ))
    (precise-closing-future W≼W′ γ)

imprecise-closing-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴵ} (W≼W′ : Future W W′)
  → ClosingSubstitution (impreciseStore (core W)) Γ
  → ClosingSubstitution (impreciseStore (core W′))
      (liftImpreciseContext W≼W′ Γ)
imprecise-closing-future future-refl closing-empty = closing-empty
imprecise-closing-future future-refl (closing-cons vV V⊢ γ) =
  closing-cons vV V⊢ (imprecise-closing-future future-refl γ)
imprecise-closing-future
    {Γ = Γ} (future-paired {Aᴵ = Bᴵ} W≼W′ related) γ =
  subst≡ (ClosingSubstitution _)
    (sym (liftImpreciseContext-paired W≼W′ Γ))
    (shiftClosingBind {B = Bᴵ} (imprecise-closing-future W≼W′ γ))
imprecise-closing-future {Γ = Γ}
    (future-precise W≼W′ r★) γ =
  subst≡ (ClosingSubstitution _)
    (sym (liftImpreciseContext-precise W≼W′ Γ))
    (imprecise-closing-future W≼W′ γ)
imprecise-closing-future {Γ = Γ}
    (future-imprecise {Aᴵ = Bᴵ} W≼W′) γ =
  subst≡ (ClosingSubstitution _)
    (sym (liftImpreciseContext-imprecise W≼W′ Γ))
    (shiftClosingBind {B = Bᴵ} (imprecise-closing-future W≼W′ γ))

precise-closing-future-lookup : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴾ} (W≼W′ : Future W W′)
    (γ : ClosingSubstitution (preciseStore (core W)) Γ) x
  → lookupClosing (precise-closing-future W≼W′ γ) x
    ≡ liftPreciseTerm W≼W′ (lookupClosing γ x)
precise-closing-future-lookup future-refl closing-empty x = refl
precise-closing-future-lookup future-refl
    (closing-cons vV V⊢ γ) zero = refl
precise-closing-future-lookup future-refl
    (closing-cons vV V⊢ γ) (suc x) =
  precise-closing-future-lookup future-refl γ x
precise-closing-future-lookup
    {Γ = Γ} (future-paired {Aᴾ = Bᴾ} W≼W′ related) γ x =
  trans
    (lookupClosing-subst
      (sym (liftPreciseContext-paired W≼W′ Γ))
      (shiftClosingBind {B = Bᴾ} (precise-closing-future W≼W′ γ)) x)
    (trans (lookup-shiftClosingBind (precise-closing-future W≼W′ γ) x)
      (cong ⇑ᵗᵐ (precise-closing-future-lookup W≼W′ γ x)))
precise-closing-future-lookup
    {Γ = Γ} (future-precise {Aᴾ = Bᴾ} W≼W′ r★) γ x =
  trans
    (lookupClosing-subst
      (sym (liftPreciseContext-precise W≼W′ Γ))
      (shiftClosingBind {B = Bᴾ} (precise-closing-future W≼W′ γ)) x)
    (trans (lookup-shiftClosingBind (precise-closing-future W≼W′ γ) x)
      (cong ⇑ᵗᵐ (precise-closing-future-lookup W≼W′ γ x)))
precise-closing-future-lookup
    {Γ = Γ} (future-imprecise W≼W′) γ x =
  trans
    (lookupClosing-subst
      (sym (liftPreciseContext-imprecise W≼W′ Γ))
      (precise-closing-future W≼W′ γ) x)
    (precise-closing-future-lookup W≼W′ γ x)

imprecise-closing-future-lookup : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴵ} (W≼W′ : Future W W′)
    (γ : ClosingSubstitution (impreciseStore (core W)) Γ) x
  → lookupClosing (imprecise-closing-future W≼W′ γ) x
    ≡ liftImpreciseTerm W≼W′ (lookupClosing γ x)
imprecise-closing-future-lookup future-refl closing-empty x = refl
imprecise-closing-future-lookup future-refl
    (closing-cons vV V⊢ γ) zero = refl
imprecise-closing-future-lookup future-refl
    (closing-cons vV V⊢ γ) (suc x) =
  imprecise-closing-future-lookup future-refl γ x
imprecise-closing-future-lookup
    {Γ = Γ} (future-paired {Aᴵ = Bᴵ} W≼W′ related) γ x =
  trans
    (lookupClosing-subst
      (sym (liftImpreciseContext-paired W≼W′ Γ))
      (shiftClosingBind {B = Bᴵ}
        (imprecise-closing-future W≼W′ γ)) x)
    (trans
      (lookup-shiftClosingBind (imprecise-closing-future W≼W′ γ) x)
      (cong ⇑ᵗᵐ (imprecise-closing-future-lookup W≼W′ γ x)))
imprecise-closing-future-lookup
    {Γ = Γ} (future-precise W≼W′ r★) γ x =
  trans
    (lookupClosing-subst
      (sym (liftImpreciseContext-precise W≼W′ Γ))
      (imprecise-closing-future W≼W′ γ) x)
    (imprecise-closing-future-lookup W≼W′ γ x)
imprecise-closing-future-lookup
    {Γ = Γ} (future-imprecise {Aᴵ = Bᴵ} W≼W′) γ x =
  trans
    (lookupClosing-subst
      (sym (liftImpreciseContext-imprecise W≼W′ Γ))
      (shiftClosingBind {B = Bᴵ}
        (imprecise-closing-future W≼W′ γ)) x)
    (trans
      (lookup-shiftClosingBind (imprecise-closing-future W≼W′ γ) x)
      (cong ⇑ᵗᵐ (imprecise-closing-future-lookup W≼W′ γ x)))

precise-close-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴾ} (W≼W′ : Future W W′)
    (γ : ClosingSubstitution (preciseStore (core W)) Γ) M
  → liftPreciseTerm W≼W′ (close γ M)
    ≡ close (precise-closing-future W≼W′ γ)
        (liftPreciseTerm W≼W′ M)
precise-close-future future-refl γ M =
  subst-cong (λ x → sym (precise-closing-future-lookup future-refl γ x)) M
precise-close-future
    (future-paired W≼W′ related) γ M =
  trans (cong ⇑ᵗᵐ (precise-close-future W≼W′ γ M))
    (sym (subst-renameᵗᵐ C.wk↪ᵗ
      (closingSubstitution
        (precise-closing-future
          (future-paired W≼W′ related) γ))
      (closingSubstitution (precise-closing-future W≼W′ γ))
      (liftPreciseTerm W≼W′ M) env-eq))
  where
  env-eq : ∀ x
    → closingSubstitution
        (precise-closing-future
          (future-paired W≼W′ related) γ) x
      ≡ ⇑ᵗᵐ (closingSubstitution
          (precise-closing-future W≼W′ γ) x)
  env-eq x =
    trans
      (precise-closing-future-lookup
        (future-paired W≼W′ related) γ x)
      (cong ⇑ᵗᵐ (sym (precise-closing-future-lookup W≼W′ γ x)))
precise-close-future
    (future-precise W≼W′ r★) γ M =
  trans (cong ⇑ᵗᵐ (precise-close-future W≼W′ γ M))
    (sym (subst-renameᵗᵐ C.wk↪ᵗ
      (closingSubstitution
        (precise-closing-future (future-precise W≼W′ r★) γ))
      (closingSubstitution (precise-closing-future W≼W′ γ))
      (liftPreciseTerm W≼W′ M) env-eq))
  where
  env-eq : ∀ x
    → closingSubstitution
        (precise-closing-future (future-precise W≼W′ r★) γ) x
      ≡ ⇑ᵗᵐ (closingSubstitution
          (precise-closing-future W≼W′ γ) x)
  env-eq x =
    trans (precise-closing-future-lookup
      (future-precise W≼W′ r★) γ x)
      (cong ⇑ᵗᵐ (sym (precise-closing-future-lookup W≼W′ γ x)))
precise-close-future (future-imprecise W≼W′) γ M =
  trans (precise-close-future W≼W′ γ M)
    (subst-cong env-eq (liftPreciseTerm W≼W′ M))
  where
  env-eq : ∀ x
    → closingSubstitution (precise-closing-future W≼W′ γ) x
      ≡ closingSubstitution
          (precise-closing-future (future-imprecise W≼W′) γ) x
  env-eq x =
    trans (precise-closing-future-lookup W≼W′ γ x)
      (sym (precise-closing-future-lookup
        (future-imprecise W≼W′) γ x))

imprecise-close-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Γ : T.TermCtx Δᴵ} (W≼W′ : Future W W′)
    (γ : ClosingSubstitution (impreciseStore (core W)) Γ) M
  → liftImpreciseTerm W≼W′ (close γ M)
    ≡ close (imprecise-closing-future W≼W′ γ)
        (liftImpreciseTerm W≼W′ M)
imprecise-close-future future-refl γ M =
  subst-cong
    (λ x → sym (imprecise-closing-future-lookup future-refl γ x)) M
imprecise-close-future
    (future-paired W≼W′ related) γ M =
  trans (cong ⇑ᵗᵐ (imprecise-close-future W≼W′ γ M))
    (sym (subst-renameᵗᵐ C.wk↪ᵗ
      (closingSubstitution
        (imprecise-closing-future
          (future-paired W≼W′ related) γ))
      (closingSubstitution (imprecise-closing-future W≼W′ γ))
      (liftImpreciseTerm W≼W′ M) env-eq))
  where
  env-eq : ∀ x
    → closingSubstitution
        (imprecise-closing-future
          (future-paired W≼W′ related) γ) x
      ≡ ⇑ᵗᵐ (closingSubstitution
          (imprecise-closing-future W≼W′ γ) x)
  env-eq x =
    trans
      (imprecise-closing-future-lookup
        (future-paired W≼W′ related) γ x)
      (cong ⇑ᵗᵐ
        (sym (imprecise-closing-future-lookup W≼W′ γ x)))
imprecise-close-future
    (future-precise W≼W′ r★) γ M =
  trans (imprecise-close-future W≼W′ γ M)
    (subst-cong env-eq (liftImpreciseTerm W≼W′ M))
  where
  env-eq : ∀ x
    → closingSubstitution (imprecise-closing-future W≼W′ γ) x
      ≡ closingSubstitution
          (imprecise-closing-future (future-precise W≼W′ r★) γ) x
  env-eq x =
    trans (imprecise-closing-future-lookup W≼W′ γ x)
      (sym (imprecise-closing-future-lookup
        (future-precise W≼W′ r★) γ x))
imprecise-close-future (future-imprecise W≼W′) γ M =
  trans (cong ⇑ᵗᵐ (imprecise-close-future W≼W′ γ M))
    (sym (subst-renameᵗᵐ C.wk↪ᵗ
      (closingSubstitution
        (imprecise-closing-future (future-imprecise W≼W′) γ))
      (closingSubstitution (imprecise-closing-future W≼W′ γ))
      (liftImpreciseTerm W≼W′ M) env-eq))
  where
  env-eq : ∀ x
    → closingSubstitution
        (imprecise-closing-future (future-imprecise W≼W′) γ) x
      ≡ ⇑ᵗᵐ (closingSubstitution
          (imprecise-closing-future W≼W′ γ) x)
  env-eq x =
    trans
      (imprecise-closing-future-lookup
        (future-imprecise W≼W′) γ x)
      (cong ⇑ᵗᵐ
        (sym (imprecise-closing-future-lookup W≼W′ γ x)))

related-closing-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {k : ℕ} {Γ : ContextImprecision W}
    (W≼W′ : Future W W′)
  → RelatedClosingSubstitutions W k Γ
  → RelatedClosingSubstitutions W′ k
      (liftContextImprecision W≼W′ Γ)
related-closing-future W≼W′ related-empty = related-empty
related-closing-future W≼W′
    (related-cons {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p related γ) =
  related-cons (liftLocalImprecision W≼W′ p)
    (λ j j≤k → related′ j j≤k)
    (related-closing-future W≼W′ γ)
  where
  related′ = λ j j≤k → ClosureProof.value-imprecision-reindex
    (liftLocalImprecision W≼W′ p)
    (liftCenterImprecision W≼W′ p)
    (embedPrecise-lift W≼W′ Aᴾ)
    (embedImprecise-lift W≼W′ Aᴵ)
    (value-imprecision-future W≼W′ (related j j≤k))

------------------------------------------------------------------------
-- Endpoint projections preserve the entries of related substitutions
------------------------------------------------------------------------

lift-precise-blame : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → liftPreciseTerm W≼W′ blame ≡ blame
lift-precise-blame future-refl = refl
lift-precise-blame (future-paired W≼W′ related)
    rewrite lift-precise-blame W≼W′ = refl
lift-precise-blame (future-precise W≼W′ r★)
    rewrite lift-precise-blame W≼W′ = refl
lift-precise-blame (future-imprecise W≼W′) =
  lift-precise-blame W≼W′

lift-imprecise-blame : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → liftImpreciseTerm W≼W′ blame ≡ blame
lift-imprecise-blame future-refl = refl
lift-imprecise-blame (future-paired W≼W′ related)
    rewrite lift-imprecise-blame W≼W′ = refl
lift-imprecise-blame (future-precise W≼W′ r★) =
  lift-imprecise-blame W≼W′
lift-imprecise-blame (future-imprecise W≼W′)
    rewrite lift-imprecise-blame W≼W′ = refl

precise-related-downward-lookup : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {j k : ℕ}
    {Γ : ContextImprecision W}
    (j≤k : j ≤ k) (γ : RelatedClosingSubstitutions W k Γ) x
  → lookupClosing
      (preciseClosingSubstitution (related-closing-downward j≤k γ)) x
    ≡ lookupClosing (preciseClosingSubstitution γ) x
precise-related-downward-lookup j≤k related-empty x = refl
precise-related-downward-lookup j≤k (related-cons p related γ) zero =
  refl
precise-related-downward-lookup j≤k (related-cons p related γ) (suc x) =
  precise-related-downward-lookup j≤k γ x

imprecise-related-downward-lookup : ∀ {Δᴾ Δᴵ Δᶜ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {j k : ℕ}
    {Γ : ContextImprecision W}
    (j≤k : j ≤ k) (γ : RelatedClosingSubstitutions W k Γ) x
  → lookupClosing
      (impreciseClosingSubstitution (related-closing-downward j≤k γ)) x
    ≡ lookupClosing (impreciseClosingSubstitution γ) x
imprecise-related-downward-lookup j≤k related-empty x = refl
imprecise-related-downward-lookup j≤k (related-cons p related γ) zero =
  refl
imprecise-related-downward-lookup j≤k
    (related-cons p related γ) (suc x) =
  imprecise-related-downward-lookup j≤k γ x

precise-related-future-lookup : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {k : ℕ} {Γ : ContextImprecision W}
    (W≼W′ : Future W W′)
    (γ : RelatedClosingSubstitutions W k Γ) x
  → lookupClosing
      (preciseClosingSubstitution (related-closing-future W≼W′ γ)) x
    ≡ liftPreciseTerm W≼W′
        (lookupClosing (preciseClosingSubstitution γ) x)
precise-related-future-lookup W≼W′ related-empty x =
  sym (lift-precise-blame W≼W′)
precise-related-future-lookup W≼W′
    (related-cons p related γ) zero = refl
precise-related-future-lookup W≼W′
    (related-cons p related γ) (suc x) =
  precise-related-future-lookup W≼W′ γ x

imprecise-related-future-lookup : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {k : ℕ} {Γ : ContextImprecision W}
    (W≼W′ : Future W W′)
    (γ : RelatedClosingSubstitutions W k Γ) x
  → lookupClosing
      (impreciseClosingSubstitution (related-closing-future W≼W′ γ)) x
    ≡ liftImpreciseTerm W≼W′
        (lookupClosing (impreciseClosingSubstitution γ) x)
imprecise-related-future-lookup W≼W′ related-empty x =
  sym (lift-imprecise-blame W≼W′)
imprecise-related-future-lookup W≼W′
    (related-cons p related γ) zero = refl
imprecise-related-future-lookup W≼W′
    (related-cons p related γ) (suc x) =
  imprecise-related-future-lookup W≼W′ γ x

precise-related-trans-lookup : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁ : TyCtx}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂ : TyCtx}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {k : ℕ} {Γ : ContextImprecision W₀}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (γ : RelatedClosingSubstitutions W₂ k
      (liftContextImprecision W₁≼W₂
        (liftContextImprecision W₀≼W₁ Γ))) x
  → lookupClosing
      (preciseClosingSubstitution
        (related-closing-trans W₀≼W₁ W₁≼W₂ γ)) x
    ≡ lookupClosing (preciseClosingSubstitution γ) x
precise-related-trans-lookup {Γ = []} W₀≼W₁ W₁≼W₂ related-empty x =
  refl
precise-related-trans-lookup {Γ = context-imp Aᴾ Aᴵ p ∷ Γ}
    W₀≼W₁ W₁≼W₂ (related-cons q related γ) zero = refl
precise-related-trans-lookup {Γ = context-imp Aᴾ Aᴵ p ∷ Γ}
    W₀≼W₁ W₁≼W₂ (related-cons q related γ) (suc x) =
  precise-related-trans-lookup W₀≼W₁ W₁≼W₂ γ x

imprecise-related-trans-lookup : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁ : TyCtx}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂ : TyCtx}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {k : ℕ} {Γ : ContextImprecision W₀}
    (W₀≼W₁ : Future W₀ W₁) (W₁≼W₂ : Future W₁ W₂)
    (γ : RelatedClosingSubstitutions W₂ k
      (liftContextImprecision W₁≼W₂
        (liftContextImprecision W₀≼W₁ Γ))) x
  → lookupClosing
      (impreciseClosingSubstitution
        (related-closing-trans W₀≼W₁ W₁≼W₂ γ)) x
    ≡ lookupClosing (impreciseClosingSubstitution γ) x
imprecise-related-trans-lookup {Γ = []}
    W₀≼W₁ W₁≼W₂ related-empty x = refl
imprecise-related-trans-lookup {Γ = context-imp Aᴾ Aᴵ p ∷ Γ}
    W₀≼W₁ W₁≼W₂ (related-cons q related γ) zero = refl
imprecise-related-trans-lookup {Γ = context-imp Aᴾ Aᴵ p ∷ Γ}
    W₀≼W₁ W₁≼W₂ (related-cons q related γ) (suc x) =
  imprecise-related-trans-lookup W₀≼W₁ W₁≼W₂ γ x
