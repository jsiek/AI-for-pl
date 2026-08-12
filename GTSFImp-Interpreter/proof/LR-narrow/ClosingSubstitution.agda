module proof.LR-narrow.ClosingSubstitution where

-- File Charter:
--   * Proves lookup and typing for closing substitutions.
--   * Projects related substitutions to their typed endpoint substitutions.
--   * Proves lookup and future-world transport for related substitutions.
--   * Supplies proof terms re-exported by the public properties module.

open import Data.List using ([]; _∷_)
import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym)
  renaming (subst to subst≡)

open import Types
open import TyStore
import TermCtx as T
open import CastTerms
import Consistency as C
import Imprecision as I
open import proof.TermInTermSubst using
  (SubstWf; typing-subst; subst-preserves-Value)
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
value-imprecision-endpoints {k = zero} related = related
value-imprecision-endpoints {k = suc k} related =
  value-imprecision-endpoints (value-imprecision-downward related)

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

lift-precise-context-paired : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Bᴾ : Ty Δᴾ′} {Bᴵ : Ty Δᴵ′}
    {r : Bᴾ ⊑ᵂ⟨ core W′ ⟩ Bᴵ}
    {fresh : SemanticAtom (pairedBindCore (core W′) Bᴾ Bᴵ) Fin.zero}
    (W≼W′ : Future W W′) (Γ : T.TermCtx Δᴾ)
  → liftPreciseContext (future-paired W≼W′ r fresh) Γ
      ≡ T.⇑ᶜ (liftPreciseContext W≼W′ Γ)
lift-precise-context-paired W≼W′ [] = refl
lift-precise-context-paired W≼W′ (A ∷ Γ) =
  cong (⇑ᵗ (liftPreciseTy W≼W′ A) ∷_)
    (lift-precise-context-paired W≼W′ Γ)

lift-precise-context-precise : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Bᴾ : Ty Δᴾ′}
    {fresh : DynamicSemanticAtom (preciseBindCore (core W′) Bᴾ) Fin.zero}
    (W≼W′ : Future W W′) (Γ : T.TermCtx Δᴾ)
  → liftPreciseContext (future-precise W≼W′ fresh) Γ
      ≡ T.⇑ᶜ (liftPreciseContext W≼W′ Γ)
lift-precise-context-precise W≼W′ [] = refl
lift-precise-context-precise W≼W′ (A ∷ Γ) =
  cong (⇑ᵗ (liftPreciseTy W≼W′ A) ∷_)
    (lift-precise-context-precise W≼W′ Γ)

lift-imprecise-context-paired : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Bᴾ : Ty Δᴾ′} {Bᴵ : Ty Δᴵ′}
    {r : Bᴾ ⊑ᵂ⟨ core W′ ⟩ Bᴵ}
    {fresh : SemanticAtom (pairedBindCore (core W′) Bᴾ Bᴵ) Fin.zero}
    (W≼W′ : Future W W′) (Γ : T.TermCtx Δᴵ)
  → liftImpreciseContext (future-paired W≼W′ r fresh) Γ
      ≡ T.⇑ᶜ (liftImpreciseContext W≼W′ Γ)
lift-imprecise-context-paired W≼W′ [] = refl
lift-imprecise-context-paired W≼W′ (A ∷ Γ) =
  cong (⇑ᵗ (liftImpreciseTy W≼W′ A) ∷_)
    (lift-imprecise-context-paired W≼W′ Γ)

lift-imprecise-context-precise : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Bᴾ : Ty Δᴾ′}
    {fresh : DynamicSemanticAtom (preciseBindCore (core W′) Bᴾ) Fin.zero}
    (W≼W′ : Future W W′) (Γ : T.TermCtx Δᴵ)
  → liftImpreciseContext (future-precise W≼W′ fresh) Γ
      ≡ liftImpreciseContext W≼W′ Γ
lift-imprecise-context-precise W≼W′ [] = refl
lift-imprecise-context-precise W≼W′ (A ∷ Γ) =
  cong (liftImpreciseTy W≼W′ A ∷_)
    (lift-imprecise-context-precise W≼W′ Γ)

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
    {Γ = Γ} (future-paired {Aᴾ = Bᴾ} W≼W′ related fresh) γ =
  subst≡ (ClosingSubstitution _)
    (sym (lift-precise-context-paired W≼W′ Γ))
    (shiftClosingBind {B = Bᴾ} (precise-closing-future W≼W′ γ))
precise-closing-future
    {Γ = Γ} (future-precise {Aᴾ = Bᴾ} W≼W′ fresh) γ =
  subst≡ (ClosingSubstitution _)
    (sym (lift-precise-context-precise W≼W′ Γ))
    (shiftClosingBind {B = Bᴾ} (precise-closing-future W≼W′ γ))

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
    {Γ = Γ} (future-paired {Aᴵ = Bᴵ} W≼W′ related fresh) γ =
  subst≡ (ClosingSubstitution _)
    (sym (lift-imprecise-context-paired W≼W′ Γ))
    (shiftClosingBind {B = Bᴵ} (imprecise-closing-future W≼W′ γ))
imprecise-closing-future {Γ = Γ}
    (future-precise W≼W′ fresh) γ =
  subst≡ (ClosingSubstitution _)
    (sym (lift-imprecise-context-precise W≼W′ Γ))
    (imprecise-closing-future W≼W′ γ)

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
