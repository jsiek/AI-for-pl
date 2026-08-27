{-# OPTIONS --safe #-}

module proof.DGG.TransportSourceBindProof where

-- File Charter:
--   * Proves transport of every cast-term-imprecision constructor through a
--     source-only runtime allocation.
--   * Keeps only the genuine source-rebase commutation lemmas as module
--     parameters once their exact statements have been identified.
--   * Contains no compatibility world, classifier, or result wrapper.

import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; subst; cong)

import TermCtx as TC
import TyStore
open import Types using (`∀; _[_]ᵗ)
open import Consistency using (toRenameᵗ)
import Consistency as Cons
open import CastTerms using (Ctx; renameᵗᵐ)
open import Primitives using (κℕ; κ𝔹; addℕ; and𝔹)
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (toRenameᵗ-injective)
open import proof.TypeInTermSubst using
  (reveal-renameᵗ; conceal-renameᵗ; toRename-keep-eq;
   renameᵗ-wk-eq; rename-openᵗ;
   rename-occurs; renameᵗᵐ-preserves-Value)
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition; concealGeneratorPosition;
   revealGeneratorPosition-rename; concealGeneratorPosition-rename)
open import proof.DGG.World using
  (_⊑ᶜ_; _⊑ᵀ⟨_⟩_; ηᴸᶜ; ηᴿᶜ; marksᶜ)
open import proof.DGG.TransportTermImprecisionStepDef using
  (TransportSourceBindᵀ)
open import proof.DGG.TransportSourceBindDef using
  ( SourceBindScope
  ; source-scope-root
  ; source-scope-term
  ; source-scope-both
  ; source-scope-left
  ; source-scope-center
  ; source-scope-left-commutes
  ; source-scope-right-commutes
  ; source-scope-mark
  ; source-scope-context
  ; source-scope-store
  ; source-scope-⊑ᵀ
  ; TransportSourceBindScopeᵀ
  ; TransportSourceBindTargetRevealRebaseᵀ
  ; TransportSourceBindTargetConcealRebaseᵀ
  )
import proof.DGG.CastTermImprecision as CTI


source-member-scope : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore.TyStore Δᴸ} {Σᴸ⁺ : TyStore.TyStore Δᴸ⁺}
    {Σᴿ : TyStore.TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴸ⁺ : TC.TermCtx Δᴸ⁺}
    {Γᴿ : TC.TermCtx Δᴿ} {ρ : Δᴸ Cons.↪ᵗ Δᴸ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {x} {A : Types.Ty Δᴸ}
  → (plan : SourceBindScope ρ γ γ⁺)
  → Γᴸ TC.∋ x ⦂ A
  → Γᴸ⁺ TC.∋ x ⦂ Types.renameᵗ (toRenameᵗ ρ) A
source-member-scope {ρ = ρ} plan member =
  subst (λ Γ → Γ TC.∋ _ ⦂ Types.renameᵗ (toRenameᵗ ρ) _)
    (sym (source-scope-context plan))
    (TC.renameᵗ-∋ (toRenameᵗ ρ) member)


source-scope-aligned : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore.TyStore Δᴸ} {Σᴸ⁺ : TyStore.TyStore Δᴸ⁺}
    {Σᴿ : TyStore.TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴸ⁺ : TC.TermCtx Δᴸ⁺}
    {Γᴿ : TC.TermCtx Δᴿ} {ρ : Δᴸ Cons.↪ᵗ Δᴸ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴸ : Types.TyVar Δᴸ} {Xᴿ : Types.TyVar Δᴿ}
  → (plan : SourceBindScope ρ γ γ⁺)
  → toRenameᵗ (ηᴸᶜ γ) Xᴸ ≡ toRenameᵗ (ηᴿᶜ γ) Xᴿ
  → toRenameᵗ (ηᴸᶜ γ⁺) (toRenameᵗ ρ Xᴸ)
    ≡ toRenameᵗ (ηᴿᶜ γ⁺) Xᴿ
source-scope-aligned plan aligned =
  trans (sym (source-scope-left-commutes plan _))
    (trans (cong (toRenameᵗ (source-scope-center plan)) aligned)
      (source-scope-right-commutes plan _))


source-scope-source-mark : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore.TyStore Δᴸ} {Σᴸ⁺ : TyStore.TyStore Δᴸ⁺}
    {Σᴿ : TyStore.TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴸ⁺ : TC.TermCtx Δᴸ⁺}
    {Γᴿ : TC.TermCtx Δᴿ} {ρ : Δᴸ Cons.↪ᵗ Δᴸ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴸ : Types.TyVar Δᴸ} {v}
  → (plan : SourceBindScope ρ γ γ⁺)
  → marksᶜ γ (toRenameᵗ (ηᴸᶜ γ) Xᴸ) ≡ v
  → marksᶜ γ⁺
      (toRenameᵗ (ηᴸᶜ γ⁺) (toRenameᵗ ρ Xᴸ)) ≡ v
source-scope-source-mark {γ⁺ = γ⁺} {Xᴸ = Xᴸ} plan mark =
  trans
    (cong (marksᶜ γ⁺) (sym (source-scope-left-commutes plan Xᴸ)))
    (trans (source-scope-mark plan _) mark)


source-scope-source-disaligned : ∀
    {Δᴸ Δᴸ⁺ Δᴿ}
    {Σᴸ : TyStore.TyStore Δᴸ} {Σᴸ⁺ : TyStore.TyStore Δᴸ⁺}
    {Σᴿ : TyStore.TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴸ⁺ : TC.TermCtx Δᴸ⁺}
    {Γᴿ : TC.TermCtx Δᴿ} {ρ : Δᴸ Cons.↪ᵗ Δᴸ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴸ : Types.TyVar Δᴸ}
  → (plan : SourceBindScope ρ γ γ⁺)
  → (∀ Xᴿ → toRenameᵗ (ηᴿᶜ γ) Xᴿ
      ≢ toRenameᵗ (ηᴸᶜ γ) Xᴸ)
  → ∀ Xᴿ → toRenameᵗ (ηᴿᶜ γ⁺) Xᴿ
      ≢ toRenameᵗ (ηᴸᶜ γ⁺) (toRenameᵗ ρ Xᴸ)
source-scope-source-disaligned plan free Xᴿ aligned =
  free Xᴿ (toRenameᵗ-injective (source-scope-center plan)
    (trans (source-scope-right-commutes plan Xᴿ)
      (trans aligned (sym (source-scope-left-commutes plan _)))))


retarget-CTI : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M M′ A B} {p q : A ⊑ᵀ⟨ γ ⟩ B}
  → γ CTI.⊢² M ⊑ M′ ∶ p
  → γ CTI.⊢² M ⊑ M′ ∶ q
retarget-CTI {p = p} {q = q} related =
  subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r) (PI.⊑-unique p q) related


transport-source-type : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M M′ B} {A A′ : Types.Ty (CastTerms.Δᵉ Γᴸ)}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (eq : A ≡ A′)
  → γ CTI.⊢² M ⊑ M′ ∶ p
  → γ CTI.⊢² M ⊑ M′ ∶
      subst (λ T → T ⊑ᵀ⟨ γ ⟩ B) eq p
transport-source-type refl related = related


rename-body-scope-eq : ∀ {Δ Δ′} (ρ : Δ Cons.↪ᵗ Δ′)
    (B : Types.Ty (Nat.suc Δ))
  → Types.renameᵗ (toRenameᵗ (Cons.keep ρ)) B
    ≡ Types.renameᵗ (Types.extᵗ (toRenameᵗ ρ)) B
rename-body-scope-eq ρ B =
  Types.renameᵗ-cong B (toRename-keep-eq ρ)


rename-all-scope-eq : ∀ {Δ Δ′} (ρ : Δ Cons.↪ᵗ Δ′)
    (B : Types.Ty (Nat.suc Δ))
  → `∀ (Types.renameᵗ (toRenameᵗ (Cons.keep ρ)) B)
    ≡ Types.renameᵗ (toRenameᵗ ρ) (`∀ B)
rename-all-scope-eq ρ B = cong `∀ (rename-body-scope-eq ρ B)


rename-open-scope-eq : ∀ {Δ Δ′} (ρ : Δ Cons.↪ᵗ Δ′)
    (B : Types.Ty (Nat.suc Δ)) (A : Types.Ty Δ)
  → Types.renameᵗ (toRenameᵗ (Cons.keep ρ)) B
      [ Types.renameᵗ (toRenameᵗ ρ) A ]ᵗ
    ≡ Types.renameᵗ (toRenameᵗ ρ) (B [ A ]ᵗ)
rename-open-scope-eq ρ B A =
  trans
    (cong (λ T → T [ Types.renameᵗ (toRenameᵗ ρ) A ]ᵗ)
      (rename-body-scope-eq ρ B))
    (sym (rename-openᵗ (toRenameᵗ ρ) B A))


module _
    (transport-target-reveal-rebase :
      TransportSourceBindTargetRevealRebaseᵀ)
    (transport-target-conceal-rebase :
      TransportSourceBindTargetConcealRebaseᵀ)
  where

  transport-source-bind-scope : TransportSourceBindScopeᵀ
  transport-source-bind-scope plan
      (CTI.x⊑x² source-member target-member) =
    CTI.x⊑x²
      (source-member-scope plan source-member) target-member

  transport-source-bind-scope plan
      (CTI.ƛ⊑ƛ² {pA = pA} related) =
    retarget-CTI
      (CTI.ƛ⊑ƛ²
        (transport-source-bind-scope
          (source-scope-term plan pA (source-scope-⊑ᵀ plan pA)) related))

  transport-source-bind-scope plan
      (CTI.·⊑·² {pA = pA} {pB = pB} function-rel argument-rel) =
    CTI.·⊑·²
      (retarget-CTI
        (transport-source-bind-scope plan function-rel))
      (transport-source-bind-scope plan argument-rel)

  transport-source-bind-scope {ρ = ρ} {γ⁺ = γ⁺} plan
      (CTI.Λ⊑Λ² {A = A} {B = B} source-value target-value
        related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (rename-all-scope-eq ρ A)
        (CTI.Λ⊑Λ²
          (renameᵗᵐ-preserves-Value (Cons.keep ρ) source-value)
          target-value
          (transport-source-bind-scope (source-scope-both plan) related)
          renamed-q))
    where
    renamed-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ (`∀ B))
        (sym (rename-all-scope-eq ρ A)) (source-scope-⊑ᵀ plan q)

  transport-source-bind-scope {ρ = ρ} {γ⁺ = γ⁺} plan
      (CTI.Λ⊑² {A = A} {B = B} nonvar occurs source-value
        target-typing related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (rename-all-scope-eq ρ A)
        (CTI.Λ⊑²
          (Types.renameNonVar (toRenameᵗ (Cons.keep ρ)) nonvar)
          (rename-occurs (toRenameᵗ (Cons.keep ρ)) occurs)
          (renameᵗᵐ-preserves-Value (Cons.keep ρ) source-value)
          target-typing
          (transport-source-bind-scope (source-scope-left plan) related)
          renamed-q))
    where
    renamed-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B)
        (sym (rename-all-scope-eq ρ A)) (source-scope-⊑ᵀ plan q)

  transport-source-bind-scope {ρ = ρ} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ related q r) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (rename-open-scope-eq ρ C A)
        (CTI.•⊑•² renamed-p∀ renamed-related renamed-q renamed-r))
    where
    renamed-p∀ =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ `∀ C′)
        (sym (rename-all-scope-eq ρ C)) (source-scope-⊑ᵀ plan p∀)
    renamed-related =
      retarget-CTI
        (transport-source-type {γ = γ⁺} (sym (rename-all-scope-eq ρ C))
          (transport-source-bind-scope plan related))
    renamed-q = source-scope-⊑ᵀ plan q
    renamed-r =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ (C′ [ A′ ]ᵗ))
        (sym (rename-open-scope-eq ρ C A)) (source-scope-⊑ᵀ plan r)

  transport-source-bind-scope {ρ = ρ} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.•⊑² {C = C} {A = A} {B = B} p∀ related q r) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (rename-open-scope-eq ρ C A)
        (CTI.•⊑² renamed-p∀ renamed-related renamed-q renamed-r))
    where
    renamed-p∀ =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B)
        (sym (rename-all-scope-eq ρ C)) (source-scope-⊑ᵀ plan p∀)
    renamed-related =
      retarget-CTI
        (transport-source-type {γ = γ⁺} (sym (rename-all-scope-eq ρ C))
          (transport-source-bind-scope plan related))
    renamed-q = source-scope-⊑ᵀ plan q
    renamed-r =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B)
        (sym (rename-open-scope-eq ρ C A)) (source-scope-⊑ᵀ plan r)

  transport-source-bind-scope plan (CTI.κ⊑κ² (κℕ n) p) =
    CTI.κ⊑κ² (κℕ n) (source-scope-⊑ᵀ plan p)

  transport-source-bind-scope plan (CTI.κ⊑κ² (κ𝔹 b) p) =
    CTI.κ⊑κ² (κ𝔹 b) (source-scope-⊑ᵀ plan p)

  transport-source-bind-scope {ρ = ρ} plan
      (CTI.cast⊑cast² c c′ related q) =
    retarget-CTI
      (CTI.cast⊑cast² (Cons.renameᵐᶜ ρ c) c′
        (transport-source-bind-scope plan related)
        (source-scope-⊑ᵀ plan q))

  transport-source-bind-scope plan (CTI.⊑cast² c′ related q) =
    CTI.⊑cast² c′ (transport-source-bind-scope plan related)
      (source-scope-⊑ᵀ plan q)

  transport-source-bind-scope plan
      (CTI.⊑reveal-identity c′⊢ position related q) =
    CTI.⊑reveal-identity c′⊢ position
      (transport-source-bind-scope plan related)
      (source-scope-⊑ᵀ plan q)

  transport-source-bind-scope plan
      (CTI.⊑conceal-identity c′⊢ position related q) =
    CTI.⊑conceal-identity c′⊢ position
      (transport-source-bind-scope plan related)
      (source-scope-⊑ᵀ plan q)

  transport-source-bind-scope {ρ = ρ} plan
      (CTI.cast⊑² c related q) =
    retarget-CTI
      (CTI.cast⊑² (Cons.renameᵐᶜ ρ c)
        (transport-source-bind-scope plan related)
        (source-scope-⊑ᵀ plan q))

  transport-source-bind-scope {ρ = ρ} plan
      (CTI.reveal⊑-identity c⊢ position related q) =
    retarget-CTI
      (CTI.reveal⊑-identity renamed
        (trans renamed-position position)
        (transport-source-bind-scope plan related)
        (source-scope-⊑ᵀ plan q))
    where
    renamed = reveal-renameᵗ (toRenameᵗ-injective ρ)
      (source-scope-store plan) c⊢
    renamed-position = revealGeneratorPosition-rename
      (toRenameᵗ-injective ρ) (source-scope-store plan) c⊢

  transport-source-bind-scope {ρ = ρ} plan
      (CTI.reveal⊑-only² c⊢ position mark disaligned
        represented related q) =
    retarget-CTI
      (CTI.reveal⊑-only² renamed renamed-active
        (source-scope-source-mark plan mark)
        (source-scope-source-disaligned plan disaligned)
        (source-scope-⊑ᵀ plan represented)
        (transport-source-bind-scope plan related)
        (source-scope-⊑ᵀ plan q))
    where
    renamed = reveal-renameᵗ (toRenameᵗ-injective ρ)
      (source-scope-store plan) c⊢
    renamed-position = revealGeneratorPosition-rename
      (toRenameᵗ-injective ρ) (source-scope-store plan) c⊢
    renamed-active = λ absent → position
      (trans (sym renamed-position) absent)

  transport-source-bind-scope {ρ = ρ} plan
      (CTI.conceal⊑-identity c⊢ position related q) =
    retarget-CTI
      (CTI.conceal⊑-identity renamed
        (trans renamed-position position)
        (transport-source-bind-scope plan related)
        (source-scope-⊑ᵀ plan q))
    where
    renamed = conceal-renameᵗ (toRenameᵗ-injective ρ)
      (source-scope-store plan) c⊢
    renamed-position = concealGeneratorPosition-rename
      (toRenameᵗ-injective ρ) (source-scope-store plan) c⊢

  transport-source-bind-scope {ρ = ρ} plan
      (CTI.conceal⊑-only² c⊢ position mark disaligned
        represented related q) =
    retarget-CTI
      (CTI.conceal⊑-only² renamed renamed-active
        (source-scope-source-mark plan mark)
        (source-scope-source-disaligned plan disaligned)
        (source-scope-⊑ᵀ plan represented)
        (transport-source-bind-scope plan related)
        (source-scope-⊑ᵀ plan q))
    where
    renamed = conceal-renameᵗ (toRenameᵗ-injective ρ)
      (source-scope-store plan) c⊢
    renamed-position = concealGeneratorPosition-rename
      (toRenameᵗ-injective ρ) (source-scope-store plan) c⊢
    renamed-active = λ absent → position
      (trans (sym renamed-position) absent)

  transport-source-bind-scope {ρ = ρ} plan
      (CTI.reveal⊑reveal² c⊢ c′⊢ same-position aligned
        represented related q) =
    retarget-CTI
      (CTI.reveal⊑reveal² renamed c′⊢
        (trans renamed-position same-position)
        (source-scope-aligned plan aligned)
        (source-scope-⊑ᵀ plan represented)
        (transport-source-bind-scope plan related)
        (source-scope-⊑ᵀ plan q))
    where
    renamed = reveal-renameᵗ (toRenameᵗ-injective ρ)
      (source-scope-store plan) c⊢
    renamed-position = revealGeneratorPosition-rename
      (toRenameᵗ-injective ρ) (source-scope-store plan) c⊢

  transport-source-bind-scope {ρ = ρ} plan
      (CTI.conceal⊑conceal² c⊢ c′⊢ same-position aligned
        represented related q) =
    retarget-CTI
      (CTI.conceal⊑conceal² renamed c′⊢
        (trans renamed-position same-position)
        (source-scope-aligned plan aligned)
        (source-scope-⊑ᵀ plan represented)
        (transport-source-bind-scope plan related)
        (source-scope-⊑ᵀ plan q))
    where
    renamed = conceal-renameᵗ (toRenameᵗ-injective ρ)
      (source-scope-store plan) c⊢
    renamed-position = concealGeneratorPosition-rename
      (toRenameᵗ-injective ρ) (source-scope-store plan) c⊢

  transport-source-bind-scope plan
      (CTI.⊑reveal-rebase² c′⊢ ok represented related q) =
    transport-target-reveal-rebase plan c′⊢ ok represented related q

  transport-source-bind-scope plan
      (CTI.⊑conceal-rebase² c′⊢ ok represented related q) =
    transport-target-conceal-rebase
      c′⊢ ok represented related q plan

  transport-source-bind-scope plan (CTI.blame⊑² target-typing p) =
    CTI.blame⊑² target-typing
      (source-scope-⊑ᵀ plan p)

  transport-source-bind-scope plan
      (CTI.⊕⊑⊕² addℕ left-rel right-rel r) =
    CTI.⊕⊑⊕² addℕ
      (transport-source-bind-scope plan left-rel)
      (transport-source-bind-scope plan right-rel)
      (source-scope-⊑ᵀ plan r)

  transport-source-bind-scope plan
      (CTI.⊕⊑⊕² and𝔹 left-rel right-rel r) =
    CTI.⊕⊑⊕² and𝔹
      (transport-source-bind-scope plan left-rel)
      (transport-source-bind-scope plan right-rel)
      (source-scope-⊑ᵀ plan r)

  transport-source-bind : TransportSourceBindᵀ
  transport-source-bind {A = A} {p = p} eqᴸ related =
    retarget-CTI
      (transport-source-type (renameᵗ-wk-eq A)
        (transport-source-bind-scope (source-scope-root eqᴸ) related))
