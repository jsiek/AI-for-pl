{-# OPTIONS --safe #-}

module proof.DGG.TransportTargetBindProof where

-- File Charter:
--   * Proves transport of every cast-term-imprecision constructor through a
--     target-only runtime allocation.
--   * Keeps only the genuine source-rebase commutation lemmas as module
--     parameters once their exact statements have been identified.
--   * Contains no compatibility world, classifier, or result wrapper.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; subst; cong)

import TermCtx as TC
import TyStore
open import Types using (`∀; _[_]ᵗ)
open import Consistency using (toRenameᵗ)
import Consistency as Cons
open import CastTerms using (Ctx; ⟨_,_,_⟩; _⊢_⦂_; renameᵗᵐ)
open import Primitives using (κℕ; κ𝔹; addℕ; and𝔹)
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (fin-suc-injective; toRenameᵗ-injective)
open import proof.TypeInTermSubst using
  (reveal-renameᵗ; conceal-renameᵗ; toRename-keep-eq;
   renameᵗ-wk-eq; rename-openᵗ; renameᵗᵐ-preserves-Value;
   typing-renameᵗ)
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition; concealGeneratorPosition;
   revealGeneratorPosition-rename; concealGeneratorPosition-rename)
open import proof.DGG.World using
  (_⊑ᶜ_; _⊑ᵀ⟨_⟩_; ηᴸᶜ; ηᴿᶜ; marksᶜ; toRenameⁱ)
open import proof.DGG.TransportTermImprecisionStepDef using
  (TransportTargetBindᵀ)
open import proof.DGG.TransportTargetBindDef using
  ( TargetBindScope
  ; target-scope-root
  ; target-scope-term
  ; target-scope-both
  ; target-scope-left
  ; target-scope-center
  ; target-scope-left-commutes
  ; target-scope-right-commutes
  ; target-scope-mark
  ; target-scope-context
  ; target-scope-store
  ; target-scope-⊑ᵀ
  ; TransportTargetBindScopeᵀ
  ; TransportTargetBindRevealRebaseᵀ
  ; TransportTargetBindConcealRebaseᵀ
  )
import proof.DGG.CastTermImprecision as CTI


target-member-scope : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {x} {B : Types.Ty Δᴿ}
  → (plan : TargetBindScope ρ γ γ⁺)
  → Γᴿ TC.∋ x ⦂ B
  → Γᴿ⁺ TC.∋ x ⦂ Types.renameᵗ (toRenameᵗ ρ) B
target-member-scope {ρ = ρ} plan member =
  subst (λ Γ → Γ TC.∋ _ ⦂ Types.renameᵗ (toRenameᵗ ρ) _)
    (sym (target-scope-context plan))
    (TC.renameᵗ-∋ (toRenameᵗ ρ) member)


target-typing-scope : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {M : CastTerms.Term Δᴿ} {B : Types.Ty Δᴿ}
  → (plan : TargetBindScope ρ γ γ⁺)
  → ⟨ Δᴿ , Σᴿ , Γᴿ ⟩ ⊢ M ⦂ B
  → ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ ⊢
      renameᵗᵐ ρ M ⦂ Types.renameᵗ (toRenameᵗ ρ) B
target-typing-scope plan M⊢ =
  subst (λ Γ → _ ⊢ _ ⦂ _)
    (sym (target-scope-context plan))
    (typing-renameᵗ (target-scope-store plan) M⊢)


target-scope-aligned : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {Xᴸ : Types.TyVar Δᴸ} {Xᴿ : Types.TyVar Δᴿ}
  → (plan : TargetBindScope ρ γ γ⁺)
  → toRenameⁱ (ηᴸᶜ γ) Xᴸ ≡ toRenameⁱ (ηᴿᶜ γ) Xᴿ
  → toRenameⁱ (ηᴸᶜ γ⁺) Xᴸ
    ≡ toRenameⁱ (ηᴿᶜ γ⁺) (toRenameᵗ ρ Xᴿ)
target-scope-aligned plan aligned =
  trans (sym (target-scope-left-commutes plan _))
    (trans (cong (toRenameᵗ (target-scope-center plan)) aligned)
      (target-scope-right-commutes plan _))


target-scope-source-mark : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {Xᴸ : Types.TyVar Δᴸ} {v}
  → (plan : TargetBindScope ρ γ γ⁺)
  → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) Xᴸ) ≡ v
  → marksᶜ γ⁺ (toRenameⁱ (ηᴸᶜ γ⁺) Xᴸ) ≡ v
target-scope-source-mark {γ⁺ = γ⁺} {Xᴸ = Xᴸ} plan mark =
  trans
    (cong (marksᶜ γ⁺) (sym (target-scope-left-commutes plan Xᴸ)))
    (trans (target-scope-mark plan _) mark)


target-scope-source-disaligned : ∀
    {Δᴸ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {Xᴸ : Types.TyVar Δᴸ}
  → (plan : TargetBindScope ρ γ γ⁺)
  → (∀ Xᴿ → toRenameⁱ (ηᴿᶜ γ) Xᴿ
      ≢ toRenameⁱ (ηᴸᶜ γ) Xᴸ)
  → ∀ Xᴿ → toRenameⁱ (ηᴿᶜ γ⁺) Xᴿ
      ≢ toRenameⁱ (ηᴸᶜ γ⁺) Xᴸ
target-scope-source-disaligned
    (target-scope-root fresh eqᴿ) free Fin.zero ()
target-scope-source-disaligned
    (target-scope-root fresh eqᴿ) free (Fin.suc Xᴿ) aligned =
  free Xᴿ (fin-suc-injective aligned)
target-scope-source-disaligned
    (target-scope-term plan p p⁺) free Xᴿ aligned =
  target-scope-source-disaligned plan free Xᴿ aligned
target-scope-source-disaligned {Xᴸ = Fin.zero}
    (target-scope-both plan) free Xᴿ aligned =
  ⊥-elim (free Fin.zero refl)
target-scope-source-disaligned {Xᴸ = Fin.suc Xᴸ}
    (target-scope-both plan) free Fin.zero ()
target-scope-source-disaligned {Xᴸ = Fin.suc Xᴸ}
    (target-scope-both plan) free (Fin.suc Xᴿ) aligned =
  target-scope-source-disaligned plan old-free Xᴿ
    (fin-suc-injective aligned)
  where
  old-free = λ Y eq → free (Fin.suc Y) (cong Fin.suc eq)
target-scope-source-disaligned {Xᴸ = Fin.zero}
    (target-scope-left plan) free Xᴿ ()
target-scope-source-disaligned {Xᴸ = Fin.suc Xᴸ}
    (target-scope-left plan) free Xᴿ aligned =
  target-scope-source-disaligned plan old-free Xᴿ
    (fin-suc-injective aligned)
  where
  old-free = λ Y eq → free Y (cong Fin.suc eq)


retarget-CTI : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M M′ A B} {p q : A ⊑ᵀ⟨ γ ⟩ B}
  → γ CTI.⊢² M ⊑ M′ ∶ p
  → γ CTI.⊢² M ⊑ M′ ∶ q
retarget-CTI {p = p} {q = q} related =
  subst (λ r → _ CTI.⊢² _ ⊑ _ ∶ r) (PI.⊑-unique p q) related


transport-target-type : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M M′ A} {B B′ : Types.Ty (CastTerms.Δᵉ Γᴿ)}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → (eq : B ≡ B′)
  → γ CTI.⊢² M ⊑ M′ ∶ p
  → γ CTI.⊢² M ⊑ M′ ∶
      subst (λ T → A ⊑ᵀ⟨ γ ⟩ T) eq p
transport-target-type refl related = related


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
    (transport-reveal-rebase : TransportTargetBindRevealRebaseᵀ)
    (transport-conceal-rebase : TransportTargetBindConcealRebaseᵀ)
  where

  transport-target-bind-scope : TransportTargetBindScopeᵀ
  transport-target-bind-scope plan
      (CTI.x⊑x² source-member target-member) =
    CTI.x⊑x² source-member
      (target-member-scope plan target-member)

  transport-target-bind-scope plan
      (CTI.ƛ⊑ƛ² {pA = pA} related) =
    retarget-CTI
      (CTI.ƛ⊑ƛ²
        (transport-target-bind-scope
          (target-scope-term plan pA (target-scope-⊑ᵀ plan pA)) related))

  transport-target-bind-scope plan
      (CTI.·⊑·² {pA = pA} {pB = pB} function-rel argument-rel) =
    CTI.·⊑·²
      (retarget-CTI
        (transport-target-bind-scope plan function-rel))
      (transport-target-bind-scope plan argument-rel)

  transport-target-bind-scope {ρ = ρ} {γ⁺ = γ⁺} plan
      (CTI.Λ⊑Λ² {A = A} {B = B} source-value target-value
        related q) =
    retarget-CTI
      (transport-target-type {γ = γ⁺} (rename-all-scope-eq ρ B)
        (CTI.Λ⊑Λ² source-value
          (renameᵗᵐ-preserves-Value (Cons.keep ρ) target-value)
          (transport-target-bind-scope (target-scope-both plan) related)
          renamed-q))
    where
    renamed-q =
      subst (λ T → (`∀ A) ⊑ᵀ⟨ γ⁺ ⟩ T)
        (sym (rename-all-scope-eq ρ B)) (target-scope-⊑ᵀ plan q)

  transport-target-bind-scope {γ⁺ = γ⁺} plan
      (CTI.Λ⊑² nonvar occurs source-value target-typing related q) =
    retarget-CTI
      (CTI.Λ⊑² nonvar occurs source-value
        (target-typing-scope plan target-typing)
        (transport-target-bind-scope (target-scope-left plan) related)
        (target-scope-⊑ᵀ plan q))

  transport-target-bind-scope {ρ = ρ} {γ⁺ = γ⁺} plan
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ related q r) =
    retarget-CTI
      (transport-target-type {γ = γ⁺}
        (rename-open-scope-eq ρ C′ A′)
        (CTI.•⊑•² renamed-p∀ renamed-related renamed-q renamed-r))
    where
    renamed-p∀ =
      subst (λ T → (`∀ C) ⊑ᵀ⟨ γ⁺ ⟩ T)
        (sym (rename-all-scope-eq ρ C′)) (target-scope-⊑ᵀ plan p∀)
    renamed-related =
      retarget-CTI
        (transport-target-type {γ = γ⁺} (sym (rename-all-scope-eq ρ C′))
          (transport-target-bind-scope plan related))
    renamed-q = target-scope-⊑ᵀ plan q
    renamed-r =
      subst (λ T → (C [ A ]ᵗ) ⊑ᵀ⟨ γ⁺ ⟩ T)
        (sym (rename-open-scope-eq ρ C′ A′))
        (target-scope-⊑ᵀ plan r)

  transport-target-bind-scope plan
      (CTI.•⊑² p∀ related q r) =
    CTI.•⊑² (target-scope-⊑ᵀ plan p∀)
      (transport-target-bind-scope plan related)
      (target-scope-⊑ᵀ plan q) (target-scope-⊑ᵀ plan r)

  transport-target-bind-scope plan (CTI.κ⊑κ² (κℕ n) p) =
    CTI.κ⊑κ² (κℕ n) (target-scope-⊑ᵀ plan p)

  transport-target-bind-scope plan (CTI.κ⊑κ² (κ𝔹 b) p) =
    CTI.κ⊑κ² (κ𝔹 b) (target-scope-⊑ᵀ plan p)

  transport-target-bind-scope {ρ = ρ} plan
      (CTI.cast⊑cast² c c′ related q) =
    retarget-CTI
      (CTI.cast⊑cast² c (Cons.renameᵐᶜ ρ c′)
        (transport-target-bind-scope plan related)
        (target-scope-⊑ᵀ plan q))

  transport-target-bind-scope {ρ = ρ} plan
      (CTI.⊑cast² c′ related q) =
    retarget-CTI
      (CTI.⊑cast² (Cons.renameᵐᶜ ρ c′)
        (transport-target-bind-scope plan related)
        (target-scope-⊑ᵀ plan q))

  transport-target-bind-scope {ρ = ρ} plan
      (CTI.⊑reveal-identity c′⊢ position related q) =
    retarget-CTI
      (CTI.⊑reveal-identity renamed
        (trans renamed-position position)
        (transport-target-bind-scope plan related)
        (target-scope-⊑ᵀ plan q))
    where
    renamed = reveal-renameᵗ (toRenameᵗ-injective ρ)
      (target-scope-store plan) c′⊢
    renamed-position = revealGeneratorPosition-rename
      (toRenameᵗ-injective ρ) (target-scope-store plan) c′⊢

  transport-target-bind-scope {ρ = ρ} plan
      (CTI.⊑conceal-identity c′⊢ position related q) =
    retarget-CTI
      (CTI.⊑conceal-identity renamed
        (trans renamed-position position)
        (transport-target-bind-scope plan related)
        (target-scope-⊑ᵀ plan q))
    where
    renamed = conceal-renameᵗ (toRenameᵗ-injective ρ)
      (target-scope-store plan) c′⊢
    renamed-position = concealGeneratorPosition-rename
      (toRenameᵗ-injective ρ) (target-scope-store plan) c′⊢

  transport-target-bind-scope plan (CTI.cast⊑² c related q) =
    CTI.cast⊑² c (transport-target-bind-scope plan related)
      (target-scope-⊑ᵀ plan q)

  transport-target-bind-scope plan
      (CTI.reveal⊑-identity c⊢ position related q) =
    CTI.reveal⊑-identity c⊢ position
      (transport-target-bind-scope plan related)
      (target-scope-⊑ᵀ plan q)

  transport-target-bind-scope plan
      (CTI.reveal⊑-only² c⊢ position mark disaligned
        represented related q) =
    CTI.reveal⊑-only² c⊢ position
      (target-scope-source-mark plan mark)
      (target-scope-source-disaligned plan disaligned)
      (target-scope-⊑ᵀ plan represented)
      (transport-target-bind-scope plan related)
      (target-scope-⊑ᵀ plan q)

  transport-target-bind-scope plan
      (CTI.conceal⊑-identity c⊢ position related q) =
    CTI.conceal⊑-identity c⊢ position
      (transport-target-bind-scope plan related)
      (target-scope-⊑ᵀ plan q)

  transport-target-bind-scope plan
      (CTI.conceal⊑-only² c⊢ position mark disaligned
        represented related q) =
    CTI.conceal⊑-only² c⊢ position
      (target-scope-source-mark plan mark)
      (target-scope-source-disaligned plan disaligned)
      (target-scope-⊑ᵀ plan represented)
      (transport-target-bind-scope plan related)
      (target-scope-⊑ᵀ plan q)

  transport-target-bind-scope {ρ = ρ} plan
      (CTI.reveal⊑reveal² c⊢ c′⊢ same-position aligned
        represented related q) =
    retarget-CTI
      (CTI.reveal⊑reveal² c⊢ renamed
        (trans same-position (sym renamed-position))
        (target-scope-aligned plan aligned)
        (target-scope-⊑ᵀ plan represented)
        (transport-target-bind-scope plan related)
        (target-scope-⊑ᵀ plan q))
    where
    renamed = reveal-renameᵗ (toRenameᵗ-injective ρ)
      (target-scope-store plan) c′⊢
    renamed-position = revealGeneratorPosition-rename
      (toRenameᵗ-injective ρ) (target-scope-store plan) c′⊢

  transport-target-bind-scope {ρ = ρ} plan
      (CTI.conceal⊑conceal² c⊢ c′⊢ same-position aligned
        represented related q) =
    retarget-CTI
      (CTI.conceal⊑conceal² c⊢ renamed
        (trans same-position (sym renamed-position))
        (target-scope-aligned plan aligned)
        (target-scope-⊑ᵀ plan represented)
        (transport-target-bind-scope plan related)
        (target-scope-⊑ᵀ plan q))
    where
    renamed = conceal-renameᵗ (toRenameᵗ-injective ρ)
      (target-scope-store plan) c′⊢
    renamed-position = concealGeneratorPosition-rename
      (toRenameᵗ-injective ρ) (target-scope-store plan) c′⊢

  transport-target-bind-scope plan
      (CTI.⊑reveal-rebase² c′⊢ rebase related q) =
    transport-reveal-rebase plan c′⊢ rebase related q

  transport-target-bind-scope plan
      (CTI.⊑conceal-rebase² c′⊢ rebase related q) =
    transport-conceal-rebase c′⊢ rebase related q plan

  transport-target-bind-scope plan (CTI.blame⊑² target-typing p) =
    CTI.blame⊑² (target-typing-scope plan target-typing)
      (target-scope-⊑ᵀ plan p)

  transport-target-bind-scope plan
      (CTI.⊕⊑⊕² addℕ left-rel right-rel r) =
    CTI.⊕⊑⊕² addℕ
      (transport-target-bind-scope plan left-rel)
      (transport-target-bind-scope plan right-rel)
      (target-scope-⊑ᵀ plan r)

  transport-target-bind-scope plan
      (CTI.⊕⊑⊕² and𝔹 left-rel right-rel r) =
    CTI.⊕⊑⊕² and𝔹
      (transport-target-bind-scope plan left-rel)
      (transport-target-bind-scope plan right-rel)
      (target-scope-⊑ᵀ plan r)

  transport-target-bind : TransportTargetBindᵀ
  transport-target-bind {B = B} fresh eqᴿ related =
    retarget-CTI
      (transport-target-type (renameᵗ-wk-eq B)
        (transport-target-bind-scope
          (target-scope-root fresh eqᴿ) related))
