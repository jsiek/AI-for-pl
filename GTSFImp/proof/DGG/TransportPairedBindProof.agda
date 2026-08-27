{-# OPTIONS --safe #-}

module proof.DGG.TransportPairedBindProof where

-- File Charter:
--   * Proves CTI transport through precise and dynamic paired allocations.
--   * Uses one induction because both roots have the same scope action.
--   * Keeps only source-rebase commutation as module parameters.
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
  (reveal-renameᵗ; conceal-renameᵗ; toRename-keep-eq; toRename-id-eq;
   renameᵗ-wk-eq; rename-openᵗ; rename-occurs;
   renameᵗᵐ-preserves-Value; typing-renameᵗ)
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition; concealGeneratorPosition;
   revealGeneratorPosition-rename; concealGeneratorPosition-rename)
open import proof.DGG.World using
  (_⊑ᶜ_; _⊑ᵀ⟨_⟩_; ηᴸᶜ; ηᴿᶜ; marksᶜ)
open import proof.DGG.TransportTermImprecisionStepDef using
  (TransportPairedBindᵀ; TransportPairedStarBindᵀ)
open import proof.DGG.TransportPairedBindDef using
  ( PairedBindScope
  ; paired-scope-root
  ; paired-star-scope-root
  ; paired-scope-term
  ; paired-scope-both
  ; paired-scope-left
  ; paired-scope-center
  ; paired-scope-left-commutes
  ; paired-scope-right-commutes
  ; paired-scope-mark
  ; paired-scope-source-context
  ; paired-scope-target-context
  ; paired-scope-source-store
  ; paired-scope-target-store
  ; paired-scope-⊑ᵀ
  ; TransportPairedBindScopeᵀ
  ; TransportPairedBindRevealRebaseᵀ
  ; TransportPairedBindConcealRebaseᵀ
  )
import proof.DGG.CastTermImprecision as CTI


paired-source-member : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ} {Σᴸ⁺ : TyStore.TyStore Δᴸ⁺}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴸ⁺ : TC.TermCtx Δᴸ⁺}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ Cons.↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {x} {A : Types.Ty Δᴸ}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → Γᴸ TC.∋ x ⦂ A
  → Γᴸ⁺ TC.∋ x ⦂ Types.renameᵗ (toRenameᵗ ρᴸ) A
paired-source-member {ρᴸ = ρᴸ} plan member =
  subst (λ Γ → Γ TC.∋ _ ⦂ Types.renameᵗ (toRenameᵗ ρᴸ) _)
    (sym (paired-scope-source-context plan))
    (TC.renameᵗ-∋ (toRenameᵗ ρᴸ) member)


paired-target-member : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ} {Σᴸ⁺ : TyStore.TyStore Δᴸ⁺}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴸ⁺ : TC.TermCtx Δᴸ⁺}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ Cons.↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {x} {B : Types.Ty Δᴿ}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → Γᴿ TC.∋ x ⦂ B
  → Γᴿ⁺ TC.∋ x ⦂ Types.renameᵗ (toRenameᵗ ρᴿ) B
paired-target-member {ρᴿ = ρᴿ} plan member =
  subst (λ Γ → Γ TC.∋ _ ⦂ Types.renameᵗ (toRenameᵗ ρᴿ) _)
    (sym (paired-scope-target-context plan))
    (TC.renameᵗ-∋ (toRenameᵗ ρᴿ) member)


paired-target-typing : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ} {Σᴸ⁺ : TyStore.TyStore Δᴸ⁺}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴸ⁺ : TC.TermCtx Δᴸ⁺}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ Cons.↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {M : CastTerms.Term Δᴿ} {B : Types.Ty Δᴿ}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → ⟨ Δᴿ , Σᴿ , Γᴿ ⟩ ⊢ M ⦂ B
  → ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ ⊢ renameᵗᵐ ρᴿ M ⦂
      Types.renameᵗ (toRenameᵗ ρᴿ) B
paired-target-typing plan M⊢ =
  subst (λ Γ → _ ⊢ _ ⦂ _)
    (sym (paired-scope-target-context plan))
    (typing-renameᵗ (paired-scope-target-store plan) M⊢)


paired-scope-aligned : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ} {Σᴸ⁺ : TyStore.TyStore Δᴸ⁺}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴸ⁺ : TC.TermCtx Δᴸ⁺}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ Cons.↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {Xᴸ : Types.TyVar Δᴸ} {Xᴿ : Types.TyVar Δᴿ}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → toRenameᵗ (ηᴸᶜ γ) Xᴸ ≡ toRenameᵗ (ηᴿᶜ γ) Xᴿ
  → toRenameᵗ (ηᴸᶜ γ⁺) (toRenameᵗ ρᴸ Xᴸ)
    ≡ toRenameᵗ (ηᴿᶜ γ⁺) (toRenameᵗ ρᴿ Xᴿ)
paired-scope-aligned plan aligned =
  trans (sym (paired-scope-left-commutes plan _))
    (trans (cong (toRenameᵗ (paired-scope-center plan)) aligned)
      (paired-scope-right-commutes plan _))


paired-scope-source-mark : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ} {Σᴸ⁺ : TyStore.TyStore Δᴸ⁺}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴸ⁺ : TC.TermCtx Δᴸ⁺}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ Cons.↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {Xᴸ : Types.TyVar Δᴸ} {v}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → marksᶜ γ (toRenameᵗ (ηᴸᶜ γ) Xᴸ) ≡ v
  → marksᶜ γ⁺
      (toRenameᵗ (ηᴸᶜ γ⁺) (toRenameᵗ ρᴸ Xᴸ)) ≡ v
paired-scope-source-mark {γ⁺ = γ⁺} {Xᴸ = Xᴸ} plan mark =
  trans
    (cong (marksᶜ γ⁺) (sym (paired-scope-left-commutes plan Xᴸ)))
    (trans (paired-scope-mark plan _) mark)


paired-scope-source-disaligned : ∀
    {Δᴸ Δᴸ⁺ Δᴿ Δᴿ⁺}
    {Σᴸ : TyStore.TyStore Δᴸ} {Σᴸ⁺ : TyStore.TyStore Δᴸ⁺}
    {Σᴿ : TyStore.TyStore Δᴿ} {Σᴿ⁺ : TyStore.TyStore Δᴿ⁺}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴸ⁺ : TC.TermCtx Δᴸ⁺}
    {Γᴿ : TC.TermCtx Δᴿ} {Γᴿ⁺ : TC.TermCtx Δᴿ⁺}
    {ρᴸ : Δᴸ Cons.↪ᵗ Δᴸ⁺} {ρᴿ : Δᴿ Cons.↪ᵗ Δᴿ⁺}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Δᴸ⁺ , Σᴸ⁺ , Γᴸ⁺ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩}
    {Xᴸ : Types.TyVar Δᴸ}
  → (plan : PairedBindScope ρᴸ ρᴿ γ γ⁺)
  → (∀ Xᴿ → toRenameᵗ (ηᴿᶜ γ) Xᴿ
      ≢ toRenameᵗ (ηᴸᶜ γ) Xᴸ)
  → ∀ Xᴿ → toRenameᵗ (ηᴿᶜ γ⁺) Xᴿ
      ≢ toRenameᵗ (ηᴸᶜ γ⁺) (toRenameᵗ ρᴸ Xᴸ)
paired-scope-source-disaligned
    (paired-scope-root represented eqᴸ eqᴿ) free Fin.zero ()
paired-scope-source-disaligned
    {Xᴸ = Xᴸ} (paired-scope-root represented eqᴸ eqᴿ)
    free (Fin.suc Xᴿ) aligned =
  free Xᴿ
    (trans (fin-suc-injective aligned)
      (cong (toRenameᵗ _) (toRename-id-eq Xᴸ)))
paired-scope-source-disaligned
    (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) free
    Fin.zero ()
paired-scope-source-disaligned
    {Xᴸ = Xᴸ}
    (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) free
    (Fin.suc Xᴿ) aligned =
  free Xᴿ
    (trans (fin-suc-injective aligned)
      (cong (toRenameᵗ _) (toRename-id-eq Xᴸ)))
paired-scope-source-disaligned
    (paired-scope-term plan p p⁺) free Xᴿ aligned =
  paired-scope-source-disaligned plan free Xᴿ aligned
paired-scope-source-disaligned {Xᴸ = Fin.zero}
    (paired-scope-both plan) free Xᴿ aligned =
  ⊥-elim (free Fin.zero refl)
paired-scope-source-disaligned {Xᴸ = Fin.suc Xᴸ}
    (paired-scope-both plan) free Fin.zero ()
paired-scope-source-disaligned {Xᴸ = Fin.suc Xᴸ}
    (paired-scope-both plan) free (Fin.suc Xᴿ) aligned =
  paired-scope-source-disaligned plan old-free Xᴿ
    (fin-suc-injective aligned)
  where
  old-free = λ Y eq → free (Fin.suc Y) (cong Fin.suc eq)
paired-scope-source-disaligned {Xᴸ = Fin.zero}
    (paired-scope-left plan) free Xᴿ ()
paired-scope-source-disaligned {Xᴸ = Fin.suc Xᴸ}
    (paired-scope-left plan) free Xᴿ aligned =
  paired-scope-source-disaligned plan old-free Xᴿ
    (fin-suc-injective aligned)
  where
  old-free = λ Y eq → free Y (cong Fin.suc eq)


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
    (transport-reveal-rebase : TransportPairedBindRevealRebaseᵀ)
    (transport-conceal-rebase : TransportPairedBindConcealRebaseᵀ)
  where

  transport-paired-bind-scope : TransportPairedBindScopeᵀ
  transport-paired-bind-scope plan
      (CTI.x⊑x² source-member target-member) =
    CTI.x⊑x² (paired-source-member plan source-member)
      (paired-target-member plan target-member)

  transport-paired-bind-scope plan
      (CTI.ƛ⊑ƛ² {pA = pA} related) =
    retarget-CTI
      (CTI.ƛ⊑ƛ²
        (transport-paired-bind-scope
          (paired-scope-term plan pA (paired-scope-⊑ᵀ plan pA)) related))

  transport-paired-bind-scope plan
      (CTI.·⊑·² {pA = pA} {pB = pB} function-rel argument-rel) =
    CTI.·⊑·²
      (retarget-CTI (transport-paired-bind-scope plan function-rel))
      (transport-paired-bind-scope plan argument-rel)

  transport-paired-bind-scope
      {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} {γ⁺ = γ⁺} plan
      (CTI.Λ⊑Λ² {A = A} {B = B} source-value target-value
        related q) =
    retarget-CTI
      (transport-source-type (rename-all-scope-eq ρᴸ A)
        (transport-target-type (rename-all-scope-eq ρᴿ B)
          (CTI.Λ⊑Λ²
            (renameᵗᵐ-preserves-Value (Cons.keep ρᴸ) source-value)
            (renameᵗᵐ-preserves-Value (Cons.keep ρᴿ) target-value)
            (transport-paired-bind-scope (paired-scope-both plan) related)
            renamed-q)))
    where
    renamed-q =
      subst (λ L → L ⊑ᵀ⟨ γ⁺ ⟩
          (`∀ (Types.renameᵗ (toRenameᵗ (Cons.keep ρᴿ)) B)))
        (sym (rename-all-scope-eq ρᴸ A))
        (subst (λ R → Types.renameᵗ (toRenameᵗ ρᴸ) (`∀ A)
            ⊑ᵀ⟨ γ⁺ ⟩ R)
          (sym (rename-all-scope-eq ρᴿ B))
          (paired-scope-⊑ᵀ plan q))

  transport-paired-bind-scope
      {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} {γ⁺ = γ⁺} plan
      (CTI.Λ⊑² {A = A} {B = B} nonvar occurs source-value
        target-typing related q) =
    retarget-CTI
      (transport-source-type (rename-all-scope-eq ρᴸ A)
        (CTI.Λ⊑²
          (Types.renameNonVar (toRenameᵗ (Cons.keep ρᴸ)) nonvar)
          (rename-occurs (toRenameᵗ (Cons.keep ρᴸ)) occurs)
          (renameᵗᵐ-preserves-Value (Cons.keep ρᴸ) source-value)
          (paired-target-typing plan target-typing)
          (transport-paired-bind-scope (paired-scope-left plan) related)
          renamed-q))
    where
    renamed-q =
      subst (λ L → L ⊑ᵀ⟨ γ⁺ ⟩
          Types.renameᵗ (toRenameᵗ ρᴿ) B)
        (sym (rename-all-scope-eq ρᴸ A))
        (paired-scope-⊑ᵀ plan q)

  transport-paired-bind-scope
      {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} {γ⁺ = γ⁺} plan
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ related q r) =
    retarget-CTI
      (transport-source-type (rename-open-scope-eq ρᴸ C A)
        (transport-target-type (rename-open-scope-eq ρᴿ C′ A′)
          (CTI.•⊑•² renamed-p∀ renamed-related renamed-q renamed-r)))
    where
    renamed-p∀ =
      subst (λ L → L ⊑ᵀ⟨ γ⁺ ⟩
          (`∀ (Types.renameᵗ (toRenameᵗ (Cons.keep ρᴿ)) C′)))
        (sym (rename-all-scope-eq ρᴸ C))
        (subst (λ R → Types.renameᵗ (toRenameᵗ ρᴸ) (`∀ C)
            ⊑ᵀ⟨ γ⁺ ⟩ R)
          (sym (rename-all-scope-eq ρᴿ C′))
          (paired-scope-⊑ᵀ plan p∀))
    renamed-related =
      retarget-CTI
        (transport-source-type (sym (rename-all-scope-eq ρᴸ C))
          (transport-target-type (sym (rename-all-scope-eq ρᴿ C′))
            (transport-paired-bind-scope plan related)))
    renamed-q = paired-scope-⊑ᵀ plan q
    renamed-r =
      subst (λ L → L ⊑ᵀ⟨ γ⁺ ⟩
          (Types.renameᵗ (toRenameᵗ (Cons.keep ρᴿ)) C′
            [ Types.renameᵗ (toRenameᵗ ρᴿ) A′ ]ᵗ))
        (sym (rename-open-scope-eq ρᴸ C A))
        (subst (λ R → Types.renameᵗ (toRenameᵗ ρᴸ) (C [ A ]ᵗ)
            ⊑ᵀ⟨ γ⁺ ⟩ R)
          (sym (rename-open-scope-eq ρᴿ C′ A′))
          (paired-scope-⊑ᵀ plan r))

  transport-paired-bind-scope
      {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} {γ⁺ = γ⁺} plan
      (CTI.•⊑² {C = C} {A = A} {B = B} p∀ related q r) =
    retarget-CTI
      (transport-source-type (rename-open-scope-eq ρᴸ C A)
        (CTI.•⊑² renamed-p∀ renamed-related
          (paired-scope-⊑ᵀ plan q) renamed-r))
    where
    renamed-p∀ =
      subst (λ L → L ⊑ᵀ⟨ γ⁺ ⟩
          Types.renameᵗ (toRenameᵗ ρᴿ) B)
        (sym (rename-all-scope-eq ρᴸ C))
        (paired-scope-⊑ᵀ plan p∀)
    renamed-related =
      retarget-CTI
        (transport-source-type (sym (rename-all-scope-eq ρᴸ C))
          (transport-paired-bind-scope plan related))
    renamed-r =
      subst (λ L → L ⊑ᵀ⟨ γ⁺ ⟩
          Types.renameᵗ (toRenameᵗ ρᴿ) B)
        (sym (rename-open-scope-eq ρᴸ C A))
        (paired-scope-⊑ᵀ plan r)

  transport-paired-bind-scope plan (CTI.κ⊑κ² (κℕ n) p) =
    CTI.κ⊑κ² (κℕ n) (paired-scope-⊑ᵀ plan p)

  transport-paired-bind-scope plan (CTI.κ⊑κ² (κ𝔹 b) p) =
    CTI.κ⊑κ² (κ𝔹 b) (paired-scope-⊑ᵀ plan p)

  transport-paired-bind-scope {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} plan
      (CTI.cast⊑cast² c c′ related q) =
    retarget-CTI
      (CTI.cast⊑cast² (Cons.renameᵐᶜ ρᴸ c) (Cons.renameᵐᶜ ρᴿ c′)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))

  transport-paired-bind-scope {ρᴿ = ρᴿ} plan
      (CTI.⊑cast² c′ related q) =
    retarget-CTI
      (CTI.⊑cast² (Cons.renameᵐᶜ ρᴿ c′)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))

  transport-paired-bind-scope {ρᴿ = ρᴿ} plan
      (CTI.⊑reveal-identity c′⊢ position related q) =
    retarget-CTI
      (CTI.⊑reveal-identity renamed
        (trans renamed-position position)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))
    where
    renamed = reveal-renameᵗ (toRenameᵗ-injective ρᴿ)
      (paired-scope-target-store plan) c′⊢
    renamed-position = revealGeneratorPosition-rename
      (toRenameᵗ-injective ρᴿ) (paired-scope-target-store plan) c′⊢

  transport-paired-bind-scope {ρᴿ = ρᴿ} plan
      (CTI.⊑conceal-identity c′⊢ position related q) =
    retarget-CTI
      (CTI.⊑conceal-identity renamed
        (trans renamed-position position)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))
    where
    renamed = conceal-renameᵗ (toRenameᵗ-injective ρᴿ)
      (paired-scope-target-store plan) c′⊢
    renamed-position = concealGeneratorPosition-rename
      (toRenameᵗ-injective ρᴿ) (paired-scope-target-store plan) c′⊢

  transport-paired-bind-scope {ρᴸ = ρᴸ} plan
      (CTI.cast⊑² c related q) =
    retarget-CTI
      (CTI.cast⊑² (Cons.renameᵐᶜ ρᴸ c)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))

  transport-paired-bind-scope {ρᴸ = ρᴸ} plan
      (CTI.reveal⊑-identity c⊢ position related q) =
    retarget-CTI
      (CTI.reveal⊑-identity renamed
        (trans renamed-position position)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))
    where
    renamed = reveal-renameᵗ (toRenameᵗ-injective ρᴸ)
      (paired-scope-source-store plan) c⊢
    renamed-position = revealGeneratorPosition-rename
      (toRenameᵗ-injective ρᴸ) (paired-scope-source-store plan) c⊢

  transport-paired-bind-scope {ρᴸ = ρᴸ} plan
      (CTI.reveal⊑-only² c⊢ position mark disaligned
        represented related q) =
    retarget-CTI
      (CTI.reveal⊑-only² renamed renamed-active
        (paired-scope-source-mark plan mark)
        (paired-scope-source-disaligned plan disaligned)
        (paired-scope-⊑ᵀ plan represented)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))
    where
    renamed = reveal-renameᵗ (toRenameᵗ-injective ρᴸ)
      (paired-scope-source-store plan) c⊢
    renamed-position = revealGeneratorPosition-rename
      (toRenameᵗ-injective ρᴸ) (paired-scope-source-store plan) c⊢
    renamed-active = λ absent → position
      (trans (sym renamed-position) absent)

  transport-paired-bind-scope {ρᴸ = ρᴸ} plan
      (CTI.conceal⊑-identity c⊢ position related q) =
    retarget-CTI
      (CTI.conceal⊑-identity renamed
        (trans renamed-position position)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))
    where
    renamed = conceal-renameᵗ (toRenameᵗ-injective ρᴸ)
      (paired-scope-source-store plan) c⊢
    renamed-position = concealGeneratorPosition-rename
      (toRenameᵗ-injective ρᴸ) (paired-scope-source-store plan) c⊢

  transport-paired-bind-scope {ρᴸ = ρᴸ} plan
      (CTI.conceal⊑-only² c⊢ position mark disaligned
        represented related q) =
    retarget-CTI
      (CTI.conceal⊑-only² renamed renamed-active
        (paired-scope-source-mark plan mark)
        (paired-scope-source-disaligned plan disaligned)
        (paired-scope-⊑ᵀ plan represented)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))
    where
    renamed = conceal-renameᵗ (toRenameᵗ-injective ρᴸ)
      (paired-scope-source-store plan) c⊢
    renamed-position = concealGeneratorPosition-rename
      (toRenameᵗ-injective ρᴸ) (paired-scope-source-store plan) c⊢
    renamed-active = λ absent → position
      (trans (sym renamed-position) absent)

  transport-paired-bind-scope {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} plan
      (CTI.reveal⊑reveal² c⊢ c′⊢ same-position aligned
        represented related q) =
    retarget-CTI
      (CTI.reveal⊑reveal² renamed-source renamed-target
        (trans source-position
          (trans same-position (sym target-position)))
        (paired-scope-aligned plan aligned)
        (paired-scope-⊑ᵀ plan represented)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))
    where
    renamed-source = reveal-renameᵗ (toRenameᵗ-injective ρᴸ)
      (paired-scope-source-store plan) c⊢
    renamed-target = reveal-renameᵗ (toRenameᵗ-injective ρᴿ)
      (paired-scope-target-store plan) c′⊢
    source-position = revealGeneratorPosition-rename
      (toRenameᵗ-injective ρᴸ) (paired-scope-source-store plan) c⊢
    target-position = revealGeneratorPosition-rename
      (toRenameᵗ-injective ρᴿ) (paired-scope-target-store plan) c′⊢

  transport-paired-bind-scope {ρᴸ = ρᴸ} {ρᴿ = ρᴿ} plan
      (CTI.conceal⊑conceal² c⊢ c′⊢ same-position aligned
        represented related q) =
    retarget-CTI
      (CTI.conceal⊑conceal² renamed-source renamed-target
        (trans source-position
          (trans same-position (sym target-position)))
        (paired-scope-aligned plan aligned)
        (paired-scope-⊑ᵀ plan represented)
        (transport-paired-bind-scope plan related)
        (paired-scope-⊑ᵀ plan q))
    where
    renamed-source = conceal-renameᵗ (toRenameᵗ-injective ρᴸ)
      (paired-scope-source-store plan) c⊢
    renamed-target = conceal-renameᵗ (toRenameᵗ-injective ρᴿ)
      (paired-scope-target-store plan) c′⊢
    source-position = concealGeneratorPosition-rename
      (toRenameᵗ-injective ρᴸ) (paired-scope-source-store plan) c⊢
    target-position = concealGeneratorPosition-rename
      (toRenameᵗ-injective ρᴿ) (paired-scope-target-store plan) c′⊢

  transport-paired-bind-scope plan
      (CTI.⊑reveal-rebase² c′⊢ rebase related q) =
    transport-reveal-rebase plan c′⊢ rebase related q

  transport-paired-bind-scope plan
      (CTI.⊑conceal-rebase² c′⊢ rebase related q) =
    transport-conceal-rebase c′⊢ rebase related q plan

  transport-paired-bind-scope plan (CTI.blame⊑² target-typing p) =
    CTI.blame⊑² (paired-target-typing plan target-typing)
      (paired-scope-⊑ᵀ plan p)

  transport-paired-bind-scope plan
      (CTI.⊕⊑⊕² addℕ left-rel right-rel r) =
    CTI.⊕⊑⊕² addℕ
      (transport-paired-bind-scope plan left-rel)
      (transport-paired-bind-scope plan right-rel)
      (paired-scope-⊑ᵀ plan r)

  transport-paired-bind-scope plan
      (CTI.⊕⊑⊕² and𝔹 left-rel right-rel r) =
    CTI.⊕⊑⊕² and𝔹
      (transport-paired-bind-scope plan left-rel)
      (transport-paired-bind-scope plan right-rel)
      (paired-scope-⊑ᵀ plan r)

  transport-paired-bind : TransportPairedBindᵀ
  transport-paired-bind {A = A} {B = B}
      represented eqᴸ eqᴿ related =
    retarget-CTI
      (transport-source-type (renameᵗ-wk-eq A)
        (transport-target-type (renameᵗ-wk-eq B)
          (transport-paired-bind-scope
            (paired-scope-root represented eqᴸ eqᴿ) related)))

  transport-paired-star-bind : TransportPairedStarBindᵀ
  transport-paired-star-bind {A = A} {B = B}
      represented A≢★ eqᴸ eqᴿ related =
    retarget-CTI
      (transport-source-type (renameᵗ-wk-eq A)
        (transport-target-type (renameᵗ-wk-eq B)
          (transport-paired-bind-scope
            (paired-star-scope-root represented A≢★ eqᴸ eqᴿ) related)))
