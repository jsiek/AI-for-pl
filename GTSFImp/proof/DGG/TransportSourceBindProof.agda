{-# OPTIONS --safe #-}

module proof.DGG.TransportSourceBindProof where

-- File Charter:
--   * Proves transport of every cast-term-imprecision constructor through a
--     source-only runtime allocation.
--   * Keeps genuine scope and source-rebase commutation lemmas as module
--     parameters once their exact statements have been identified.
--   * Contains no compatibility world, classifier, or result wrapper.

import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; subst; cong)

import TermCtx as TC
import TyStore
import Conversion
open import Types using (⇑ᵗ; `∀; _[_]ᵗ)
open import Consistency using (toRenameᵗ)
import Consistency as Cons
open import CastTerms using (Ctx; ⇑ᵗᵐ)
open import Primitives using (κℕ; κ𝔹; addℕ; and𝔹)
open import Reduction using (bind; []; _∷_)
import proof.Reduction as PR
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (fin-suc-injective; toRenameᵗ-injective)
open import proof.TypeInTermSubst using
  (StoreRename-wk-bind; reveal-renameᵗ; conceal-renameᵗ;
   toRename-wk-eq; renameᵗ-wk-eq; rename-openᵗ)
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition; concealGeneratorPosition;
   revealGeneratorPosition-rename; concealGeneratorPosition-rename)
open import proof.DGG.WorldEvolution using
  ( evolution-bind-left
  ; evolution-⊑ᵀ
  ; evolution-aligned
  ; evolution-source-mark
  ; evolution-source-disaligned
  )
open import proof.DGG.World using
  (_⊑ᶜ_; _⊑ᵀ⟨_⟩_; ηᴸᶜ; ηᴿᶜ; marksᶜ)
open import proof.DGG.TransportTermImprecisionStepDef using
  (TransportSourceBindᵀ)
open import proof.DGG.TransportSourceBindDef using
  ( SourceBindThroughTerms
  ; source-bind-root
  ; source-bind-term
  ; source-bind-⊑ᵀ
  ; TransportSourceBindThroughTermsᵀ
  ; TransportSourceBindTypeLambdaᵀ
  ; TransportSourceBindSourceLambdaᵀ
  ; TransportSourceBindTargetRevealRebaseᵀ
  ; TransportSourceBindTargetConcealRebaseᵀ
  )
import proof.DGG.CastTermImprecision as CTI


source-member-bind : ∀
    {Δ} {Γ : TC.TermCtx Δ} {Γ⁺ : TC.TermCtx (Nat.suc Δ)}
    {A : Types.Ty Δ} {x}
  → Γ⁺ ≡ TC.⇑ᶜ Γ
  → Γ TC.∋ x ⦂ A
  → Γ⁺ TC.∋ x ⦂ ⇑ᵗ A
source-member-bind eq member =
  subst (λ Ψ → Ψ TC.∋ _ ⦂ ⇑ᵗ _) (sym eq)
    (TC.renameᵗ-∋ Fin.suc member)


source-member-through-terms : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore.TyStore Δᴸ}
    {Σᴿ : TyStore.TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {Γᴸ⁺ : TC.TermCtx (Nat.suc Δᴸ)} {C : Types.Ty Δᴸ}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Nat.suc Δᴸ , TyStore.store-bind Σᴸ C , Γᴸ⁺ ⟩
      ⊑ᶜ CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {x} {A : Types.Ty Δᴸ}
  → SourceBindThroughTerms γ γ⁺
  → Γᴸ TC.∋ x ⦂ A
  → Γᴸ⁺ TC.∋ x ⦂ ⇑ᵗ A
source-member-through-terms (source-bind-root eqᴸ) member =
  source-member-bind eqᴸ member
source-member-through-terms
    (source-bind-term plan p p⁺) TC.Z = TC.Z
source-member-through-terms
    (source-bind-term plan p p⁺) (TC.S member) =
  TC.S (source-member-through-terms plan member)


source-bind-aligned : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore.TyStore Δᴸ}
    {Σᴿ : TyStore.TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {Γᴸ⁺ : TC.TermCtx (Nat.suc Δᴸ)} {C : Types.Ty Δᴸ}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Nat.suc Δᴸ , TyStore.store-bind Σᴸ C , Γᴸ⁺ ⟩
      ⊑ᶜ CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴸ : Types.TyVar Δᴸ} {Xᴿ : Types.TyVar Δᴿ}
  → SourceBindThroughTerms γ γ⁺
  → toRenameᵗ (ηᴸᶜ γ) Xᴸ ≡ toRenameᵗ (ηᴿᶜ γ) Xᴿ
  → toRenameᵗ (ηᴸᶜ γ⁺) (Fin.suc Xᴸ)
    ≡ toRenameᵗ (ηᴿᶜ γ⁺) Xᴿ
source-bind-aligned {C = C} {γ = γ}
    (source-bind-root eqᴸ) aligned =
  evolution-aligned
    (evolution-bind-left {A = C} {W = γ} eqᴸ) aligned
source-bind-aligned (source-bind-term plan p p⁺) aligned =
  source-bind-aligned plan aligned


source-bind-source-mark : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore.TyStore Δᴸ}
    {Σᴿ : TyStore.TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {Γᴸ⁺ : TC.TermCtx (Nat.suc Δᴸ)} {C : Types.Ty Δᴸ}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Nat.suc Δᴸ , TyStore.store-bind Σᴸ C , Γᴸ⁺ ⟩
      ⊑ᶜ CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴸ : Types.TyVar Δᴸ} {v}
  → SourceBindThroughTerms γ γ⁺
  → marksᶜ γ (toRenameᵗ (ηᴸᶜ γ) Xᴸ) ≡ v
  → marksᶜ γ⁺ (toRenameᵗ (ηᴸᶜ γ⁺) (Fin.suc Xᴸ)) ≡ v
source-bind-source-mark {C = C} {γ = γ}
    (source-bind-root eqᴸ) mark =
  evolution-source-mark
    (evolution-bind-left {A = C} {W = γ} eqᴸ) mark
source-bind-source-mark (source-bind-term plan p p⁺) mark =
  source-bind-source-mark plan mark


source-bind-source-disaligned : ∀
    {Δᴸ Δᴿ} {Σᴸ : TyStore.TyStore Δᴸ}
    {Σᴿ : TyStore.TyStore Δᴿ}
    {Γᴸ : TC.TermCtx Δᴸ} {Γᴿ : TC.TermCtx Δᴿ}
    {Γᴸ⁺ : TC.TermCtx (Nat.suc Δᴸ)} {C : Types.Ty Δᴸ}
    {γ : CastTerms.⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ
      CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {γ⁺ : CastTerms.⟨ Nat.suc Δᴸ , TyStore.store-bind Σᴸ C , Γᴸ⁺ ⟩
      ⊑ᶜ CastTerms.⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {Xᴸ : Types.TyVar Δᴸ}
  → SourceBindThroughTerms γ γ⁺
  → (∀ Xᴿ → toRenameᵗ (ηᴿᶜ γ) Xᴿ
      ≢ toRenameᵗ (ηᴸᶜ γ) Xᴸ)
  → ∀ Xᴿ → toRenameᵗ (ηᴿᶜ γ⁺) Xᴿ
      ≢ toRenameᵗ (ηᴸᶜ γ⁺) (Fin.suc Xᴸ)
source-bind-source-disaligned {C = C} {γ = γ}
    (source-bind-root eqᴸ) free =
  evolution-source-disaligned
    (evolution-bind-left {A = C} {W = γ} eqᴸ) free
source-bind-source-disaligned
    (source-bind-term plan p p⁺) free =
  source-bind-source-disaligned plan free


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


reveal-index-transport : ∀ {Δ} {Σ : TyStore.TyStore Δ}
    {X X′ : Types.TyVar Δ} {R R′ A B : Types.Ty Δ}
    {c : Conversion.Conv↑ Δ A B}
  → X ≡ X′
  → R ≡ R′
  → Σ Conversion.⊢↑[ X ⦂ R ] c
  → Σ Conversion.⊢↑[ X′ ⦂ R′ ] c
reveal-index-transport refl refl c⊢ = c⊢


reveal-index-transport-position : ∀ {Δ} {Σ : TyStore.TyStore Δ}
    {X X′ : Types.TyVar Δ} {R R′ A B : Types.Ty Δ}
    {c : Conversion.Conv↑ Δ A B}
  → (eqX : X ≡ X′)
  → (eqR : R ≡ R′)
  → (c⊢ : Σ Conversion.⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (reveal-index-transport eqX eqR c⊢)
      ≡ revealGeneratorPosition c⊢
reveal-index-transport-position refl refl c⊢ = refl


conceal-index-transport : ∀ {Δ} {Σ : TyStore.TyStore Δ}
    {X X′ : Types.TyVar Δ} {R R′ A B : Types.Ty Δ}
    {c : Conversion.Conv↓ Δ A B}
  → X ≡ X′
  → R ≡ R′
  → Σ Conversion.⊢↓[ X ⦂ R ] c
  → Σ Conversion.⊢↓[ X′ ⦂ R′ ] c
conceal-index-transport refl refl c⊢ = c⊢


conceal-index-transport-position : ∀ {Δ} {Σ : TyStore.TyStore Δ}
    {X X′ : Types.TyVar Δ} {R R′ A B : Types.Ty Δ}
    {c : Conversion.Conv↓ Δ A B}
  → (eqX : X ≡ X′)
  → (eqR : R ≡ R′)
  → (c⊢ : Σ Conversion.⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (conceal-index-transport eqX eqR c⊢)
      ≡ concealGeneratorPosition c⊢
conceal-index-transport-position refl refl c⊢ = refl


shift-reveal-typing : ∀ {Δ} {Σ : TyStore.TyStore Δ} {C}
    {X : Types.TyVar Δ} {R A B : Types.Ty Δ}
    {c : Conversion.Conv↑ Δ A B}
  → Σ Conversion.⊢↑[ X ⦂ R ] c
  → TyStore.store-bind Σ C Conversion.⊢↑[
      Fin.suc X ⦂ ⇑ᵗ R ] Conversion.rename↑ (toRenameᵗ Cons.wk↪ᵗ) c
shift-reveal-typing {X = X} {R = R} c⊢ =
  reveal-index-transport
    (toRename-wk-eq X) (renameᵗ-wk-eq R)
    (reveal-renameᵗ (toRenameᵗ-injective Cons.wk↪ᵗ)
      StoreRename-wk-bind c⊢)


shift-reveal-position : ∀ {Δ} {Σ : TyStore.TyStore Δ} {C}
    {X : Types.TyVar Δ} {R A B : Types.Ty Δ}
    {c : Conversion.Conv↑ Δ A B}
  → (c⊢ : Σ Conversion.⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (shift-reveal-typing {C = C} c⊢)
      ≡ revealGeneratorPosition c⊢
shift-reveal-position {X = X} {R = R} c⊢ =
  trans
    (reveal-index-transport-position
      (toRename-wk-eq X) (renameᵗ-wk-eq R)
      (reveal-renameᵗ (toRenameᵗ-injective Cons.wk↪ᵗ)
        StoreRename-wk-bind c⊢))
    (revealGeneratorPosition-rename
      (toRenameᵗ-injective Cons.wk↪ᵗ)
      StoreRename-wk-bind c⊢)


shift-conceal-typing : ∀ {Δ} {Σ : TyStore.TyStore Δ} {C}
    {X : Types.TyVar Δ} {R A B : Types.Ty Δ}
    {c : Conversion.Conv↓ Δ A B}
  → Σ Conversion.⊢↓[ X ⦂ R ] c
  → TyStore.store-bind Σ C Conversion.⊢↓[
      Fin.suc X ⦂ ⇑ᵗ R ] Conversion.rename↓ (toRenameᵗ Cons.wk↪ᵗ) c
shift-conceal-typing {X = X} {R = R} c⊢ =
  conceal-index-transport
    (toRename-wk-eq X) (renameᵗ-wk-eq R)
    (conceal-renameᵗ (toRenameᵗ-injective Cons.wk↪ᵗ)
      StoreRename-wk-bind c⊢)


shift-conceal-position : ∀ {Δ} {Σ : TyStore.TyStore Δ} {C}
    {X : Types.TyVar Δ} {R A B : Types.Ty Δ}
    {c : Conversion.Conv↓ Δ A B}
  → (c⊢ : Σ Conversion.⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (shift-conceal-typing {C = C} c⊢)
      ≡ concealGeneratorPosition c⊢
shift-conceal-position {X = X} {R = R} c⊢ =
  trans
    (conceal-index-transport-position
      (toRename-wk-eq X) (renameᵗ-wk-eq R)
      (conceal-renameᵗ (toRenameᵗ-injective Cons.wk↪ᵗ)
        StoreRename-wk-bind c⊢))
    (concealGeneratorPosition-rename
      (toRenameᵗ-injective Cons.wk↪ᵗ)
      StoreRename-wk-bind c⊢)


rename-body-wk-eq : ∀ {Δ} (B : Types.Ty (Nat.suc Δ))
  → Types.renameᵗ (toRenameᵗ (Cons.keep Cons.wk↪ᵗ)) B
    ≡ Types.renameᵗ (Types.extᵗ Fin.suc) B
rename-body-wk-eq B = Types.renameᵗ-cong B pointwise
  where
  pointwise : ∀ X → toRenameᵗ (Cons.keep Cons.wk↪ᵗ) X
    ≡ Types.extᵗ Fin.suc X
  pointwise Fin.zero = refl
  pointwise (Fin.suc X) = cong Fin.suc (toRename-wk-eq X)


rename-body-open-eq : ∀ {Δ} (B : Types.Ty (Nat.suc Δ))
  → Types.renameᵗ (toRenameᵗ (Cons.keep Cons.wk↪ᵗ)) B
    ≡ Types.renameᵗ (Types.extᵗ (toRenameᵗ Cons.wk↪ᵗ)) B
rename-body-open-eq B = Types.renameᵗ-cong B pointwise
  where
  pointwise : ∀ X → toRenameᵗ (Cons.keep Cons.wk↪ᵗ) X
    ≡ Types.extᵗ (toRenameᵗ Cons.wk↪ᵗ) X
  pointwise Fin.zero = refl
  pointwise (Fin.suc X) = refl


shift-all-eq : ∀ {Δ} (B : Types.Ty (Nat.suc Δ))
  → `∀ (Types.renameᵗ (toRenameᵗ (Cons.keep Cons.wk↪ᵗ)) B)
    ≡ ⇑ᵗ (`∀ B)
shift-all-eq B = cong `∀ (rename-body-wk-eq B)


shift-open-eq : ∀ {Δ} (B : Types.Ty (Nat.suc Δ))
    (A : Types.Ty Δ)
  → Types.renameᵗ (toRenameᵗ (Cons.keep Cons.wk↪ᵗ)) B
      [ Types.renameᵗ (toRenameᵗ Cons.wk↪ᵗ) A ]ᵗ
    ≡ ⇑ᵗ (B [ A ]ᵗ)
shift-open-eq B A =
  trans
    (cong (λ T → T [ Types.renameᵗ
      (toRenameᵗ Cons.wk↪ᵗ) A ]ᵗ) (rename-body-open-eq B))
    (trans (sym (rename-openᵗ (toRenameᵗ Cons.wk↪ᵗ) B A))
      (renameᵗ-wk-eq (B [ A ]ᵗ)))


module _
    (transport-type-lambda : TransportSourceBindTypeLambdaᵀ)
    (transport-source-lambda : TransportSourceBindSourceLambdaᵀ)
    (transport-target-reveal-rebase :
      TransportSourceBindTargetRevealRebaseᵀ)
    (transport-target-conceal-rebase :
      TransportSourceBindTargetConcealRebaseᵀ)
  where

  transport-source-bind-through-terms : TransportSourceBindThroughTermsᵀ
  transport-source-bind-through-terms plan
      (CTI.x⊑x² source-member target-member) =
    CTI.x⊑x²
      (source-member-through-terms plan source-member) target-member

  transport-source-bind-through-terms plan
      (CTI.ƛ⊑ƛ² {pA = pA} related) =
    retarget-CTI
      (CTI.ƛ⊑ƛ²
        (transport-source-bind-through-terms
          (source-bind-term plan pA (source-bind-⊑ᵀ plan pA)) related))

  transport-source-bind-through-terms plan
      (CTI.·⊑·² {pA = pA} {pB = pB} function-rel argument-rel) =
    CTI.·⊑·²
      (retarget-CTI
        (transport-source-bind-through-terms plan function-rel))
      (transport-source-bind-through-terms plan argument-rel)

  transport-source-bind-through-terms plan
      (CTI.Λ⊑Λ² source-value target-value related q) =
    transport-type-lambda plan source-value target-value related q

  transport-source-bind-through-terms plan
      (CTI.Λ⊑² nonvar occurs source-value target-typing related q) =
    transport-source-lambda plan nonvar occurs source-value target-typing
      related q

  transport-source-bind-through-terms {C = D} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ related q r) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (shift-open-eq C A)
        (CTI.•⊑•² shifted-p∀ shifted-related shifted-q shifted-r))
    where
    shifted-p∀ =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ `∀ C′) (sym (shift-all-eq C))
        (source-bind-⊑ᵀ plan p∀)
    shifted-related =
      retarget-CTI
        (transport-source-type {γ = γ⁺} (sym (shift-all-eq C))
          (transport-source-bind-through-terms plan related))
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ A′) (sym (renameᵗ-wk-eq A))
        (source-bind-⊑ᵀ plan q)
    shifted-r =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ (C′ [ A′ ]ᵗ))
        (sym (shift-open-eq C A)) (source-bind-⊑ᵀ plan r)

  transport-source-bind-through-terms {C = D} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.•⊑² {C = C} {A = A} {B = B} p∀ related q r) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (shift-open-eq C A)
        (CTI.•⊑² shifted-p∀ shifted-related shifted-q shifted-r))
    where
    shifted-p∀ =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B) (sym (shift-all-eq C))
        (source-bind-⊑ᵀ plan p∀)
    shifted-related =
      retarget-CTI
        (transport-source-type {γ = γ⁺} (sym (shift-all-eq C))
          (transport-source-bind-through-terms plan related))
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ Types.★) (sym (renameᵗ-wk-eq A))
        (source-bind-⊑ᵀ plan q)
    shifted-r =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B) (sym (shift-open-eq C A))
        (source-bind-⊑ᵀ plan r)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.κ⊑κ² (κℕ n) p) =
    CTI.κ⊑κ² (κℕ n)
      (source-bind-⊑ᵀ plan p)
  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.κ⊑κ² (κ𝔹 b) p) =
    CTI.κ⊑κ² (κ𝔹 b)
      (source-bind-⊑ᵀ plan p)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.cast⊑cast² {C = A} {C′ = A′} {A = B} {A′ = B′}
        c c′ related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.cast⊑cast² shifted c′ shifted-related shifted-q))
    where
    shifted = Cons.renameᵐᶜ Cons.wk↪ᵗ c
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind-through-terms plan related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B′) (sym (renameᵗ-wk-eq B))
        (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.⊑cast² c′ related q) =
    CTI.⊑cast² c′ (transport-source-bind-through-terms plan related)
      (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.⊑reveal-identity c′⊢ position related q) =
    CTI.⊑reveal-identity c′⊢ position
      (transport-source-bind-through-terms plan related)
      (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.⊑conceal-identity c′⊢ position related q) =
    CTI.⊑conceal-identity c′⊢ position
      (transport-source-bind-through-terms plan related)
      (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.cast⊑² {A = A} {A′ = B} {B = D} c related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.cast⊑² shifted shifted-related shifted-q))
    where
    shifted = Cons.renameᵐᶜ Cons.wk↪ᵗ c
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind-through-terms plan related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ D) (sym (renameᵗ-wk-eq B))
        (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.reveal⊑-identity {A = A} {A′ = B} {B = D}
        c⊢ position related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.reveal⊑-identity shifted
          (trans (shift-reveal-position c⊢) position)
          shifted-related shifted-q))
    where
    shifted = shift-reveal-typing {C = C} c⊢
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind-through-terms plan related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ D) (sym (renameᵗ-wk-eq B))
        (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.reveal⊑-only² {A = A} {A′ = B} {B = D}
        c⊢ position mark disaligned represented related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.reveal⊑-only² shifted shifted-position
          (source-bind-source-mark plan mark)
          (source-bind-source-disaligned plan disaligned)
          (source-bind-⊑ᵀ plan represented)
          shifted-related shifted-q))
    where
    shifted = shift-reveal-typing {C = C} c⊢
    shifted-position = λ absent → position
      (trans (sym (shift-reveal-position c⊢)) absent)
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind-through-terms plan related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ D) (sym (renameᵗ-wk-eq B))
        (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.conceal⊑-identity {A = A} {A′ = B} {B = D}
        c⊢ position related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.conceal⊑-identity shifted
          (trans (shift-conceal-position c⊢) position)
          shifted-related shifted-q))
    where
    shifted = shift-conceal-typing {C = C} c⊢
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind-through-terms plan related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ D) (sym (renameᵗ-wk-eq B))
        (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.conceal⊑-only² {A = A} {A′ = B} {B = D}
        c⊢ position mark disaligned represented related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.conceal⊑-only² shifted shifted-position
          (source-bind-source-mark plan mark)
          (source-bind-source-disaligned plan disaligned)
          (source-bind-⊑ᵀ plan represented)
          shifted-related shifted-q))
    where
    shifted = shift-conceal-typing {C = C} c⊢
    shifted-position = λ absent → position
      (trans (sym (shift-conceal-position c⊢)) absent)
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind-through-terms plan related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ D) (sym (renameᵗ-wk-eq B))
        (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.reveal⊑reveal² {A = A} {A′ = A′} {B = B} {B′ = B′}
        c⊢ c′⊢ same-position aligned represented related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.reveal⊑reveal² shifted c′⊢
          (trans (shift-reveal-position c⊢) same-position)
          (source-bind-aligned plan aligned)
          (source-bind-⊑ᵀ plan represented)
          shifted-related shifted-q))
    where
    shifted = shift-reveal-typing {C = C} c⊢
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind-through-terms plan related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B′) (sym (renameᵗ-wk-eq B))
        (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.conceal⊑conceal² {A = A} {A′ = A′} {B = B} {B′ = B′}
        c⊢ c′⊢ same-position aligned represented related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.conceal⊑conceal² shifted c′⊢
          (trans (shift-conceal-position c⊢) same-position)
          (source-bind-aligned plan aligned)
          (source-bind-⊑ᵀ plan represented)
          shifted-related shifted-q))
    where
    shifted = shift-conceal-typing {C = C} c⊢
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind-through-terms plan related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B′) (sym (renameᵗ-wk-eq B))
        (source-bind-⊑ᵀ plan q)

  transport-source-bind-through-terms {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.⊑reveal-rebase² c′⊢ ok represented related q) =
    transport-target-reveal-rebase plan c′⊢ ok represented related q

  transport-source-bind-through-terms {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.⊑conceal-rebase² c′⊢ ok represented related q) =
    transport-target-conceal-rebase
      c′⊢ ok represented related q plan

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.blame⊑² target-typing p) =
    CTI.blame⊑² target-typing
      (source-bind-⊑ᵀ plan p)

  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.⊕⊑⊕² addℕ left-rel right-rel r) =
    CTI.⊕⊑⊕² addℕ
      (transport-source-bind-through-terms plan left-rel)
      (transport-source-bind-through-terms plan right-rel)
      (source-bind-⊑ᵀ plan r)
  transport-source-bind-through-terms {C = C} {γ = γ} {γ⁺ = γ⁺} plan
      (CTI.⊕⊑⊕² and𝔹 left-rel right-rel r) =
    CTI.⊕⊑⊕² and𝔹
      (transport-source-bind-through-terms plan left-rel)
      (transport-source-bind-through-terms plan right-rel)
      (source-bind-⊑ᵀ plan r)

  transport-source-bind : TransportSourceBindᵀ
  transport-source-bind eqᴸ related =
    transport-source-bind-through-terms (source-bind-root eqᴸ) related
