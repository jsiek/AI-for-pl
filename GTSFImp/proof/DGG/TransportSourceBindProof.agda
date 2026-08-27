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
  (_≡_; refl; sym; trans; subst; cong)

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
  (_⊑ᶜ_; _⊑ᵀ⟨_⟩_; _▻ᶜ_; bind-left-changeᶜ)
open import proof.DGG.TransportTermImprecisionStepDef using
  (TransportSourceBindᵀ)
open import proof.DGG.TransportSourceBindDef using
  ( TransportSourceBindLambdaᵀ
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
    (transport-lambda : TransportSourceBindLambdaᵀ)
    (transport-type-lambda : TransportSourceBindTypeLambdaᵀ)
    (transport-source-lambda : TransportSourceBindSourceLambdaᵀ)
    (transport-target-reveal-rebase :
      TransportSourceBindTargetRevealRebaseᵀ)
    (transport-target-conceal-rebase :
      TransportSourceBindTargetConcealRebaseᵀ)
  where

  transport-source-bind : TransportSourceBindᵀ
  transport-source-bind {γ = γ} eqᴸ (CTI.x⊑x² source-member target-member) =
    CTI.x⊑x² (source-member-bind eqᴸ source-member) target-member

  transport-source-bind {γ = γ} eqᴸ (CTI.ƛ⊑ƛ² related) =
    transport-lambda eqᴸ related

  transport-source-bind {γ = γ} eqᴸ
      (CTI.·⊑·² {pA = pA} {pB = pB} function-rel argument-rel) =
    CTI.·⊑·²
      (retarget-CTI (transport-source-bind eqᴸ function-rel))
      (transport-source-bind eqᴸ argument-rel)

  transport-source-bind {γ = γ} eqᴸ
      (CTI.Λ⊑Λ² source-value target-value related q) =
    transport-type-lambda eqᴸ source-value target-value related q

  transport-source-bind {γ = γ} eqᴸ
      (CTI.Λ⊑² nonvar occurs source-value target-typing related q) =
    transport-source-lambda eqᴸ nonvar occurs source-value target-typing
      related q

  transport-source-bind {C = D} {γ = γ} eqᴸ
      (CTI.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
        p∀ related q r) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (shift-open-eq C A)
        (CTI.•⊑•² shifted-p∀ shifted-related shifted-q shifted-r))
    where
    evolution = evolution-bind-left {A = D} {W = γ} eqᴸ
    γ⁺ = γ ▻ᶜ bind-left-changeᶜ D eqᴸ
    shifted-p∀ =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ `∀ C′) (sym (shift-all-eq C))
        (evolution-⊑ᵀ evolution p∀)
    shifted-related =
      retarget-CTI
        (transport-source-type {γ = γ⁺} (sym (shift-all-eq C))
          (transport-source-bind eqᴸ related))
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ A′) (sym (renameᵗ-wk-eq A))
        (evolution-⊑ᵀ evolution q)
    shifted-r =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ (C′ [ A′ ]ᵗ))
        (sym (shift-open-eq C A)) (evolution-⊑ᵀ evolution r)

  transport-source-bind {C = D} {γ = γ} eqᴸ
      (CTI.•⊑² {C = C} {A = A} {B = B} p∀ related q r) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (shift-open-eq C A)
        (CTI.•⊑² shifted-p∀ shifted-related shifted-q shifted-r))
    where
    evolution = evolution-bind-left {A = D} {W = γ} eqᴸ
    γ⁺ = γ ▻ᶜ bind-left-changeᶜ D eqᴸ
    shifted-p∀ =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B) (sym (shift-all-eq C))
        (evolution-⊑ᵀ evolution p∀)
    shifted-related =
      retarget-CTI
        (transport-source-type {γ = γ⁺} (sym (shift-all-eq C))
          (transport-source-bind eqᴸ related))
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ Types.★) (sym (renameᵗ-wk-eq A))
        (evolution-⊑ᵀ evolution q)
    shifted-r =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B) (sym (shift-open-eq C A))
        (evolution-⊑ᵀ evolution r)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.κ⊑κ² (κℕ n) p) =
    CTI.κ⊑κ² (κℕ n)
      (evolution-⊑ᵀ (evolution-bind-left {A = C} {W = γ} eqᴸ) p)
  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.κ⊑κ² (κ𝔹 b) p) =
    CTI.κ⊑κ² (κ𝔹 b)
      (evolution-⊑ᵀ (evolution-bind-left {A = C} {W = γ} eqᴸ) p)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.cast⊑cast² {C = A} {C′ = A′} {A = B} {A′ = B′}
        c c′ related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.cast⊑cast² shifted c′ shifted-related shifted-q))
    where
    evolution = evolution-bind-left {A = C} {W = γ} eqᴸ
    γ⁺ = γ ▻ᶜ bind-left-changeᶜ C eqᴸ
    shifted = Cons.renameᵐᶜ Cons.wk↪ᵗ c
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind eqᴸ related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B′) (sym (renameᵗ-wk-eq B))
        (evolution-⊑ᵀ evolution q)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.⊑cast² c′ related q) =
    CTI.⊑cast² c′ (transport-source-bind eqᴸ related)
      (evolution-⊑ᵀ (evolution-bind-left {A = C} {W = γ} eqᴸ) q)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.⊑reveal-identity c′⊢ position related q) =
    CTI.⊑reveal-identity c′⊢ position
      (transport-source-bind eqᴸ related)
      (evolution-⊑ᵀ (evolution-bind-left {A = C} {W = γ} eqᴸ) q)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.⊑conceal-identity c′⊢ position related q) =
    CTI.⊑conceal-identity c′⊢ position
      (transport-source-bind eqᴸ related)
      (evolution-⊑ᵀ (evolution-bind-left {A = C} {W = γ} eqᴸ) q)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.cast⊑² {A = A} {A′ = B} {B = D} c related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.cast⊑² shifted shifted-related shifted-q))
    where
    evolution = evolution-bind-left {A = C} {W = γ} eqᴸ
    γ⁺ = γ ▻ᶜ bind-left-changeᶜ C eqᴸ
    shifted = Cons.renameᵐᶜ Cons.wk↪ᵗ c
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind eqᴸ related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ D) (sym (renameᵗ-wk-eq B))
        (evolution-⊑ᵀ evolution q)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.reveal⊑-identity {A = A} {A′ = B} {B = D}
        c⊢ position related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.reveal⊑-identity shifted
          (trans (shift-reveal-position c⊢) position)
          shifted-related shifted-q))
    where
    evolution = evolution-bind-left {A = C} {W = γ} eqᴸ
    γ⁺ = γ ▻ᶜ bind-left-changeᶜ C eqᴸ
    shifted = shift-reveal-typing {C = C} c⊢
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind eqᴸ related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ D) (sym (renameᵗ-wk-eq B))
        (evolution-⊑ᵀ evolution q)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.reveal⊑-only² {A = A} {A′ = B} {B = D}
        c⊢ position mark disaligned represented related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.reveal⊑-only² shifted shifted-position
          (evolution-source-mark evolution mark)
          (evolution-source-disaligned evolution disaligned)
          (evolution-⊑ᵀ evolution represented)
          shifted-related shifted-q))
    where
    evolution = evolution-bind-left {A = C} {W = γ} eqᴸ
    γ⁺ = γ ▻ᶜ bind-left-changeᶜ C eqᴸ
    shifted = shift-reveal-typing {C = C} c⊢
    shifted-position = λ absent → position
      (trans (sym (shift-reveal-position c⊢)) absent)
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind eqᴸ related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ D) (sym (renameᵗ-wk-eq B))
        (evolution-⊑ᵀ evolution q)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.conceal⊑-identity {A = A} {A′ = B} {B = D}
        c⊢ position related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.conceal⊑-identity shifted
          (trans (shift-conceal-position c⊢) position)
          shifted-related shifted-q))
    where
    evolution = evolution-bind-left {A = C} {W = γ} eqᴸ
    γ⁺ = γ ▻ᶜ bind-left-changeᶜ C eqᴸ
    shifted = shift-conceal-typing {C = C} c⊢
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind eqᴸ related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ D) (sym (renameᵗ-wk-eq B))
        (evolution-⊑ᵀ evolution q)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.conceal⊑-only² {A = A} {A′ = B} {B = D}
        c⊢ position mark disaligned represented related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.conceal⊑-only² shifted shifted-position
          (evolution-source-mark evolution mark)
          (evolution-source-disaligned evolution disaligned)
          (evolution-⊑ᵀ evolution represented)
          shifted-related shifted-q))
    where
    evolution = evolution-bind-left {A = C} {W = γ} eqᴸ
    γ⁺ = γ ▻ᶜ bind-left-changeᶜ C eqᴸ
    shifted = shift-conceal-typing {C = C} c⊢
    shifted-position = λ absent → position
      (trans (sym (shift-conceal-position c⊢)) absent)
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind eqᴸ related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ D) (sym (renameᵗ-wk-eq B))
        (evolution-⊑ᵀ evolution q)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.reveal⊑reveal² {A = A} {A′ = A′} {B = B} {B′ = B′}
        c⊢ c′⊢ same-position aligned represented related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.reveal⊑reveal² shifted c′⊢
          (trans (shift-reveal-position c⊢) same-position)
          (evolution-aligned evolution aligned)
          (evolution-⊑ᵀ evolution represented)
          shifted-related shifted-q))
    where
    evolution = evolution-bind-left {A = C} {W = γ} eqᴸ
    γ⁺ = γ ▻ᶜ bind-left-changeᶜ C eqᴸ
    shifted = shift-reveal-typing {C = C} c⊢
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind eqᴸ related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B′) (sym (renameᵗ-wk-eq B))
        (evolution-⊑ᵀ evolution q)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.conceal⊑conceal² {A = A} {A′ = A′} {B = B} {B′ = B′}
        c⊢ c′⊢ same-position aligned represented related q) =
    retarget-CTI
      (transport-source-type {γ = γ⁺} (renameᵗ-wk-eq B)
        (CTI.conceal⊑conceal² shifted c′⊢
          (trans (shift-conceal-position c⊢) same-position)
          (evolution-aligned evolution aligned)
          (evolution-⊑ᵀ evolution represented)
          shifted-related shifted-q))
    where
    evolution = evolution-bind-left {A = C} {W = γ} eqᴸ
    γ⁺ = γ ▻ᶜ bind-left-changeᶜ C eqᴸ
    shifted = shift-conceal-typing {C = C} c⊢
    shifted-related =
      transport-source-type {γ = γ⁺} (sym (renameᵗ-wk-eq A))
        (transport-source-bind eqᴸ related)
    shifted-q =
      subst (λ T → T ⊑ᵀ⟨ γ⁺ ⟩ B′) (sym (renameᵗ-wk-eq B))
        (evolution-⊑ᵀ evolution q)

  transport-source-bind {γ = γ} eqᴸ
      (CTI.⊑reveal-rebase² c′⊢ ok represented related q) =
    transport-target-reveal-rebase eqᴸ c′⊢ ok represented related q

  transport-source-bind {γ = γ} eqᴸ
      (CTI.⊑conceal-rebase² c′⊢ ok represented related q) =
    transport-target-conceal-rebase eqᴸ c′⊢ ok represented related q

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.blame⊑² target-typing p) =
    CTI.blame⊑² target-typing
      (evolution-⊑ᵀ (evolution-bind-left {A = C} {W = γ} eqᴸ) p)

  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.⊕⊑⊕² addℕ left-rel right-rel r) =
    CTI.⊕⊑⊕² addℕ
      (transport-source-bind eqᴸ left-rel)
      (transport-source-bind eqᴸ right-rel)
      (evolution-⊑ᵀ (evolution-bind-left {A = C} {W = γ} eqᴸ) r)
  transport-source-bind {C = C} {γ = γ} eqᴸ
      (CTI.⊕⊑⊕² and𝔹 left-rel right-rel r) =
    CTI.⊕⊑⊕² and𝔹
      (transport-source-bind eqᴸ left-rel)
      (transport-source-bind eqᴸ right-rel)
      (evolution-⊑ᵀ (evolution-bind-left {A = C} {W = γ} eqᴸ) r)
