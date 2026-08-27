module alt.ThetaTermSubst where

-- File Charter:
--   * Provides the substitution and transport toolkit used by theta
--     preservation: conversion endpoint determinacy, term substitution, and
--     transport along balanced telescope extensions.
--   * Representation premises are equations for the total evaluator `rep?`.
--     Transport therefore proves evaluator stability directly; there is no
--     representation-lookup relation or relational-walk lemma surface.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc; toℕ)
import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_; suc-injective)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
  renaming (map to mapMaybe)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (_,_; _×_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (¬_; yes; no)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Consistency
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction

private
  variable
    Θ Θ′ : AnchorCtx
    Δ Δ′ : TyCtx
    σ : Vec.Vec (Maybe (TyVar Θ)) Δ
    Ψ Ψ′ : TyEnv Θ Δ σ
    Γ Γ′ : TermCtx Δ
    A B C D : Ty Δ
    L M N : Term Θ Δ
    slot inner outer : TyVar Δ
    entry anchor bound α a : TyVar Θ

------------------------------------------------------------------------
-- Conversion endpoint determinacy
------------------------------------------------------------------------

-- Raw shapes omit their endpoints, but a typed shape determines each
-- missing endpoint from the other one.  The dual target statements are
-- simultaneous induction hypotheses for contravariant arrow positions.

mutual
  source-determinacy↑ : ∀ {Δ} {X : TyVar Δ} {R : Ty Δ}
      {c : Reveal} {A T : Ty Δ}
    → ⊢↑[ X ⦂ R ] c ⦂ A ↝ T
    → A ≡ src↑ X c T
  source-determinacy↑ ⊢unseal = refl
  source-determinacy↑ (⊢↑-⇒ c⊢ d⊢) =
    cong₂ _⇒_ (target-determinacy↓ c⊢) (source-determinacy↑ d⊢)
  source-determinacy↑ (⊢↑-∀ c⊢) =
    cong `∀ (source-determinacy↑ c⊢)
  source-determinacy↑ (⊢id↑ A) = refl

  target-determinacy↓ : ∀ {Δ} {X : TyVar Δ} {R : Ty Δ}
      {c : Conceal} {A T : Ty Δ}
    → ⊢↓[ X ⦂ R ] c ⦂ A ↝ T
    → T ≡ tgt↓ X c A
  target-determinacy↓ ⊢seal = refl
  target-determinacy↓ (⊢↓-⇒ c⊢ d⊢) =
    cong₂ _⇒_ (source-determinacy↑ c⊢) (target-determinacy↓ d⊢)
  target-determinacy↓ (⊢↓-∀ c⊢) =
    cong `∀ (target-determinacy↓ c⊢)
  target-determinacy↓ (⊢id↓ A) = refl

mutual
  source-determinacy↓ : ∀ {Δ} {X : TyVar Δ} {R : Ty Δ}
      {c : Conceal} {A T : Ty Δ}
    → ⊢↓[ X ⦂ R ] c ⦂ A ↝ T
    → A ≡ src↓ X R c T
  source-determinacy↓ ⊢seal = refl
  source-determinacy↓ (⊢↓-⇒ c⊢ d⊢) =
    cong₂ _⇒_ (target-determinacy↑ c⊢) (source-determinacy↓ d⊢)
  source-determinacy↓ (⊢↓-∀ c⊢) =
    cong `∀ (source-determinacy↓ c⊢)
  source-determinacy↓ (⊢id↓ A) = refl

  target-determinacy↑ : ∀ {Δ} {X : TyVar Δ} {R : Ty Δ}
      {c : Reveal} {A T : Ty Δ}
    → ⊢↑[ X ⦂ R ] c ⦂ A ↝ T
    → T ≡ tgt↑ X R c A
  target-determinacy↑ ⊢unseal = refl
  target-determinacy↑ (⊢↑-⇒ c⊢ d⊢) =
    cong₂ _⇒_ (source-determinacy↓ c⊢) (target-determinacy↑ d⊢)
  target-determinacy↑ (⊢↑-∀ c⊢) =
    cong `∀ (target-determinacy↑ c⊢)
  target-determinacy↑ (⊢id↑ A) = refl

------------------------------------------------------------------------
-- Resolution algebra for conversions crossing a deleted slot
------------------------------------------------------------------------

substᵗ-subst : ∀ {Δ₁ Δ₂ Δ₃} (σ : Δ₁ ⇒ˢ Δ₂)
    (τ : Δ₂ ⇒ˢ Δ₃) (A : Ty Δ₁)
  → substᵗ τ (substᵗ σ A) ≡ substᵗ (λ X → substᵗ τ (σ X)) A
substᵗ-subst σ τ (＇ X) = refl
substᵗ-subst σ τ (‵ ι) = refl
substᵗ-subst σ τ ★ = refl
substᵗ-subst σ τ (A ⇒ B)
    rewrite substᵗ-subst σ τ A | substᵗ-subst σ τ B =
  refl
substᵗ-subst σ τ (`∀ A) =
  cong `∀
    (trans (substᵗ-subst (extsᵗ σ) (extsᵗ τ) A)
      (substᵗ-cong A exts-compose))
  where
  exts-compose : ∀ X
    → substᵗ (extsᵗ τ) (extsᵗ σ X)
      ≡ extsᵗ (λ Y → substᵗ τ (σ Y)) X
  exts-compose zero = refl
  exts-compose (suc X) = substᵗ-shift τ (σ X)

resolve-openᵗ : ∀ {Δ} (X : TyVar (suc Δ)) (C : Ty Δ)
    (B : Ty (suc (suc Δ))) (A : Ty (suc Δ))
  → substᵗ (resolveSubᵗ X C) (B [ A ]ᵗ)
    ≡ (substᵗ (resolveSubᵗ (suc X) (⇑ᵗ C)) B)
        [ substᵗ (resolveSubᵗ X C) A ]ᵗ
resolve-openᵗ X C B A =
  trans (substᵗ-subst (singleSubᵗ A) (resolveSubᵗ X C) B)
    (trans (substᵗ-cong B env-eq)
      (sym (substᵗ-subst
        (resolveSubᵗ (suc X) (⇑ᵗ C))
        (singleSubᵗ (substᵗ (resolveSubᵗ X C) A)) B)))
  where
  env-eq : ∀ Y
    → substᵗ (resolveSubᵗ X C) (singleSubᵗ A Y)
      ≡ substᵗ (singleSubᵗ (substᵗ (resolveSubᵗ X C) A))
          (resolveSubᵗ (suc X) (⇑ᵗ C) Y)
  env-eq zero = refl
  env-eq (suc Y) =
    sym (trans (cong
      (substᵗ (singleSubᵗ (substᵗ (resolveSubᵗ X C) A)))
      (resolveSub-ext X C (suc Y)))
      (shift-openᵗ (resolveSubᵗ X C Y)
        (substᵗ (resolveSubᵗ X C) A)))

resolve-wk-exchange : ∀ {Δ} (X : TyVar (suc Δ)) (C : Ty Δ)
  → ⇑ᵗ (wkᵗ X C) ≡ wkᵗ (suc X) (⇑ᵗ C)
resolve-wk-exchange X C =
  trans (renameᵗ-comp (punchIn X) suc C)
    (trans (renameᵗ-cong C punch-exchange)
      (sym (renameᵗ-comp suc (punchIn (suc X)) C)))
  where
  punch-exchange : ∀ Y
    → suc (punchIn X Y) ≡ punchIn (suc X) (suc Y)
  punch-exchange Y = refl

mutual
  resolve-conversion↑ : ∀ {Δ} {X : TyVar (suc Δ)} {C : Ty Δ}
      {c : Reveal} {A B : Ty (suc Δ)}
    → ⊢↑[ X ⦂ wkᵗ X C ] c ⦂ A ↝ B
    → substᵗ (resolveSubᵗ X C) A
      ≡ substᵗ (resolveSubᵗ X C) B
  resolve-conversion↑ {X = X} {C = C} ⊢unseal =
    trans (resolveSub-here X C) (sym (resolve-wkᵗ X C C))
  resolve-conversion↑ (⊢↑-⇒ c⊢ d⊢) =
    cong₂ _⇒_ (sym (resolve-conversion↓ c⊢))
      (resolve-conversion↑ d⊢)
  resolve-conversion↑ {X = X} {C = C} (⊢↑-∀ {A = A} {B = B} c⊢) =
    cong `∀
      (trans (substᵗ-cong A (λ Y → sym (resolveSub-ext X C Y)))
        (trans (resolve-conversion↑ inner⊢)
          (substᵗ-cong B (resolveSub-ext X C))))
    where
    inner⊢ = subst≡ (λ R → ⊢↑[ suc X ⦂ R ] _ ⦂ A ↝ B)
      (resolve-wk-exchange X C) c⊢
  resolve-conversion↑ (⊢id↑ A) = refl

  resolve-conversion↓ : ∀ {Δ} {X : TyVar (suc Δ)} {C : Ty Δ}
      {c : Conceal} {A B : Ty (suc Δ)}
    → ⊢↓[ X ⦂ wkᵗ X C ] c ⦂ A ↝ B
    → substᵗ (resolveSubᵗ X C) A
      ≡ substᵗ (resolveSubᵗ X C) B
  resolve-conversion↓ {X = X} {C = C} ⊢seal =
    trans (resolve-wkᵗ X C C) (sym (resolveSub-here X C))
  resolve-conversion↓ (⊢↓-⇒ c⊢ d⊢) =
    cong₂ _⇒_ (sym (resolve-conversion↑ c⊢))
      (resolve-conversion↓ d⊢)
  resolve-conversion↓ {X = X} {C = C} (⊢↓-∀ {A = A} {B = B} c⊢) =
    cong `∀
      (trans (substᵗ-cong A (λ Y → sym (resolveSub-ext X C Y)))
        (trans (resolve-conversion↓ inner⊢)
          (substᵗ-cong B (resolveSub-ext X C))))
    where
    inner⊢ = subst≡ (λ R → ⊢↓[ suc X ⦂ R ] _ ⦂ A ↝ B)
      (resolve-wk-exchange X C) c⊢
  resolve-conversion↓ (⊢id↓ A) = refl

------------------------------------------------------------------------
-- Injection identities used by telescope and conversion transport
------------------------------------------------------------------------

toRename-keep-eq : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) X
  → toRenameᵗ (keep ρ) X ≡ extᵗ (toRenameᵗ ρ) X
toRename-keep-eq ρ zero = refl
toRename-keep-eq ρ (suc X) = refl

toRename-id-eq : ∀ {Δ} (X : TyVar Δ)
  → toRenameᵗ id↪ᵗ X ≡ X
toRename-id-eq {zero} ()
toRename-id-eq {suc Δ} zero = refl
toRename-id-eq {suc Δ} (suc X) = cong suc (toRename-id-eq X)

toRename-wk-eq : ∀ {Δ} (X : TyVar Δ)
  → toRenameᵗ wk↪ᵗ X ≡ suc X
toRename-wk-eq X = cong suc (toRename-id-eq X)

renameᵗ-wk-eq : ∀ {Δ} (A : Ty Δ)
  → renameᵗ (toRenameᵗ wk↪ᵗ) A ≡ ⇑ᵗ A
renameᵗ-wk-eq A = renameᵗ-cong A toRename-wk-eq

delete-insert↪ᵗ : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ))
  → delete↪ᵗ (insert↪ᵗ ρ Y) Y ≡ ρ
delete-insert↪ᵗ ρ zero = refl
delete-insert↪ᵗ (keep ρ) (suc Y) =
  cong keep (delete-insert↪ᵗ ρ Y)
delete-insert↪ᵗ (skip ρ) (suc Y) =
  cong skip (delete-insert↪ᵗ ρ (suc Y))

insert-punchIn : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ)) (X : TyVar Δ)
  → toRenameᵗ (insert↪ᵗ ρ Y) (punchIn Y X)
    ≡ punchIn (toRenameᵗ (insert↪ᵗ ρ Y) Y) (toRenameᵗ ρ X)
insert-punchIn ρ zero X = refl
insert-punchIn (keep ρ) (suc Y) zero = refl
insert-punchIn (keep ρ) (suc Y) (suc X) =
  cong suc (insert-punchIn ρ Y X)
insert-punchIn (skip ρ) (suc Y) X =
  cong suc (insert-punchIn ρ (suc Y) X)

delete-punchIn : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (X : TyVar Δ)
  → toRenameᵗ ρ (punchIn Y X)
    ≡ punchIn (toRenameᵗ ρ Y) (toRenameᵗ (delete↪ᵗ ρ Y) X)
delete-punchIn (keep ρ) zero X = refl
delete-punchIn (keep (keep ρ)) (suc Y) zero = refl
delete-punchIn (keep (keep ρ)) (suc Y) (suc X) =
  cong suc (delete-punchIn (keep ρ) Y X)
delete-punchIn (keep (skip ρ)) (suc Y) zero = refl
delete-punchIn (keep (skip ρ)) (suc Y) (suc X) =
  cong suc (delete-punchIn (skip ρ) Y X)
delete-punchIn (skip (keep ρ)) Y X =
  cong suc (delete-punchIn (keep ρ) Y X)
delete-punchIn (skip (skip ρ)) Y X =
  cong suc (delete-punchIn (skip ρ) Y X)

delete-keep-suc : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ))
  → delete↪ᵗ (keep ρ) (suc Y) ≡ keep (delete↪ᵗ ρ Y)
delete-keep-suc ρ Y = refl

delete-skip : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ))
  → delete↪ᵗ (skip ρ) Y ≡ skip (delete↪ᵗ ρ Y)
delete-skip ρ Y = refl

toRename-compose : ∀ {Δ₁ Δ₂ Δ₃}
    (ρ : Δ₁ ↪ᵗ Δ₂) (η : Δ₂ ↪ᵗ Δ₃) X
  → toRenameᵗ (ρ ⨟↪ᵗ η) X
    ≡ toRenameᵗ η (toRenameᵗ ρ X)
toRename-compose empty empty ()
toRename-compose empty (skip η) ()
toRename-compose (keep ρ) (skip η) X =
  cong suc (toRename-compose (keep ρ) η X)
toRename-compose (skip ρ) (skip η) X =
  cong suc (toRename-compose (skip ρ) η X)
toRename-compose empty (keep η) ()
toRename-compose (keep ρ) (keep η) zero = refl
toRename-compose (keep ρ) (keep η) (suc X) =
  cong suc (toRename-compose ρ η X)
toRename-compose (skip ρ) (keep η) X =
  cong suc (toRename-compose ρ η X)

rename-insert-wk : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (insert↪ᵗ ρ Y)) (wkᵗ Y A)
    ≡ wkᵗ (toRenameᵗ (insert↪ᵗ ρ Y) Y)
        (renameᵗ (toRenameᵗ ρ) A)
rename-insert-wk ρ Y A =
  trans (renameᵗ-comp (punchIn Y)
           (toRenameᵗ (insert↪ᵗ ρ Y)) A)
    (trans (renameᵗ-cong A (insert-punchIn ρ Y))
      (sym (renameᵗ-comp (toRenameᵗ ρ)
        (punchIn (toRenameᵗ (insert↪ᵗ ρ Y) Y)) A)))

rename-delete-wk : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ ρ) (wkᵗ Y A)
    ≡ wkᵗ (toRenameᵗ ρ Y)
        (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) A)
rename-delete-wk ρ Y A =
  trans (renameᵗ-comp (punchIn Y) (toRenameᵗ ρ) A)
    (trans (renameᵗ-cong A (delete-punchIn ρ Y))
      (sym (renameᵗ-comp (toRenameᵗ (delete↪ᵗ ρ Y))
        (punchIn (toRenameᵗ ρ Y)) A)))

-- Conversion typing under regular-context injections
------------------------------------------------------------------------

renameAtom : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {A : Ty Δ}
  → Atom A
  → Atom (renameᵗ ρ A)
renameAtom ρ (＇ X) = ＇ ρ X
renameAtom ρ (‵ ι) = ‵ ι
renameAtom ρ ★ = ★

mutual
  rename-⊢↑ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
      {X : TyVar Δ} {R A B : Ty Δ} {c : Reveal}
    → ⊢↑[ X ⦂ R ] c ⦂ A ↝ B
    → ⊢↑[ ρ X ⦂ renameᵗ ρ R ] c
        ⦂ renameᵗ ρ A ↝ renameᵗ ρ B
  rename-⊢↑ ρ ⊢unseal = ⊢unseal
  rename-⊢↑ ρ (⊢↑-⇒ c⊢ d⊢) =
    ⊢↑-⇒ (rename-⊢↓ ρ c⊢) (rename-⊢↑ ρ d⊢)
  rename-⊢↑ ρ (⊢↑-∀ {R = R} c⊢) =
    ⊢↑-∀
      (subst≡
        (λ R′ → ⊢↑[ suc _ ⦂ R′ ] _ ⦂ _ ↝ _)
        (renameᵗ-shift ρ R)
        (rename-⊢↑ (extᵗ ρ) c⊢))
  rename-⊢↑ ρ (⊢id↑ a) = ⊢id↑ (renameAtom ρ a)

  rename-⊢↓ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
      {X : TyVar Δ} {R A B : Ty Δ} {c : Conceal}
    → ⊢↓[ X ⦂ R ] c ⦂ A ↝ B
    → ⊢↓[ ρ X ⦂ renameᵗ ρ R ] c
        ⦂ renameᵗ ρ A ↝ renameᵗ ρ B
  rename-⊢↓ ρ ⊢seal = ⊢seal
  rename-⊢↓ ρ (⊢↓-⇒ c⊢ d⊢) =
    ⊢↓-⇒ (rename-⊢↑ ρ c⊢) (rename-⊢↓ ρ d⊢)
  rename-⊢↓ ρ (⊢↓-∀ {R = R} c⊢) =
    ⊢↓-∀
      (subst≡
        (λ R′ → ⊢↓[ suc _ ⦂ R′ ] _ ⦂ _ ↝ _)
        (renameᵗ-shift ρ R)
        (rename-⊢↓ (extᵗ ρ) c⊢))
  rename-⊢↓ ρ (⊢id↓ a) = ⊢id↓ (renameAtom ρ a)

------------------------------------------------------------------------
-- Term-variable renaming preserves typing
------------------------------------------------------------------------

ext-∋ : ∀ {Δ} {Γ Γ′ : TermCtx Δ} {ρ : Rename} {A : Ty Δ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
  → ∀ {x B} → A ∷ Γ ∋ x ⦂ B → A ∷ Γ′ ∋ ext ρ x ⦂ B
ext-∋ hρ Z = Z
ext-∋ hρ (S x∈) = S (hρ x∈)

lookup-renameCtx-inv : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
    {Γ : TermCtx Δ} {x A}
  → renameCtx ρ Γ ∋ x ⦂ A
  → ∃[ B ] (Γ ∋ x ⦂ B × renameᵗ ρ B ≡ A)
lookup-renameCtx-inv {Γ = B ∷ Γ} Z = B , Z , refl
lookup-renameCtx-inv {Γ = C ∷ Γ} (S x∈)
    with lookup-renameCtx-inv x∈
lookup-renameCtx-inv {Γ = C ∷ Γ} (S x∈) | B , B∈ , refl =
  B , S B∈ , refl

renameCtx-∋ : ∀ {Δ Δ′} {ρᵗ : Δ ⇒ʳ Δ′}
    {Γ Γ′ : TermCtx Δ} {ρ : Rename}
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → ∀ {x A}
  → renameCtx ρᵗ Γ ∋ x ⦂ A
  → renameCtx ρᵗ Γ′ ∋ ρ x ⦂ A
renameCtx-∋ hρ x∈ with lookup-renameCtx-inv x∈
renameCtx-∋ {ρᵗ = ρᵗ} hρ x∈ | B , B∈ , refl =
  renameᵗ-∋ ρᵗ (hρ B∈)

⊢rename : ∀ {Θ Δ} {σ : Vec.Vec (Maybe (TyVar Θ)) Δ}
    {Ψ : TyEnv Θ Δ σ} {Γ Γ′ : TermCtx Δ}
    {ρ : Rename} {M : Term Θ Δ} {B : Ty Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → Ψ ∣ Γ ⊢ M ⦂ B
  → Ψ ∣ Γ′ ⊢ rename ρ M ⦂ B
⊢rename hρ (⊢` x∈) = ⊢` (hρ x∈)
⊢rename hρ (⊢ƛ M⊢) = ⊢ƛ (⊢rename (ext-∋ hρ) M⊢)
⊢rename hρ (⊢· L⊢ M⊢) =
  ⊢· (⊢rename hρ L⊢) (⊢rename hρ M⊢)
⊢rename hρ (⊢Λ M⊢) = ⊢Λ (⊢rename (renameCtx-∋ hρ) M⊢)
⊢rename hρ (⊢⦂∀ L⊢) = ⊢⦂∀ (⊢rename hρ L⊢)
⊢rename hρ (⊢$ κ) = ⊢$ κ
⊢rename hρ (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢rename hρ L⊢) (⊢rename hρ M⊢)
⊢rename hρ (⊢⟨⟩ M⊢ c) = ⊢⟨⟩ (⊢rename hρ M⊢) c
⊢rename hρ (⊢ν M⊢) = ⊢ν M⊢
⊢rename hρ (⊢reveal α∈ c⊢ M⊢) = ⊢reveal α∈ c⊢ M⊢
⊢rename hρ (⊢conceal slot∈ α∈ c⊢ M⊢) =
  ⊢conceal slot∈ α∈ c⊢ M⊢
⊢rename hρ ⊢blame = ⊢blame

⊢rename-suc : ∀ {Θ Δ} {σ : Vec.Vec (Maybe (TyVar Θ)) Δ}
    {Ψ : TyEnv Θ Δ σ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Ψ ∣ B ∷ Γ ⊢ rename suc M ⦂ A
⊢rename-suc M⊢ = ⊢rename (λ x∈ → S x∈) M⊢

------------------------------------------------------------------------
-- Evaluator transport through a lexical slot
------------------------------------------------------------------------

mapMaybe-compose : ∀ {a b c} {X : Set a} {Y : Set b} {Z : Set c}
    (f : Y → Z) (g : X → Y) (m : Maybe X)
  → mapMaybe f (mapMaybe g m) ≡ mapMaybe (λ x → f (g x)) m
mapMaybe-compose f g nothing = refl
mapMaybe-compose f g (just x) = refl

mapMaybe-skip : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) (m : Maybe (TyVar Δ))
  → mapMaybe suc (mapMaybe (toRenameᵗ ρ) m)
    ≡ mapMaybe (toRenameᵗ (skip ρ)) m
mapMaybe-skip ρ nothing = refl
mapMaybe-skip ρ (just X) = refl

mapMaybe-keep-tail : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (m : Maybe (TyVar Δ))
  → mapMaybe suc (mapMaybe (toRenameᵗ ρ) m)
    ≡ mapMaybe (toRenameᵗ (keep ρ)) (mapMaybe suc m)
mapMaybe-keep-tail ρ nothing = refl
mapMaybe-keep-tail ρ (just X) = refl

emptySlots : ∀ {Θ} (D : TyCtx) → Vec.Vec (Maybe (TyVar Θ)) D
emptySlots zero = Vec.[]
emptySlots (suc D) = nothing Vec.∷ emptySlots D

renameSlots : ∀ {Θ Δ Δ′}
  → Δ ↪ᵗ Δ′
  → Vec.Vec (Maybe (TyVar Θ)) Δ
  → Vec.Vec (Maybe (TyVar Θ)) Δ′
renameSlots { Δ′ = Δ′ } empty Vec.[] = emptySlots Δ′
renameSlots (skip ρ) slots = nothing Vec.∷ renameSlots ρ slots
renameSlots (keep ρ) (slot Vec.∷ slots) =
  slot Vec.∷ renameSlots ρ slots

renameSlots-id : ∀ {Θ Δ} (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → renameSlots id↪ᵗ slots ≡ slots
renameSlots-id Vec.[] = refl
renameSlots-id (slot Vec.∷ slots) =
  cong (slot Vec.∷_) (renameSlots-id slots)

liveSlot?-rename : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ) α
  → liveSlot? (renameSlots ρ slots) α
    ≡ mapMaybe (toRenameᵗ ρ) (liveSlot? slots α)
liveSlot?-rename { Δ′ = zero } empty Vec.[] α = refl
liveSlot?-rename { Δ′ = suc Δ′ } empty Vec.[] α
    rewrite liveSlot?-rename { Δ′ = Δ′ } empty Vec.[] α =
  refl
liveSlot?-rename (skip ρ) slots α
    rewrite liveSlot?-rename ρ slots α =
  mapMaybe-skip ρ (liveSlot? slots α)
liveSlot?-rename (keep ρ) (nothing Vec.∷ slots) α
    rewrite liveSlot?-rename ρ slots α =
  mapMaybe-keep-tail ρ (liveSlot? slots α)
liveSlot?-rename (keep ρ) (just q Vec.∷ slots) α
    with α ≟ q
liveSlot?-rename (keep ρ) (just q Vec.∷ slots) .q
    | yes refl = refl
liveSlot?-rename (keep ρ) (just q Vec.∷ slots) α
    | no α≢q rewrite liveSlot?-rename ρ slots α =
  mapMaybe-keep-tail ρ (liveSlot? slots α)

AliasUnique : ∀ {Θ Δ}
  → Vec.Vec (Maybe (TyVar Θ)) Δ → Set
AliasUnique slots = ∀ {X Y a}
  → Vec.lookup slots X ≡ just a
  → Vec.lookup slots Y ≡ just a
  → X ≡ Y

AliasUnique-tail : ∀ {Θ Δ} {head : Maybe (TyVar Θ)}
    {slots : Vec.Vec (Maybe (TyVar Θ)) Δ}
  → AliasUnique (head Vec.∷ slots)
  → AliasUnique slots
AliasUnique-tail unique left right =
  suc-injective (unique left right)

mapMaybe-suc-just-injective : ∀ {n} {value : Maybe (TyVar n)} {X}
  → mapMaybe suc value ≡ just (suc X)
  → value ≡ just X
mapMaybe-suc-just-injective {value = nothing} ()
mapMaybe-suc-just-injective {value = just Y} eq =
  cong just (suc-injective (just-injective eq))

mapMaybe-suc≢zero : ∀ {n} (value : Maybe (TyVar n))
  → mapMaybe Fin.suc value ≢ just Fin.zero
mapMaybe-suc≢zero nothing ()
mapMaybe-suc≢zero (just X) ()

liveSlot?-sound : ∀ {Θ Δ}
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ) a X
  → liveSlot? slots a ≡ just X
  → Vec.lookup slots X ≡ just a
liveSlot?-sound Vec.[] a () eq
liveSlot?-sound (nothing Vec.∷ slots) a zero eq =
  ⊥-elim (mapMaybe-suc≢zero (liveSlot? slots a) eq)
liveSlot?-sound (nothing Vec.∷ slots) a (suc X) eq =
  liveSlot?-sound slots a X (mapMaybe-suc-just-injective eq)
liveSlot?-sound (just q Vec.∷ slots) a X eq with a ≟ q
liveSlot?-sound (just q Vec.∷ slots) .q zero eq | yes refl = refl
liveSlot?-sound (just q Vec.∷ slots) .q (suc X) () | yes refl
liveSlot?-sound (just q Vec.∷ slots) a zero eq | no a≢q =
  ⊥-elim (mapMaybe-suc≢zero (liveSlot? slots a) eq)
liveSlot?-sound (just q Vec.∷ slots) a (suc X) eq | no a≢q =
  liveSlot?-sound slots a X (mapMaybe-suc-just-injective eq)

liveSlot?-complete : ∀ {Θ Δ}
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → AliasUnique slots
  → ∀ {a X}
  → Vec.lookup slots X ≡ just a
  → liveSlot? slots a ≡ just X
liveSlot?-complete Vec.[] unique {X = ()} lookup-eq
liveSlot?-complete (nothing Vec.∷ slots) unique {X = zero} ()
liveSlot?-complete (nothing Vec.∷ slots) unique {X = suc X} lookup-eq =
  cong (mapMaybe suc)
    (liveSlot?-complete slots (AliasUnique-tail unique) lookup-eq)
liveSlot?-complete (just q Vec.∷ slots) unique {a = a} {X = X}
    lookup-eq with a ≟ q
liveSlot?-complete (just q Vec.∷ slots) unique {a = .q} {X = zero}
    lookup-eq | yes refl = refl
liveSlot?-complete (just q Vec.∷ slots) unique {a = .q} {X = suc X}
    lookup-eq | yes refl =
  cong just (unique refl lookup-eq)
liveSlot?-complete (just q Vec.∷ slots) unique {a = a} {X = zero}
    lookup-eq | no a≢q = ⊥-elim (a≢q (just-injective (sym lookup-eq)))
liveSlot?-complete (just q Vec.∷ slots) unique {a = a} {X = suc X}
    lookup-eq | no a≢q =
  cong (mapMaybe suc)
    (liveSlot?-complete slots (AliasUnique-tail unique) lookup-eq)

renameᵗ-id : ∀ {Δ} (A : Ty Δ)
  → renameᵗ (λ X → X) A ≡ A
renameᵗ-id (＇ X) = refl
renameᵗ-id (‵ ι) = refl
renameᵗ-id ★ = refl
renameᵗ-id (A ⇒ B)
    rewrite renameᵗ-id A | renameᵗ-id B = refl
renameᵗ-id (`∀ A) = cong `∀
  (trans (renameᵗ-cong A ext-id) (renameᵗ-id A))
  where
  ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
  ext-id zero = refl
  ext-id (suc X) = refl

route-map : ∀ {Δ₀ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
  → (TyVar Δ₀ → Maybe (TyVar Δ))
  → TyVar Δ₀ → Maybe (TyVar Δ′)
route-map ρ route X = mapMaybe (toRenameᵗ ρ) (route X)

route-end-map : ∀ {Δ₀ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ₀))
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) X
  → route-end Y (route-map ρ route) X
    ≡ route-map ρ (route-end Y route) X
route-end-map ρ Y route X with Y ≟ X
route-end-map ρ Y route .Y | yes refl = refl
route-end-map ρ Y route X | no Y≢X = refl

infixr 5 _⇒?_

_⇒?_ : ∀ {Δ} → Maybe (Ty Δ) → Maybe (Ty Δ) → Maybe (Ty Δ)
nothing ⇒? right = nothing
just A ⇒? nothing = nothing
just A ⇒? just B = just (A ⇒ B)

repoint?-arrow : ∀ {Θ₀ Θ Δ₀ Δ Δout}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A B : Ty Δ₀)
  → repoint? resolve target birth anchor-map route live-ren (A ⇒ B)
    ≡ repoint? resolve target birth anchor-map route live-ren A ⇒?
      repoint? resolve target birth anchor-map route live-ren B
repoint?-arrow resolve target birth anchor-map route live-ren A B
    with repoint? resolve target birth anchor-map route live-ren A
repoint?-arrow resolve target birth anchor-map route live-ren A B
    | nothing = refl
repoint?-arrow resolve target birth anchor-map route live-ren A B
    | just A′ with repoint? resolve target birth anchor-map route live-ren B
repoint?-arrow resolve target birth anchor-map route live-ren A B
    | just A′ | nothing = refl
repoint?-arrow resolve target birth anchor-map route live-ren A B
    | just A′ | just B′ = refl

rename-⇒? : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (left right : Maybe (Ty Δ))
  → mapMaybe (renameᵗ ρ) left ⇒? mapMaybe (renameᵗ ρ) right
    ≡ mapMaybe (renameᵗ ρ) (left ⇒? right)
rename-⇒? ρ nothing right = refl
rename-⇒? ρ (just A) nothing = refl
rename-⇒? ρ (just A) (just B) = refl

all? : ∀ {Δ} → Maybe (Ty (suc Δ)) → Maybe (Ty Δ)
all? nothing = nothing
all? (just A) = just (`∀ A)

repoint?-all : ∀ {Θ₀ Θ Δ₀ Δ Δout}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A : Ty (suc Δ₀))
  → repoint? resolve target birth anchor-map route live-ren (`∀ A)
    ≡ all? (repoint? resolve target (nothing Vec.∷ birth) anchor-map
      (ext-route route) (λ X → suc (live-ren X)) A)
repoint?-all resolve target birth anchor-map route live-ren A
    with repoint? resolve target (nothing Vec.∷ birth) anchor-map
      (ext-route route) (λ X → suc (live-ren X)) A
repoint?-all resolve target birth anchor-map route live-ren A
    | nothing = refl
repoint?-all resolve target birth anchor-map route live-ren A
    | just A′ = refl

rename-all? : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
    (value : Maybe (Ty (suc Δ)))
  → all? (mapMaybe (renameᵗ (extᵗ ρ)) value)
    ≡ mapMaybe (renameᵗ ρ) (all? value)
rename-all? ρ nothing = refl
rename-all? ρ (just A) = refl

rename-all?-keep : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (value : Maybe (Ty (suc Δ)))
  → all? (mapMaybe (renameᵗ (toRenameᵗ (keep ρ))) value)
    ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (all? value)
rename-all?-keep ρ nothing = refl
rename-all?-keep ρ (just A) =
  cong (λ B → just (`∀ B))
    (renameᵗ-cong A (toRename-keep-eq ρ))

repoint?-route-cong : ∀ {Θ₀ Θ Δ₀ Δ Δout}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (left right : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A : Ty Δ₀)
  → (∀ X → left X ≡ right X)
  → repoint? resolve target birth anchor-map left live-ren A
    ≡ repoint? resolve target birth anchor-map right live-ren A
repoint?-route-cong resolve target birth anchor-map left right
    live-ren (＇ X) eq
    with Vec.lookup birth X
repoint?-route-cong resolve target birth anchor-map left right
    live-ren (＇ X) eq
    | nothing with left X | right X | eq X
repoint?-route-cong resolve target birth anchor-map left right live-ren (＇ X) eq
    | nothing | nothing | .nothing | refl = refl
repoint?-route-cong resolve target birth anchor-map left right live-ren (＇ X) eq
    | nothing | just Y | .(just Y) | refl = refl
repoint?-route-cong resolve target birth anchor-map left right live-ren (＇ X) eq
    | just q = refl
repoint?-route-cong resolve target birth anchor-map left right live-ren (‵ ι) eq = refl
repoint?-route-cong resolve target birth anchor-map left right live-ren ★ eq = refl
repoint?-route-cong resolve target birth anchor-map left right live-ren (A ⇒ B) eq =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-route-cong resolve target birth anchor-map left right live-ren A eq)
        (repoint?-route-cong resolve target birth anchor-map left right live-ren B eq))
      (sym (repoint?-arrow _ _ _ _ _ _ A B)))
repoint?-route-cong resolve target birth anchor-map left right live-ren (`∀ A) eq =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (repoint?-route-cong resolve target (nothing Vec.∷ birth)
          anchor-map (ext-route left) (ext-route right)
          (λ X → suc (live-ren X)) A ext-eq))
      (sym (repoint?-all _ _ _ _ _ _ A)))
  where
  ext-eq : ∀ X → ext-route _ X ≡ ext-route _ X
  ext-eq zero = refl
  ext-eq (suc X) = cong (mapMaybe suc) (eq X)

repoint?-anchor-cong : ∀ {Θ₀ Θ Δ₀ Δ Δout}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (left right : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A : Ty Δ₀)
  → (∀ q → left q ≡ right q)
  → repoint? resolve target birth left route live-ren A
    ≡ repoint? resolve target birth right route live-ren A
repoint?-anchor-cong resolve target birth left right route live-ren
    (＇ X) eq with Vec.lookup birth X
repoint?-anchor-cong resolve target birth left right route live-ren
    (＇ X) eq | nothing = refl
repoint?-anchor-cong resolve target birth left right route live-ren
    (＇ X) eq | just q
    with left (suc q) | right (suc q) | eq (suc q)
repoint?-anchor-cong resolve target birth left right route live-ren
    (＇ X) eq | just q | anchor | .anchor | refl = refl
repoint?-anchor-cong resolve target birth left right route live-ren
    (‵ ι) eq = refl
repoint?-anchor-cong resolve target birth left right route live-ren ★ eq = refl
repoint?-anchor-cong resolve target birth left right route live-ren
    (A ⇒ B) eq =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-anchor-cong resolve target birth left right route
          live-ren A eq)
        (repoint?-anchor-cong resolve target birth left right route
          live-ren B eq))
      (sym (repoint?-arrow _ _ _ _ _ _ A B)))
repoint?-anchor-cong resolve target birth left right route live-ren
    (`∀ A) eq =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (repoint?-anchor-cong resolve target (nothing Vec.∷ birth)
          left right (ext-route route) (λ X → suc (live-ren X)) A eq))
      (sym (repoint?-all _ _ _ _ _ _ A)))

scanRep?-anchor-cong : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : TyEnv Θ Δ σ) (current : TyEnv Θ₀ Δ₀ σ₀)
    (left right : TyVar Θ₀ → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → (∀ q → left q ≡ right q)
  → scanRep? resolve target current left route a
    ≡ scanRep? resolve target current right route a
scanRep?-anchor-cong resolve target ∅ left right route () eq
scanRep?-anchor-cong resolve target
    (Ψ ,begin[ Y ≔ q ]⟨ fresh ⟩) left right route a eq =
  scanRep?-anchor-cong resolve target Ψ left right
    (λ X → route (punchIn Y X)) a eq
scanRep?-anchor-cong resolve target (Ψ ,typ) left right route a eq =
  scanRep?-anchor-cong resolve target Ψ left right
    (λ X → route (suc X)) a eq
scanRep?-anchor-cong resolve target (Ψ ,:= A) left right route zero eq =
  repoint?-anchor-cong resolve _ _ left right route (λ X → X) A eq
scanRep?-anchor-cong resolve target (Ψ ,:= A) left right route
    (suc a) eq =
  scanRep?-anchor-cong resolve target Ψ (λ q → left (suc q))
    (λ q → right (suc q)) route a (λ q → eq (suc q))
scanRep?-anchor-cong resolve target (Ψ ,end[ Y ]) left right route a eq =
  scanRep?-anchor-cong resolve target Ψ left right
    (route-end Y route) a eq

-- Regular injections preserve the evaluator's anchor-directed choice.  The
-- naturality proof is indexed by the number of surrounding type binders:
-- `raise n` embeds query slots below them and `lift↪ᵗ n` transports the
-- corresponding output.  This makes the universal-type case structural.
raise : ∀ {D} (n : TyCtx) → TyVar D → TyVar (n + D)
raise zero X = X
raise (suc n) X = suc (raise n X)

lift↪ᵗ : ∀ {Δ Δ′} (n : TyCtx) → Δ ↪ᵗ Δ′ → (n + Δ) ↪ᵗ (n + Δ′)
lift↪ᵗ zero ρ = ρ
lift↪ᵗ (suc n) ρ = keep (lift↪ᵗ n ρ)

raise-rename : ∀ {Δ Δ′} (n : TyCtx) (ρ : Δ ↪ᵗ Δ′) X
  → toRenameᵗ (lift↪ᵗ n ρ) (raise n X) ≡ raise n (toRenameᵗ ρ X)
raise-rename zero ρ X = refl
raise-rename (suc n) ρ X = cong suc (raise-rename n ρ X)

rename-raise : ∀ {Δ Δ′} (n : TyCtx) (ρ : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (lift↪ᵗ n ρ)) (renameᵗ (raise n) A)
    ≡ renameᵗ (raise n) (renameᵗ (toRenameᵗ ρ) A)
rename-raise n ρ A =
  trans (renameᵗ-comp (raise n) (toRenameᵗ (lift↪ᵗ n ρ)) A)
    (trans (renameᵗ-cong A (raise-rename n ρ))
      (sym (renameᵗ-comp (toRenameᵗ ρ) (raise n) A)))

route-mapⁿ : ∀ {Δ₀ Δ Δ′} (n : TyCtx) (ρ : Δ ↪ᵗ Δ′)
  → (TyVar Δ₀ → Maybe (TyVar (n + Δ)))
  → TyVar Δ₀ → Maybe (TyVar (n + Δ′))
route-mapⁿ n ρ route X = mapMaybe (toRenameᵗ (lift↪ᵗ n ρ)) (route X)

route-map-ext : ∀ {Δ₀ Δ Δ′} (n : TyCtx) (ρ : Δ ↪ᵗ Δ′)
    (route : TyVar Δ₀ → Maybe (TyVar (n + Δ))) X
  → ext-route (route-mapⁿ n ρ route) X
    ≡ route-mapⁿ (suc n) ρ (ext-route route) X
route-map-ext n ρ route zero = refl
route-map-ext n ρ route (suc X) =
  mapMaybe-keep-tail (lift↪ᵗ n ρ) (route X)

repoint?-rename : ∀ {Θ₀ Θ Δ₀ Δ Δ′}
    (n : TyCtx) (ρ : Δ ↪ᵗ Δ′)
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar (n + Δ))) (A : Ty Δ₀)
  → repoint? (λ q → mapMaybe (renameᵗ (toRenameᵗ ρ)) (resolve q))
      (renameSlots ρ target) birth anchor-map (route-mapⁿ n ρ route)
      (raise n) A
    ≡ mapMaybe (renameᵗ (toRenameᵗ (lift↪ᵗ n ρ)))
        (repoint? resolve target birth anchor-map route (raise n) A)
repoint?-rename n ρ resolve target birth anchor-map route (＇ X)
    with Vec.lookup birth X
repoint?-rename n ρ resolve target birth anchor-map route (＇ X)
    | nothing with route X
repoint?-rename n ρ resolve target birth anchor-map route (＇ X)
    | nothing | nothing = refl
repoint?-rename n ρ resolve target birth anchor-map route (＇ X)
    | nothing | just Y = refl
repoint?-rename n ρ resolve target birth anchor-map route (＇ X)
    | just q rewrite liveSlot?-rename ρ target (anchor-map (suc q))
    with liveSlot? target (anchor-map (suc q))
repoint?-rename n ρ resolve target birth anchor-map route (＇ X)
    | just q | just Y = cong (λ Z → just (＇ Z)) (sym (raise-rename n ρ Y))
repoint?-rename n ρ resolve target birth anchor-map route (＇ X)
    | just q | nothing with resolve (anchor-map (suc q))
repoint?-rename n ρ resolve target birth anchor-map route (＇ X)
    | just q | nothing | nothing = refl
repoint?-rename n ρ resolve target birth anchor-map route (＇ X)
    | just q | nothing | just B = cong just (sym (rename-raise n ρ B))
repoint?-rename n ρ resolve target birth anchor-map route (‵ ι) = refl
repoint?-rename n ρ resolve target birth anchor-map route ★ = refl
repoint?-rename n ρ resolve target birth anchor-map route (A ⇒ B) =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-rename n ρ resolve target birth anchor-map route A)
        (repoint?-rename n ρ resolve target birth anchor-map route B))
      (trans (rename-⇒? (toRenameᵗ (lift↪ᵗ n ρ))
          (repoint? resolve target birth anchor-map route (raise n) A)
          (repoint? resolve target birth anchor-map route (raise n) B))
        (cong (mapMaybe (renameᵗ (toRenameᵗ (lift↪ᵗ n ρ))))
          (sym (repoint?-arrow resolve target birth anchor-map route
            (raise n) A B)))))
repoint?-rename n ρ resolve target birth anchor-map route (`∀ A) =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (trans (repoint?-route-cong _ _ _ _ _ _ _ A
            (route-map-ext n ρ route))
          (repoint?-rename (suc n) ρ resolve target
            (nothing Vec.∷ birth) anchor-map (ext-route route) A)))
      (trans (rename-all?-keep (lift↪ᵗ n ρ)
          (repoint? resolve target (nothing Vec.∷ birth) anchor-map
            (ext-route route) (raise (suc n)) A))
        (cong (mapMaybe (renameᵗ (toRenameᵗ (lift↪ᵗ n ρ))))
          (sym (repoint?-all resolve target birth anchor-map route
            (raise n) A)))))

repoint?-resolve-cong : ∀ {Θ₀ Θ Δ₀ Δ Δout}
    {left right : TyVar Θ → Maybe (Ty Δ)}
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A : Ty Δ₀)
  → (∀ β → left β ≡ right β)
  → repoint? left target birth anchor-map route live-ren A
    ≡ repoint? right target birth anchor-map route live-ren A
repoint?-resolve-cong target birth anchor-map route live-ren (＇ X) eq
    with Vec.lookup birth X
repoint?-resolve-cong target birth anchor-map route live-ren (＇ X) eq
    | nothing = refl
repoint?-resolve-cong target birth anchor-map route live-ren (＇ X) eq
    | just q with liveSlot? target (anchor-map (suc q))
repoint?-resolve-cong target birth anchor-map route live-ren (＇ X) eq
    | just q | just Y = refl
repoint?-resolve-cong {left = left} {right = right}
    target birth anchor-map route live-ren (＇ X) eq
    | just q | nothing
    with left (anchor-map (suc q)) | right (anchor-map (suc q))
       | eq (anchor-map (suc q))
repoint?-resolve-cong target birth anchor-map route live-ren (＇ X) eq
    | just q | nothing | nothing | .nothing | refl = refl
repoint?-resolve-cong target birth anchor-map route live-ren (＇ X) eq
    | just q | nothing | just B | .(just B) | refl = refl
repoint?-resolve-cong target birth anchor-map route live-ren (‵ ι) eq = refl
repoint?-resolve-cong target birth anchor-map route live-ren ★ eq = refl
repoint?-resolve-cong {left = left} {right = right}
    target birth anchor-map route live-ren (A ⇒ B) eq =
  trans (repoint?-arrow left target birth anchor-map route live-ren A B)
    (trans (cong₂ _⇒?_
        (repoint?-resolve-cong target birth anchor-map route live-ren A eq)
        (repoint?-resolve-cong target birth anchor-map route live-ren B eq))
      (sym (repoint?-arrow right target birth anchor-map route live-ren A B)))
repoint?-resolve-cong {left = left} {right = right}
    target birth anchor-map route live-ren (`∀ A) eq =
  trans (repoint?-all left target birth anchor-map route live-ren A)
    (trans (cong all?
        (repoint?-resolve-cong target (nothing Vec.∷ birth) anchor-map
          (ext-route route) (λ X → suc (live-ren X)) A eq))
      (sym (repoint?-all right target birth anchor-map route live-ren A)))

repoint?-wk : ∀ {Θ₀ Θ Δ₀ Δ}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (A : Ty Δ₀)
  → repoint? (λ q → mapMaybe (renameᵗ (toRenameᵗ wk↪ᵗ)) (resolve q))
      (nothing Vec.∷ target) birth anchor-map (route-map wk↪ᵗ route)
      (λ X → X) A
    ≡ mapMaybe (renameᵗ (toRenameᵗ wk↪ᵗ))
        (repoint? resolve target birth anchor-map route (λ X → X) A)
repoint?-wk resolve target birth anchor-map route A =
  subst≡
    (λ slots → repoint?
      (λ q → mapMaybe (renameᵗ (toRenameᵗ wk↪ᵗ)) (resolve q))
      slots birth anchor-map (route-map wk↪ᵗ route) (λ X → X) A
      ≡ mapMaybe (renameᵗ (toRenameᵗ wk↪ᵗ))
          (repoint? resolve target birth anchor-map route (λ X → X) A))
    (cong (nothing Vec.∷_) (renameSlots-id target))
    (repoint?-rename zero wk↪ᵗ resolve target birth anchor-map route A)

scanRep?-resolve-cong : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
    {left right : TyVar Θ → Maybe (Ty Δ)}
    (target : TyEnv Θ Δ σ) (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → (∀ β → left β ≡ right β)
  → scanRep? left target current anchor-map route a
    ≡ scanRep? right target current anchor-map route a
scanRep?-resolve-cong target ∅ anchor-map route () eq
scanRep?-resolve-cong target (Ψ ,begin[ Y ≔ q ]⟨ fresh ⟩)
    anchor-map route a eq =
  scanRep?-resolve-cong target Ψ anchor-map
    (λ X → route (punchIn Y X)) a eq
scanRep?-resolve-cong target (Ψ ,typ) anchor-map route a eq =
  scanRep?-resolve-cong target Ψ anchor-map (λ X → route (suc X)) a eq
scanRep?-resolve-cong target (Ψ ,:= A) anchor-map route zero eq =
  repoint?-resolve-cong _ _ _ _ _ A eq
scanRep?-resolve-cong target (Ψ ,:= A) anchor-map route (suc a) eq =
  scanRep?-resolve-cong target Ψ (λ β → anchor-map (suc β)) route a eq
scanRep?-resolve-cong target (Ψ ,end[ Y ]) anchor-map route a eq =
  scanRep?-resolve-cong target Ψ anchor-map (route-end Y route) a eq

scanRep?-route-cong : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : TyEnv Θ Δ σ) (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (left right : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → (∀ X → left X ≡ right X)
  → scanRep? resolve target current anchor-map left a
    ≡ scanRep? resolve target current anchor-map right a
scanRep?-route-cong resolve target ∅ anchor-map left right () eq
scanRep?-route-cong resolve target (Ψ ,begin[ Y ≔ q ]⟨ fresh ⟩)
    anchor-map left right a eq =
  scanRep?-route-cong resolve target Ψ anchor-map
    (λ X → left (punchIn Y X)) (λ X → right (punchIn Y X))
    a (λ X → eq (punchIn Y X))
scanRep?-route-cong resolve target (Ψ ,typ) anchor-map left right a eq =
  scanRep?-route-cong resolve target Ψ anchor-map
    (λ X → left (suc X)) (λ X → right (suc X)) a
    (λ X → eq (suc X))
scanRep?-route-cong resolve target (Ψ ,:= A) anchor-map left right zero eq =
  repoint?-route-cong resolve _ _ _ left right (λ X → X) A eq
scanRep?-route-cong resolve target (Ψ ,:= A) anchor-map left right
    (suc a) eq =
  scanRep?-route-cong resolve target Ψ (λ q → anchor-map (suc q))
    left right a eq
scanRep?-route-cong resolve target (Ψ ,end[ Y ]) anchor-map left right a eq =
  scanRep?-route-cong resolve target Ψ anchor-map
    (route-end Y left) (route-end Y right) a end-eq
  where
  end-eq : ∀ X → route-end Y left X ≡ route-end Y right X
  end-eq X with Y ≟ X
  end-eq .Y | yes refl = refl
  end-eq X | no Y≢X = eq (punchOut Y X Y≢X)

scanRep?-wk : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : TyEnv Θ Δ σ) (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → scanRep? (λ β → mapMaybe (renameᵗ (toRenameᵗ wk↪ᵗ)) (resolve β))
      (target ,typ) current anchor-map (route-map wk↪ᵗ route) a
    ≡ mapMaybe (renameᵗ (toRenameᵗ wk↪ᵗ))
        (scanRep? resolve target current anchor-map route a)
scanRep?-wk resolve target ∅ anchor-map route ()
scanRep?-wk resolve target (Ψ ,begin[ Y ≔ q ]⟨ fresh ⟩)
    anchor-map route a =
  scanRep?-wk resolve target Ψ anchor-map
    (λ X → route (punchIn Y X)) a
scanRep?-wk resolve target (Ψ ,typ) anchor-map route a =
  scanRep?-wk resolve target Ψ anchor-map (λ X → route (suc X)) a
scanRep?-wk {σ = σ} resolve target (Ψ ,:= A) anchor-map route zero
  = repoint?-wk resolve σ _ _ route A
scanRep?-wk resolve target (Ψ ,:= A) anchor-map route (suc a) =
  scanRep?-wk resolve target Ψ (λ β → anchor-map (suc β)) route a
scanRep?-wk resolve target (Ψ ,end[ Y ]) anchor-map route a =
  trans (scanRep?-route-cong
      (λ q → mapMaybe (renameᵗ (toRenameᵗ wk↪ᵗ)) (resolve q))
      (target ,typ) Ψ anchor-map
      (route-end Y (route-map wk↪ᵗ route))
      (route-map wk↪ᵗ (route-end Y route)) a
      (route-end-map wk↪ᵗ Y route))
    (scanRep?-wk resolve target Ψ anchor-map (route-end Y route) a)

repFuel?-typ : ∀ fuel {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) a
  → repFuel? fuel (Ψ ,typ) a
    ≡ mapMaybe (renameᵗ (toRenameᵗ wk↪ᵗ)) (repFuel? fuel Ψ a)
repFuel?-typ zero Ψ a = refl
repFuel?-typ (suc fuel) Ψ a =
  trans (scanRep?-route-cong _ (Ψ ,typ) Ψ (λ q → q)
      (λ X → just (suc X)) (route-map wk↪ᵗ (λ X → just X)) a
      (λ X → cong (λ Y → just (suc Y)) (sym (toRename-id-eq X))))
    (trans (scanRep?-resolve-cong (Ψ ,typ) Ψ (λ q → q)
        (route-map wk↪ᵗ (λ X → just X)) a
        (λ q → repFuel?-typ fuel Ψ q))
      (scanRep?-wk (repFuel? fuel Ψ) Ψ Ψ (λ q → q)
        (λ X → just X) a))

rep?-typ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {α : TyVar Θ} {A : Ty Δ}
  → rep? Ψ α ≡ just A
  → rep? (Ψ ,typ) α ≡ just (⇑ᵗ A)
rep?-typ {Θ = Θ} {Ψ = Ψ} {α = α} {A = A} eq =
  trans (repFuel?-typ (Θ ∸ toℕ α) Ψ α)
    (trans (cong (mapMaybe (renameᵗ (toRenameᵗ wk↪ᵗ))) eq)
      (cong just (renameᵗ-wk-eq A)))

------------------------------------------------------------------------
-- Evaluator transport through a fresh newest anchor
------------------------------------------------------------------------

fin-suc-injective : ∀ {n} {X Y : TyVar n} → suc X ≡ suc Y → X ≡ Y
fin-suc-injective refl = refl

liveSlot?-shift : ∀ {Θ Δ}
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ) (a : TyVar Θ)
  → liveSlot? (mapᵛ (mapMaybe suc) slots) (suc a) ≡ liveSlot? slots a
liveSlot?-shift Vec.[] a = refl
liveSlot?-shift (nothing Vec.∷ slots) a
    rewrite liveSlot?-shift slots a = refl
liveSlot?-shift (just q Vec.∷ slots) a with a ≟ q | suc a ≟ suc q
liveSlot?-shift (just q Vec.∷ slots) .q | yes refl | yes refl = refl
liveSlot?-shift (just q Vec.∷ slots) .q | yes refl | no neq =
  ⊥-elim (neq refl)
liveSlot?-shift (just q Vec.∷ slots) a | no neq | yes eq =
  ⊥-elim (neq (fin-suc-injective eq))
liveSlot?-shift (just q Vec.∷ slots) a | no neq | no _
    rewrite liveSlot?-shift slots a = refl

repoint?-shift : ∀ {Θ₀ Θ Δ₀ Δ Δout}
    (old : TyVar Θ → Maybe (Ty Δ))
    (new : TyVar (suc Θ) → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A : Ty Δ₀)
  → (∀ q → new (suc q) ≡ old q)
  → repoint? new (mapᵛ (mapMaybe suc) target) birth
      (λ q → suc (anchor-map q)) route live-ren A
    ≡ repoint? old target birth anchor-map route live-ren A
repoint?-shift old new target birth anchor-map route live-ren (＇ X) eq
    with Vec.lookup birth X
repoint?-shift old new target birth anchor-map route live-ren (＇ X) eq
    | nothing = refl
repoint?-shift old new target birth anchor-map route live-ren (＇ X) eq
    | just q rewrite liveSlot?-shift target (anchor-map (suc q))
    with liveSlot? target (anchor-map (suc q))
repoint?-shift old new target birth anchor-map route live-ren (＇ X) eq
    | just q | just Y = refl
repoint?-shift old new target birth anchor-map route live-ren (＇ X) eq
    | just q | nothing
    with new (suc (anchor-map (suc q))) | old (anchor-map (suc q))
       | eq (anchor-map (suc q))
repoint?-shift old new target birth anchor-map route live-ren (＇ X) eq
    | just q | nothing | nothing | .nothing | refl = refl
repoint?-shift old new target birth anchor-map route live-ren (＇ X) eq
    | just q | nothing | just B | .(just B) | refl = refl
repoint?-shift old new target birth anchor-map route live-ren (‵ ι) eq = refl
repoint?-shift old new target birth anchor-map route live-ren ★ eq = refl
repoint?-shift old new target birth anchor-map route live-ren (A ⇒ B) eq =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-shift old new target birth anchor-map route live-ren A eq)
        (repoint?-shift old new target birth anchor-map route live-ren B eq))
      (sym (repoint?-arrow _ _ _ _ _ _ A B)))
repoint?-shift old new target birth anchor-map route live-ren (`∀ A) eq =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (repoint?-shift old new target (nothing Vec.∷ birth) anchor-map
          (ext-route route) (λ X → suc (live-ren X)) A eq))
      (sym (repoint?-all _ _ _ _ _ _ A)))

scanRep?-shift : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
    (old : TyVar Θ → Maybe (Ty Δ))
    (new : TyVar (suc Θ) → Maybe (Ty Δ))
    (target : TyEnv Θ Δ σ) (B : Ty Δ)
    (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → (∀ q → new (suc q) ≡ old q)
  → scanRep? new (target ,:= B) current (λ q → suc (anchor-map q)) route a
    ≡ scanRep? old target current anchor-map route a
scanRep?-shift old new target B ∅ anchor-map route () eq
scanRep?-shift old new target B (Ψ ,begin[ Y ≔ q ]⟨ fresh ⟩)
    anchor-map route a eq =
  scanRep?-shift old new target B Ψ anchor-map
    (λ X → route (punchIn Y X)) a eq
scanRep?-shift old new target B (Ψ ,typ) anchor-map route a eq =
  scanRep?-shift old new target B Ψ anchor-map (λ X → route (suc X)) a eq
scanRep?-shift old new target B (Ψ ,:= A) anchor-map route zero eq =
  repoint?-shift old new _ _ _ route (λ X → X) A eq
scanRep?-shift old new target B (Ψ ,:= A) anchor-map route (suc a) eq =
  scanRep?-shift old new target B Ψ (λ q → anchor-map (suc q)) route a eq
scanRep?-shift old new target B (Ψ ,end[ Y ]) anchor-map route a eq =
  scanRep?-shift old new target B Ψ anchor-map (route-end Y route) a eq

repFuel?-ν : ∀ fuel {Θ Δ σ} (Ψ : TyEnv Θ Δ σ)
    (B : Ty Δ) (a : TyVar Θ)
  → repFuel? fuel (Ψ ,:= B) (suc a) ≡ repFuel? fuel Ψ a
repFuel?-ν zero Ψ B a = refl
repFuel?-ν (suc fuel) Ψ B a =
  scanRep?-shift (repFuel? fuel Ψ) (repFuel? fuel (Ψ ,:= B))
    Ψ B Ψ (λ q → q) (λ X → just X) a
    (repFuel?-ν fuel Ψ B)

rep?-ν : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {B : Ty Δ}
    {a : TyVar Θ} {A : Ty Δ}
  → rep? Ψ a ≡ just A
  → rep? (Ψ ,:= B) (suc a) ≡ just A
rep?-ν {Θ = Θ} {Ψ = Ψ} {B = B} {a = a} eq =
  trans (repFuel?-ν (Θ ∸ toℕ a) Ψ B a) eq

------------------------------------------------------------------------
-- Evaluator transport through an end/re-begin pair
------------------------------------------------------------------------

reinsert-lookup : ∀ {n} {X : Set} (values : Vec.Vec X (suc n))
    (Y : TyVar (suc n))
  → insertᵛ Y (Vec.lookup values Y) (removeᵛ Y values) ≡ values
reinsert-lookup (value Vec.∷ values) zero = refl
reinsert-lookup {n = suc n} (value Vec.∷ values) (suc Y) =
  cong (value Vec.∷_) (reinsert-lookup values Y)

reinsert-alias : ∀ {Θ Δ} {slots : Vec.Vec (Maybe (TyVar Θ)) (suc Δ)}
    {Y : TyVar (suc Δ)} {a : TyVar Θ}
  → Vec.lookup slots Y ≡ just a
  → insertᵛ Y (just a) (removeᵛ Y slots) ≡ slots
reinsert-alias {slots = slots} {Y = Y} slot-eq =
  trans (cong (λ value → insertᵛ Y value (removeᵛ Y slots))
      (sym slot-eq))
    (reinsert-lookup slots Y)

punchIn≢ : ∀ {n} (Y : TyVar (suc n)) (X : TyVar n)
  → Y ≢ punchIn Y X
punchIn≢ zero X ()
punchIn≢ (suc Y) zero ()
punchIn≢ (suc Y) (suc X) eq =
  punchIn≢ Y X (fin-suc-injective eq)

punchOut-punchIn : ∀ {n} (Y : TyVar (suc n)) (X : TyVar n)
    (neq : Y ≢ punchIn Y X)
  → punchOut Y (punchIn Y X) neq ≡ X
punchOut-punchIn zero X neq = refl
punchOut-punchIn (suc Y) zero neq = refl
punchOut-punchIn (suc Y) (suc X) neq =
  cong suc (punchOut-punchIn Y X _)

punchIn-punchOut : ∀ {n} (Y X : TyVar (suc n)) (neq : Y ≢ X)
  → punchIn Y (punchOut Y X neq) ≡ X
punchIn-punchOut zero zero neq = ⊥-elim (neq refl)
punchIn-punchOut zero (suc X) neq = refl
punchIn-punchOut {n = suc n} (suc Y) zero neq = refl
punchIn-punchOut {n = suc n} (suc Y) (suc X) neq =
  cong suc (punchIn-punchOut Y X _)

route-end-punchIn : ∀ {Δ Δ′} (Y : TyVar (suc Δ))
    (route : TyVar Δ → Maybe (TyVar Δ′)) X
  → route-end Y route (punchIn Y X) ≡ route X
route-end-punchIn Y route X with Y ≟ punchIn Y X
route-end-punchIn Y route X | yes eq =
  ⊥-elim (punchIn≢ Y X eq)
route-end-punchIn Y route X | no neq =
  cong route (punchOut-punchIn Y X neq)

toRename-injective : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) {X Y}
  → toRenameᵗ ρ X ≡ toRenameᵗ ρ Y
  → X ≡ Y
toRename-injective empty {X = ()}
toRename-injective (skip ρ) eq =
  toRename-injective ρ (fin-suc-injective eq)
toRename-injective (keep ρ) {X = zero} {Y = zero} eq = refl
toRename-injective (keep ρ) {X = zero} {Y = suc Y} ()
toRename-injective (keep ρ) {X = suc X} {Y = zero} ()
toRename-injective (keep ρ) {X = suc X} {Y = suc Y} eq =
  cong suc (toRename-injective ρ (fin-suc-injective eq))

punchIn-injectiveᵗ : ∀ {Δ} (Y : TyVar (suc Δ)) {X Z}
  → punchIn Y X ≡ punchIn Y Z
  → X ≡ Z
punchIn-injectiveᵗ zero eq = fin-suc-injective eq
punchIn-injectiveᵗ (suc Y) {zero} {zero} eq = refl
punchIn-injectiveᵗ (suc Y) {zero} {suc z} ()
punchIn-injectiveᵗ (suc Y) {suc X} {zero} ()
punchIn-injectiveᵗ (suc Y) {suc X} {suc z} eq =
  cong suc (punchIn-injectiveᵗ Y (fin-suc-injective eq))

reentry-route : ∀ {Δ Δ′ Δ″ D}
    (ρ : suc Δ ↪ᵗ suc Δ′) (η : Δ′ ↪ᵗ Δ″)
    (Y X : TyVar (suc Δ)) (neq : Y ≢ X)
    (route : TyVar (suc Δ″) → Maybe (TyVar D))
  → route-end (toRenameᵗ ρ Y)
      (λ Z → route
        (punchIn
          (toRenameᵗ (insert↪ᵗ (delete↪ᵗ ρ Y ⨟↪ᵗ η) Y) Y)
          (toRenameᵗ η Z)))
      (toRenameᵗ ρ X)
    ≡ route (toRenameᵗ
        (insert↪ᵗ (delete↪ᵗ ρ Y ⨟↪ᵗ η) Y) X)
reentry-route ρ η Y X neq route
    with toRenameᵗ ρ Y ≟ toRenameᵗ ρ X
reentry-route ρ η Y X neq route | yes eq =
  ⊥-elim (neq (toRename-injective ρ eq))
reentry-route ρ η Y X neq route | no image-neq =
  cong route target-eq
  where
  reduced = punchOut Y X neq
  old = toRenameᵗ ρ Y
  deleted = delete↪ᵗ ρ Y
  combined = deleted ⨟↪ᵗ η
  inserted = insert↪ᵗ combined Y
  new = toRenameᵗ inserted Y

  source-rebuild : punchIn Y reduced ≡ X
  source-rebuild = punchIn-punchOut Y X neq

  deleted-eq : punchOut old (toRenameᵗ ρ X) image-neq
      ≡ toRenameᵗ deleted reduced
  deleted-eq = punchIn-injectiveᵗ old
    (trans (punchIn-punchOut old (toRenameᵗ ρ X) image-neq)
      (trans (cong (toRenameᵗ ρ) (sym source-rebuild))
        (delete-punchIn ρ Y reduced)))

  target-eq : punchIn new
      (toRenameᵗ η (punchOut old (toRenameᵗ ρ X) image-neq))
      ≡ toRenameᵗ inserted X
  target-eq =
    trans (cong (λ Z → punchIn new (toRenameᵗ η Z)) deleted-eq)
      (trans (cong (punchIn new)
          (sym (toRename-compose deleted η reduced)))
        (trans (sym (insert-punchIn combined Y reduced))
          (cong (toRenameᵗ inserted) source-rebuild)))

lookup-insert-punch : ∀ {n} {X : Set} (Y : TyVar (suc n))
    (value : X) (values : Vec.Vec X n) (i : TyVar n)
  → Vec.lookup (insertᵛ Y value values) (punchIn Y i)
    ≡ Vec.lookup values i
lookup-insert-punch zero value values i = refl
lookup-insert-punch (suc Y) value (head Vec.∷ values) zero = refl
lookup-insert-punch (suc Y) value (head Vec.∷ values) (suc i) =
  lookup-insert-punch Y value values i

lookup-remove-punchOut : ∀ {n} {X : Set} (Y i : TyVar (suc n))
    (values : Vec.Vec X (suc n)) (neq : Y ≢ i)
  → Vec.lookup (removeᵛ Y values) (punchOut Y i neq)
    ≡ Vec.lookup values i
lookup-remove-punchOut zero zero values neq = ⊥-elim (neq refl)
lookup-remove-punchOut zero (suc i) (head Vec.∷ values) neq = refl
lookup-remove-punchOut {n = suc n} (suc Y) zero
    (head Vec.∷ values) neq = refl
lookup-remove-punchOut {n = suc n} (suc Y) (suc i)
    (head Vec.∷ values) neq =
  lookup-remove-punchOut Y i values _

lookup-mapᵛ : ∀ {n} {X Y : Set} (f : X → Y)
    (values : Vec.Vec X n) (i : TyVar n)
  → Vec.lookup (mapᵛ f values) i ≡ f (Vec.lookup values i)
lookup-mapᵛ f (value Vec.∷ values) zero = refl
lookup-mapᵛ f (value Vec.∷ values) (suc i) =
  lookup-mapᵛ f values i

lookup-insert-here : ∀ {n} {X : Set} (Y : TyVar (suc n))
    (value : X) (values : Vec.Vec X n)
  → Vec.lookup (insertᵛ Y value values) Y ≡ value
lookup-insert-here zero value values = refl
lookup-insert-here (suc Y) value (head Vec.∷ values) =
  lookup-insert-here Y value values

lookup-insert-other : ∀ {n} {X : Set} (Y i : TyVar (suc n))
    (value : X) (values : Vec.Vec X n) (neq : Y ≢ i)
  → Vec.lookup (insertᵛ Y value values) i
    ≡ Vec.lookup values (punchOut Y i neq)
lookup-insert-other Y i value values neq =
  trans (cong (Vec.lookup (insertᵛ Y value values))
      (sym (punchIn-punchOut Y i neq)))
    (lookup-insert-punch Y value values (punchOut Y i neq))

lookup-remove-punch : ∀ {n} {X : Set} (Y : TyVar (suc n))
    (values : Vec.Vec X (suc n)) i
  → Vec.lookup (removeᵛ Y values) i
    ≡ Vec.lookup values (punchIn Y i)
lookup-remove-punch zero (head Vec.∷ values) i = refl
lookup-remove-punch (suc Y) (head Vec.∷ values) zero = refl
lookup-remove-punch (suc Y) (head Vec.∷ values) (suc i) =
  lookup-remove-punch Y values i

-- A begin/end pair deletes exactly the position it inserted.  Every older
-- slot therefore follows the composite injection displayed by ≼-begin-end.
begin-end-old-position : ∀ {Δ Δ′ Δ″}
    (ρ : Δ ↪ᵗ Δ′) (η : suc Δ′ ↪ᵗ suc Δ″)
    (Z : TyVar (suc Δ′)) (X : TyVar Δ)
  → punchIn (toRenameᵗ η Z)
      (toRenameᵗ (ρ ⨟↪ᵗ delete↪ᵗ η Z) X)
    ≡ toRenameᵗ η (punchIn Z (toRenameᵗ ρ X))
begin-end-old-position ρ η z x =
  trans (cong (punchIn (toRenameᵗ η z))
      (toRename-compose ρ (delete↪ᵗ η z) x))
    (sym (delete-punchIn η z (toRenameᵗ ρ x)))

-- Dually, an end/re-begin pair sends every slot other than the consumed one
-- around the new crossing.  This is the positional content of reentry-route.
end-begin-old-position : ∀ {Δ Δ′ Δ″}
    (ρ : suc Δ ↪ᵗ suc Δ′) (η : Δ′ ↪ᵗ Δ″)
    (X Y : TyVar (suc Δ)) (neq : X ≢ Y)
    (image-neq : toRenameᵗ ρ X ≢ toRenameᵗ ρ Y)
  → punchIn
      (toRenameᵗ (insert↪ᵗ (delete↪ᵗ ρ X ⨟↪ᵗ η) X) X)
      (toRenameᵗ η
        (punchOut (toRenameᵗ ρ X) (toRenameᵗ ρ Y) image-neq))
    ≡ toRenameᵗ (insert↪ᵗ (delete↪ᵗ ρ X ⨟↪ᵗ η) X) Y
end-begin-old-position ρ η x y neq image-neq =
  trans (cong (λ z → punchIn new (toRenameᵗ η z)) deleted-eq)
    (trans (cong (punchIn new)
        (sym (toRename-compose deleted η reduced)))
      (trans (sym (insert-punchIn combined x reduced))
        (cong (toRenameᵗ inserted) source-rebuild)))
  where
  reduced = punchOut x y neq
  old = toRenameᵗ ρ x
  deleted = delete↪ᵗ ρ x
  combined = deleted ⨟↪ᵗ η
  inserted = insert↪ᵗ combined x
  new = toRenameᵗ inserted x

  source-rebuild : punchIn x reduced ≡ y
  source-rebuild = punchIn-punchOut x y neq

  deleted-eq : punchOut old (toRenameᵗ ρ y) image-neq
      ≡ toRenameᵗ deleted reduced
  deleted-eq = punchIn-injectiveᵗ old
    (trans (punchIn-punchOut old (toRenameᵗ ρ y) image-neq)
      (trans (cong (toRenameᵗ ρ) (sym source-rebuild))
        (delete-punchIn ρ x reduced)))

AliasUnique-insert : ∀ {Θ Δ}
    {slots : Vec.Vec (Maybe (TyVar Θ)) Δ} {a : TyVar Θ}
  → AliasUnique slots
  → a ∉ᵛ slots
  → (Y : TyVar (suc Δ))
  → AliasUnique (insertᵛ Y (just a) slots)
AliasUnique-insert {slots = slots} {a = a} unique fresh Y
    {X = x-index} {Y = z-index} {a = q} left right
    with Y ≟ x-index | Y ≟ z-index
AliasUnique-insert {slots = slots} unique fresh Y left right
    | yes refl | yes refl = refl
AliasUnique-insert {slots = slots} {a = a} unique fresh Y left right
    | yes refl | no Y≢Z =
  ⊥-elim (fresh (punchOut Y _ Y≢Z) old-a)
  where
  q≡a = just-injective
    (trans (sym left) (lookup-insert-here Y (just a) slots))
  old-q = trans (sym (lookup-insert-other Y _ (just a) slots Y≢Z)) right
  old-a = trans old-q (cong just q≡a)
AliasUnique-insert {slots = slots} {a = a} unique fresh Y left right
    | no Y≢X | yes refl =
  ⊥-elim (fresh (punchOut Y _ Y≢X) old-a)
  where
  q≡a = just-injective
    (trans (sym right) (lookup-insert-here Y (just a) slots))
  old-q = trans (sym (lookup-insert-other Y _ (just a) slots Y≢X)) left
  old-a = trans old-q (cong just q≡a)
AliasUnique-insert {slots = slots} unique fresh Y left right
    | no Y≢X | no Y≢Z =
  trans (sym (punchIn-punchOut Y _ Y≢X))
    (trans (cong (punchIn Y) (unique old-left old-right))
      (punchIn-punchOut Y _ Y≢Z))
  where
  old-left = trans
    (sym (lookup-insert-other Y _ _ slots Y≢X)) left
  old-right = trans
    (sym (lookup-insert-other Y _ _ slots Y≢Z)) right

AliasUnique-insert-nothing : ∀ {Θ Δ}
    {slots : Vec.Vec (Maybe (TyVar Θ)) Δ}
  → AliasUnique slots
  → AliasUnique (nothing Vec.∷ slots)
AliasUnique-insert-nothing unique {X = zero} () right
AliasUnique-insert-nothing unique {X = suc X} {Y = zero} left ()
AliasUnique-insert-nothing unique {X = suc X} {Y = suc Y} left right =
  cong suc (unique left right)

mapMaybe-suc-inverse : ∀ {n} {value : Maybe (TyVar n)} {a}
  → mapMaybe suc value ≡ just a
  → ∃[ x ] (value ≡ just x × suc x ≡ a)
mapMaybe-suc-inverse {value = nothing} ()
mapMaybe-suc-inverse {value = just x} eq =
  x , refl , just-injective eq

AliasUnique-map-suc : ∀ {Θ Δ}
    {slots : Vec.Vec (Maybe (TyVar Θ)) Δ}
  → AliasUnique slots
  → AliasUnique (mapᵛ (mapMaybe suc) slots)
AliasUnique-map-suc {slots = slots} unique {X = x-index} {Y = y-index}
    left right
    with mapMaybe-suc-inverse
      (trans (sym (lookup-mapᵛ (mapMaybe suc) slots x-index)) left)
       | mapMaybe-suc-inverse
      (trans (sym (lookup-mapᵛ (mapMaybe suc) slots y-index)) right)
AliasUnique-map-suc unique left right
    | x , left-source , suc-x | y , right-source , suc-y
    with suc-injective (trans suc-x (sym suc-y))
AliasUnique-map-suc unique left right
    | x , left-source , suc-x | .x , right-source , suc-y | refl =
  unique left-source right-source

AliasUnique-remove : ∀ {Θ Δ}
    {slots : Vec.Vec (Maybe (TyVar Θ)) (suc Δ)}
  → AliasUnique slots
  → (Y : TyVar (suc Δ))
  → AliasUnique (removeᵛ Y slots)
AliasUnique-remove {slots = slots} unique Y {X = x-index} {Y = z-index}
    left right =
  punchIn-injectiveᵗ Y
    (unique
      (trans (sym (lookup-remove-punch Y slots x-index)) left)
      (trans (sym (lookup-remove-punch Y slots z-index)) right))

aliases-unique-ν : ∀ {Θ Δ σ} (Ψ : TyEnv Θ Δ σ)
  → AliasUnique σ
  → AliasUnique (mapᵛ (mapMaybe suc) σ)
aliases-unique-ν {σ = σ} Ψ = AliasUnique-map-suc {slots = σ}

aliases-unique : ∀ {Θ Δ σ} (Ψ : TyEnv Θ Δ σ)
  → AliasUnique σ
aliases-unique ∅ {X = ()}
aliases-unique (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩) =
  AliasUnique-insert (aliases-unique Ψ) fresh Y
aliases-unique (Ψ ,typ) = AliasUnique-insert-nothing (aliases-unique Ψ)
aliases-unique (Ψ ,:= A) = aliases-unique-ν Ψ (aliases-unique Ψ)
aliases-unique (Ψ ,end[ Y ]) = AliasUnique-remove (aliases-unique Ψ) Y

shifted-compose : ∀ {Θ₀ Θ₁ Θ₂ k k′}
    {a : TyVar Θ₀} {b : TyVar Θ₁} {c : TyVar Θ₂}
  → Shifted k a b
  → Shifted k′ b c
  → Shifted (k + k′) a c
shifted-compose {Θ₀ = Θ₀} {Θ₂ = Θ₂} {k = k} {a = a} {c = c}
    left shifted-zero =
  subst≡ (λ n → Shifted {Θ = Θ₀} {Θ′ = Θ₂} n a c)
    (sym (+-identityʳ k)) left
shifted-compose {Θ₀ = Θ₀} {Θ₂ = suc Θ₂} {k = k} {k′ = suc k′}
    {a = a} {c = suc c} left (shifted-suc right) =
  subst≡ (λ n → Shifted {Θ = Θ₀} {Θ′ = suc Θ₂} n a (suc c))
    (sym (+-suc k k′))
    (shifted-suc (shifted-compose left right))

shiftAlong-shifted : ∀ {Θ Θ′ Δ Δ′ σ σ′ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (extension : Ψ ≼[ k , ρ ] Φ) a
  → Shifted k a (shiftAlong extension a)
shiftAlong-shifted ≼-refl a = shifted-zero
shiftAlong-shifted (≼-ν extension) a =
  shifted-suc (shiftAlong-shifted extension a)
shiftAlong-shifted (≼-typ extension) a =
  shiftAlong-shifted extension a
shiftAlong-shifted (≼-begin-end extension region) a =
  shifted-compose (shiftAlong-shifted extension a)
    (shiftAlong-shifted region (shiftAlong extension a))
shiftAlong-shifted (≼-end-begin slot-eq extension region shifted) a =
  shifted-compose (shiftAlong-shifted extension a)
    (shiftAlong-shifted region (shiftAlong extension a))

shifted-unique : ∀ {Θ Θ′ k} {a : TyVar Θ} {b c : TyVar Θ′}
  → Shifted k a b
  → Shifted k a c
  → b ≡ c
shifted-unique shifted-zero shifted-zero = refl
shifted-unique (shifted-suc left) (shifted-suc right) =
  cong suc (shifted-unique left right)

shifted-source-injective : ∀ {Θ Θ′ k}
    {a b : TyVar Θ} {c : TyVar Θ′}
  → Shifted k a c
  → Shifted k b c
  → a ≡ b
shifted-source-injective shifted-zero shifted-zero = refl
shifted-source-injective (shifted-suc left) (shifted-suc right) =
  shifted-source-injective left right

shiftAlong-injective : ∀ {Θ Θ′ Δ Δ′ σ σ′ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (extension : Ψ ≼[ k , ρ ] Φ) {a b}
  → shiftAlong extension a ≡ shiftAlong extension b
  → a ≡ b
shiftAlong-injective extension eq =
  shifted-source-injective (shiftAlong-shifted extension _)
    (subst≡ (Shifted _ _) (sym eq) (shiftAlong-shifted extension _))

shifted-along : ∀ {Θ Θ′ Δ Δ′ σ σ′ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    {a : TyVar Θ} {b : TyVar Θ′}
  → (extension : Ψ ≼[ k , ρ ] Φ)
  → Shifted k a b
  → b ≡ shiftAlong extension a
shifted-along extension shifted =
  shifted-unique shifted (shiftAlong-shifted extension _)

slotsOf : ∀ {Θ Δ σ} → TyEnv Θ Δ σ
  → Vec.Vec (Maybe (TyVar Θ)) Δ
slotsOf {σ = σ} Ψ = σ

mutual
  slot-forward-≼ : ∀ {Θ Θ′ Δ Δ′ σ σ′ k}
      {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
      (extension : Ψ ≼[ k , ρ ] Φ) {X a}
    → Vec.lookup σ X ≡ just a
    → Vec.lookup σ′ (toRenameᵗ ρ X)
      ≡ just (shiftAlong extension a)
  slot-forward-≼ {σ = slots} ≼-refl {X = X} lookup-eq =
    trans (cong (Vec.lookup slots) (toRename-id-eq X)) lookup-eq
  slot-forward-≼
      (≼-ν {ρ = ρ} {Ψ′ = Φ} {B = B} extension) {X = X} lookup-eq =
    trans (lookup-mapᵛ (mapMaybe suc) (slotsOf Φ) (toRenameᵗ ρ X))
      (cong (mapMaybe suc) (slot-forward-≼ extension lookup-eq))
  slot-forward-≼ (≼-typ extension) lookup-eq =
    slot-forward-≼ extension lookup-eq
  slot-forward-≼
      (≼-begin-end {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″} {Z = z}
        extension region)
      {X = X} lookup-eq =
    trans (lookup-remove-punch (toRenameᵗ η z) (slotsOf Ψ″)
        (toRenameᵗ (ρ ⨟↪ᵗ delete↪ᵗ η z) X))
      (trans (cong (Vec.lookup (slotsOf Ψ″))
          (begin-end-old-position ρ η z X))
        (slot-forward-≼ region
          (trans (lookup-insert-punch z _ (slotsOf Ψ′)
              (toRenameᵗ ρ X))
            (slot-forward-≼ extension lookup-eq))))
  slot-forward-≼
      (≼-end-begin {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″}
        {X = pivot} slot-eq extension region shifted)
      {X = X} lookup-eq with pivot ≟ X
  slot-forward-≼
      (≼-end-begin {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″}
        {X = pivot} {fresh = fresh} slot-eq extension region shifted)
      {X = .pivot} lookup-eq | yes refl =
    trans (lookup-insert-here new (just _) (slotsOf Ψ″))
      (cong just
        (trans (shifted-along full-extension shifted)
          (cong (shiftAlong full-extension) (sym a≡α))))
    where
    full-extension =
      ≼-end-begin {fresh = fresh} slot-eq extension region shifted
    inserted = insert↪ᵗ (delete↪ᵗ ρ pivot ⨟↪ᵗ η) pivot
    new = toRenameᵗ inserted pivot
    a≡α = just-injective (trans (sym lookup-eq) slot-eq)
  slot-forward-≼
      (≼-end-begin {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″}
        {X = pivot} slot-eq extension region shifted)
      {X = X} lookup-eq | no pivot≢X =
    trans (cong (Vec.lookup (insertᵛ new (just _) (slotsOf Ψ″)))
        (sym position-eq))
      (trans (lookup-insert-punch new _ (slotsOf Ψ″) routed)
        (slot-forward-≼ region ended-eq))
    where
    old = toRenameᵗ ρ pivot
    image = toRenameᵗ ρ X
    image-neq : old ≢ image
    image-neq eq = pivot≢X (toRename-injective ρ eq)
    routed = toRenameᵗ η (punchOut old image image-neq)
    inserted = insert↪ᵗ (delete↪ᵗ ρ pivot ⨟↪ᵗ η) pivot
    new = toRenameᵗ inserted pivot
    position-eq : punchIn new routed ≡ toRenameᵗ inserted X
    position-eq = end-begin-old-position ρ η pivot X pivot≢X image-neq
    ended-eq = trans
      (lookup-remove-punchOut old image (slotsOf Ψ′) image-neq)
      (slot-forward-≼ extension lookup-eq)

  slot-backward-≼ : ∀ {Θ Θ′ Δ Δ′ σ σ′ k}
      {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
      (extension : Ψ ≼[ k , ρ ] Φ) {Y a}
    → Vec.lookup σ′ Y ≡ just (shiftAlong extension a)
    → ∃[ X ] (Y ≡ toRenameᵗ ρ X × Vec.lookup σ X ≡ just a)
  slot-backward-≼ ≼-refl {Y = Y} lookup-eq =
    Y , sym (toRename-id-eq Y) , lookup-eq
  slot-backward-≼ (≼-ν {Ψ′ = Φ} extension) {Y = Y} lookup-eq
      with mapMaybe-suc-inverse
        (trans (sym (lookup-mapᵛ (mapMaybe suc) (slotsOf Φ) Y)) lookup-eq)
  slot-backward-≼ (≼-ν extension) lookup-eq
      | q , prefix-eq , suc-eq
      with slot-backward-≼ extension
        (trans prefix-eq (cong just (suc-injective suc-eq)))
  slot-backward-≼ (≼-ν extension) lookup-eq
      | q , prefix-eq , suc-eq | X , position-eq , source-eq =
    X , position-eq , source-eq
  slot-backward-≼ (≼-typ extension) {Y = zero} ()
  slot-backward-≼ (≼-typ extension) {Y = suc Y} lookup-eq
      with slot-backward-≼ extension lookup-eq
  slot-backward-≼ (≼-typ extension) {Y = suc Y} lookup-eq
      | X , position-eq , source-eq =
    X , cong suc position-eq , source-eq
  slot-backward-≼
      (≼-begin-end {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″} {Z = z}
        extension region)
      {Y = Y} lookup-eq
      with slot-backward-≼ region inside-eq
    where
    inside-eq = trans
      (sym (lookup-remove-punch (toRenameᵗ η z) (slotsOf Ψ″) Y))
      lookup-eq
  slot-backward-≼
      (≼-begin-end {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″} {Z = z}
        extension region)
      {Y = Y} lookup-eq
      | child , child-position , child-lookup with z ≟ child
  slot-backward-≼
      (≼-begin-end {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″} {Z = z}
        extension region)
      {Y = Y} lookup-eq
      | .z , child-position , child-lookup | yes refl =
    ⊥-elim (punchIn≢ (toRenameᵗ η z) Y (sym child-position))
  slot-backward-≼
      (≼-begin-end {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″} {Z = z}
        extension region)
      {Y = Y} lookup-eq
      | child , child-position , child-lookup | no z≢child
      with slot-backward-≼ extension prefix-lookup
    where
    prefix-lookup = trans
      (sym (lookup-insert-other z child _ (slotsOf Ψ′) z≢child))
      child-lookup
  slot-backward-≼
      (≼-begin-end {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″} {Z = z}
        extension region)
      {Y = Y} lookup-eq
      | child , child-position , child-lookup | no z≢child
      | X , prefix-position , source-lookup =
    X , final-position , source-lookup
    where
    reduced = punchOut z child z≢child
    child-rebuild : punchIn z reduced ≡ child
    child-rebuild = punchIn-punchOut z child z≢child
    reduced-position : Y ≡ toRenameᵗ (delete↪ᵗ η z) reduced
    reduced-position = punchIn-injectiveᵗ (toRenameᵗ η z)
      (trans child-position
        (trans (cong (toRenameᵗ η) (sym child-rebuild))
          (delete-punchIn η z reduced)))
    final-position : Y ≡ toRenameᵗ (ρ ⨟↪ᵗ delete↪ᵗ η z) X
    final-position =
      trans reduced-position
        (trans (cong (toRenameᵗ (delete↪ᵗ η z)) prefix-position)
          (sym (toRename-compose ρ (delete↪ᵗ η z) X)))
  slot-backward-≼
      (≼-end-begin {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″}
        {X = pivot} {fresh = fresh} slot-eq extension region shifted)
      {Y = Y} lookup-eq with new ≟ Y
    where
    inserted = insert↪ᵗ (delete↪ᵗ ρ pivot ⨟↪ᵗ η) pivot
    new = toRenameᵗ inserted pivot
  slot-backward-≼
      (≼-end-begin {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″}
        {X = pivot} {fresh = fresh} slot-eq extension region shifted)
      {Y = .(toRenameᵗ
        (insert↪ᵗ (delete↪ᵗ ρ pivot ⨟↪ᵗ η) pivot) pivot)}
      lookup-eq | yes refl =
    pivot , refl , trans slot-eq (cong just (sym a≡α))
    where
    full-extension =
      ≼-end-begin {fresh = fresh} slot-eq extension region shifted
    inserted = insert↪ᵗ (delete↪ᵗ ρ pivot ⨟↪ᵗ η) pivot
    new = toRenameᵗ inserted pivot
    β≡result = just-injective
      (trans (sym (lookup-insert-here new _ (slotsOf Ψ″))) lookup-eq)
    result≡α = trans (sym β≡result)
      (shifted-along full-extension shifted)
    a≡α = shiftAlong-injective full-extension result≡α
  slot-backward-≼
      (≼-end-begin {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″}
        {X = pivot} slot-eq extension region shifted)
      {Y = Y} lookup-eq | no new≢Y
      with slot-backward-≼ region region-lookup
    where
    inserted = insert↪ᵗ (delete↪ᵗ ρ pivot ⨟↪ᵗ η) pivot
    new = toRenameᵗ inserted pivot
    reduced = punchOut new Y new≢Y
    region-lookup = trans
      (sym (lookup-insert-other new Y _ (slotsOf Ψ″) new≢Y))
      lookup-eq
  slot-backward-≼
      (≼-end-begin {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″}
        {X = pivot} slot-eq extension region shifted)
      {Y = Y} lookup-eq | no new≢Y
      | ended , region-position , ended-lookup
      with slot-backward-≼ extension prefix-lookup
    where
    old = toRenameᵗ ρ pivot
    prefix-lookup = trans
      (sym (lookup-remove-punch old (slotsOf Ψ′) ended)) ended-lookup
  slot-backward-≼
      (≼-end-begin {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Ψ″ = Ψ″}
        {X = pivot} slot-eq extension region shifted)
      {Y = Y} lookup-eq | no new≢Y
      | ended , region-position , ended-lookup
      | X , prefix-position , source-lookup =
    X , final-position , source-lookup
    where
    old = toRenameᵗ ρ pivot
    image = toRenameᵗ ρ X
    pivot≢X : pivot ≢ X
    pivot≢X refl = punchIn≢ old ended (sym prefix-position)
    image-neq : old ≢ image
    image-neq eq = pivot≢X (toRename-injective ρ eq)
    ended-position : ended ≡ punchOut old image image-neq
    ended-position = punchIn-injectiveᵗ old
      (trans prefix-position
        (sym (punchIn-punchOut old image image-neq)))
    inserted = insert↪ᵗ (delete↪ᵗ ρ pivot ⨟↪ᵗ η) pivot
    new = toRenameᵗ inserted pivot
    final-position : Y ≡ toRenameᵗ inserted X
    final-position =
      trans (sym (punchIn-punchOut new Y new≢Y))
        (trans (cong (punchIn new) region-position)
          (trans (cong (λ z → punchIn new (toRenameᵗ η z))
              ended-position)
            (end-begin-old-position ρ η pivot X pivot≢X image-neq)))

liveSlot?-≼ : ∀ {Θ Θ′ Δ Δ′ σ σ′ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (extension : Ψ ≼[ k , ρ ] Φ) a
  → liveSlot? σ′ (shiftAlong extension a)
    ≡ mapMaybe (toRenameᵗ ρ) (liveSlot? σ a)
liveSlot?-≼ {σ = source} {σ′ = target} {ρ = ρ} {Ψ = Ψ} {Φ = Φ} extension a
    with liveSlot? source a in source-live
       | liveSlot? target (shiftAlong extension a) in target-live
liveSlot?-≼ {σ = source} {σ′ = target} {ρ = ρ} {Ψ = Ψ} {Φ = Φ} extension a
    | nothing | nothing = refl
liveSlot?-≼ {σ = source} {σ′ = target} {ρ = ρ} {Ψ = Ψ} {Φ = Φ} extension a
    | nothing | just Y =
  ⊥-elim (nothing≢just (trans (sym source-live) source-complete))
  where
  target-lookup = liveSlot?-sound target (shiftAlong extension a) Y
    target-live
  source-image = slot-backward-≼ extension target-lookup
  X = proj₁ source-image
  source-lookup = proj₂ (proj₂ source-image)
  source-complete = liveSlot?-complete source (aliases-unique Ψ)
    source-lookup
  nothing≢just : ∀ {A : Set} {x : A} → nothing ≢ just x
  nothing≢just ()
liveSlot?-≼ {σ = source} {σ′ = target} {ρ = ρ} {Ψ = Ψ} {Φ = Φ} extension a
    | just X | nothing =
  ⊥-elim (nothing≢just (trans (sym target-live) target-complete))
  where
  source-lookup = liveSlot?-sound source a X source-live
  target-lookup = slot-forward-≼ extension source-lookup
  target-complete = liveSlot?-complete target (aliases-unique Φ)
    target-lookup
  nothing≢just : ∀ {A : Set} {x : A} → nothing ≢ just x
  nothing≢just ()
liveSlot?-≼ {σ = source} {σ′ = target} {ρ = ρ} {Ψ = Ψ} {Φ = Φ} extension a
    | just X | just Y =
  cong just (liveSlot?-unique {σ = target}
    {α = shiftAlong extension a} target-live target-complete)
  where
  source-lookup = liveSlot?-sound source a X source-live
  target-lookup = slot-forward-≼ extension source-lookup
  target-complete = liveSlot?-complete target (aliases-unique Φ)
    target-lookup

-- Repointing is natural over a balanced extension.  Crossing variables are
-- compared through liveSlot?-≼; lexical variables use the indexed regular
-- injection.  The binder count keeps the `∀` case structural.
repoint?-≼ : ∀ {Θ Θ′ Θ₀ Δ Δ′ Δ₀ σ σ′ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (n : TyCtx) (extension : Ψ ≼[ k , ρ ] Φ)
    (source-resolve : TyVar Θ → Maybe (Ty Δ))
    (target-resolve : TyVar Θ′ → Maybe (Ty Δ′))
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar (n + Δ))) (A : Ty Δ₀)
  → (∀ q → target-resolve (shiftAlong extension q)
      ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (source-resolve q))
  → repoint? target-resolve σ′ birth
      (λ q → shiftAlong extension (anchor-map q))
      (route-mapⁿ n ρ route) (raise n) A
    ≡ mapMaybe (renameᵗ (toRenameᵗ (lift↪ᵗ n ρ)))
        (repoint? source-resolve σ birth anchor-map route (raise n) A)
repoint?-≼ n extension source-resolve target-resolve birth anchor-map
    route (＇ X) resolve-eq with Vec.lookup birth X
repoint?-≼ n extension source-resolve target-resolve birth anchor-map
    route (＇ X) resolve-eq | nothing with route X
repoint?-≼ n extension source-resolve target-resolve birth anchor-map
    route (＇ X) resolve-eq | nothing | nothing = refl
repoint?-≼ n extension source-resolve target-resolve birth anchor-map
    route (＇ X) resolve-eq | nothing | just Y = refl
repoint?-≼ {σ = source} {σ′ = target} {ρ = ρ} n extension
    source-resolve target-resolve birth anchor-map route (＇ X)
    resolve-eq | just q
    rewrite liveSlot?-≼ extension (anchor-map (suc q))
    with liveSlot? source (anchor-map (suc q))
repoint?-≼ {ρ = ρ} n extension source-resolve target-resolve birth
    anchor-map route (＇ X) resolve-eq | just q | just Y =
  cong (λ z → just (＇ z)) (sym (raise-rename n ρ Y))
repoint?-≼ {ρ = ρ} n extension source-resolve target-resolve birth
    anchor-map route (＇ X) resolve-eq | just q | nothing
    with source-resolve (anchor-map (suc q))
       | target-resolve (shiftAlong extension (anchor-map (suc q)))
       | resolve-eq (anchor-map (suc q))
repoint?-≼ n extension source-resolve target-resolve birth anchor-map
    route (＇ X) resolve-eq | just q | nothing
    | nothing | .nothing | refl = refl
repoint?-≼ {ρ = ρ} n extension source-resolve target-resolve birth
    anchor-map route (＇ X) resolve-eq | just q | nothing
    | just B | .(just (renameᵗ (toRenameᵗ ρ) B)) | refl =
  cong just (sym (rename-raise n ρ B))
repoint?-≼ n extension source-resolve target-resolve birth anchor-map
    route (‵ ι) resolve-eq = refl
repoint?-≼ n extension source-resolve target-resolve birth anchor-map
    route ★ resolve-eq = refl
repoint?-≼ n extension source-resolve target-resolve birth anchor-map
    route (A ⇒ B) resolve-eq =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-≼ n extension source-resolve target-resolve birth
          anchor-map route A resolve-eq)
        (repoint?-≼ n extension source-resolve target-resolve birth
          anchor-map route B resolve-eq))
      (trans (rename-⇒? _
          (repoint? source-resolve _ birth anchor-map route (raise n) A)
          (repoint? source-resolve _ birth anchor-map route (raise n) B))
        (cong (mapMaybe (renameᵗ (toRenameᵗ (lift↪ᵗ n _))))
          (sym (repoint?-arrow _ _ _ _ _ _ A B)))))
repoint?-≼ {ρ = ρ} n extension source-resolve target-resolve birth
    anchor-map route (`∀ A) resolve-eq =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (trans (repoint?-route-cong _ _ _ _ _ _ _ A
            (route-map-ext n ρ route))
          (repoint?-≼ (suc n) extension source-resolve target-resolve
            (nothing Vec.∷ birth) anchor-map (ext-route route) A
            resolve-eq)))
      (trans (rename-all?-keep (lift↪ᵗ n ρ)
          (repoint? source-resolve _ (nothing Vec.∷ birth) anchor-map
            (ext-route route) (raise (suc n)) A))
        (cong (mapMaybe (renameᵗ (toRenameᵗ (lift↪ᵗ n ρ))))
          (sym (repoint?-all _ _ _ _ _ _ A)))))

repoint?-route-lex : ∀ {Θ₀ Θ Δ₀ Δ Δout}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (left right : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A : Ty Δ₀)
  → (∀ X → Vec.lookup birth X ≡ nothing → left X ≡ right X)
  → repoint? resolve target birth anchor-map left live-ren A
    ≡ repoint? resolve target birth anchor-map right live-ren A
repoint?-route-lex resolve target birth anchor-map left right live-ren (＇ X)
    rel with Vec.lookup birth X in lookup-eq
repoint?-route-lex resolve target birth anchor-map left right live-ren (＇ X)
    rel | nothing with left X | right X | rel X lookup-eq
repoint?-route-lex resolve target birth anchor-map left right live-ren (＇ X)
    rel | nothing | nothing | .nothing | refl = refl
repoint?-route-lex resolve target birth anchor-map left right live-ren (＇ X)
    rel | nothing | just Y | .(just Y) | refl = refl
repoint?-route-lex resolve target birth anchor-map left right live-ren (＇ X)
    rel | just q = refl
repoint?-route-lex resolve target birth anchor-map left right live-ren (‵ ι)
    rel = refl
repoint?-route-lex resolve target birth anchor-map left right live-ren ★ rel = refl
repoint?-route-lex resolve target birth anchor-map left right live-ren (A ⇒ B)
    rel =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-route-lex resolve target birth anchor-map left right
          live-ren A rel)
        (repoint?-route-lex resolve target birth anchor-map left right
          live-ren B rel))
      (sym (repoint?-arrow _ _ _ _ _ _ A B)))
repoint?-route-lex resolve target birth anchor-map left right live-ren (`∀ A)
    rel =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (repoint?-route-lex resolve target (nothing Vec.∷ birth) anchor-map
          (ext-route left) (ext-route right) (λ X → suc (live-ren X)) A
          ext-rel))
      (sym (repoint?-all _ _ _ _ _ _ A)))
  where
  ext-rel : ∀ X → Vec.lookup (nothing Vec.∷ birth) X ≡ nothing
    → ext-route left X ≡ ext-route right X
  ext-rel zero eq = refl
  ext-rel (suc X) eq = cong (mapMaybe suc) (rel X eq)

scanRep?-route-lex : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : TyEnv Θ Δ σ) (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (left right : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → (∀ X → Vec.lookup σ₀ X ≡ nothing → left X ≡ right X)
  → scanRep? resolve target current anchor-map left a
    ≡ scanRep? resolve target current anchor-map right a
scanRep?-route-lex resolve target ∅ anchor-map left right () rel
scanRep?-route-lex resolve target
    (Ψ ,begin[ Y ≔ q ]⟨ fresh ⟩) anchor-map left right a rel =
  scanRep?-route-lex resolve target Ψ anchor-map
    (λ X → left (punchIn Y X)) (λ X → right (punchIn Y X)) a
    (λ X lex → rel (punchIn Y X)
      (trans (lookup-insert-punch Y (just q) (slotsOf Ψ) X) lex))
scanRep?-route-lex resolve target (Ψ ,typ) anchor-map left right a rel =
  scanRep?-route-lex resolve target Ψ anchor-map
    (λ X → left (suc X)) (λ X → right (suc X)) a
    (λ X lex → rel (suc X) lex)
scanRep?-route-lex resolve target (Ψ ,:= A) anchor-map left right zero rel =
  repoint?-route-lex resolve (slotsOf target) (slotsOf Ψ) anchor-map
    left right (λ X → X) A
    (λ X lex → rel X
      (trans (lookup-mapᵛ (mapMaybe suc) (slotsOf Ψ) X)
        (cong (mapMaybe suc) lex)))
scanRep?-route-lex resolve target (Ψ ,:= A) anchor-map left right
    (suc a) rel =
  scanRep?-route-lex resolve target Ψ (λ q → anchor-map (suc q))
    left right a
    (λ X lex → rel X
      (trans (lookup-mapᵛ (mapMaybe suc) (slotsOf Ψ) X)
        (cong (mapMaybe suc) lex)))
scanRep?-route-lex resolve target (Ψ ,end[ Y ]) anchor-map left right a rel =
  scanRep?-route-lex resolve target Ψ anchor-map
    (route-end Y left) (route-end Y right) a end-rel
  where
  end-rel : ∀ X → Vec.lookup (slotsOf Ψ) X ≡ nothing
    → route-end Y left X ≡ route-end Y right X
  end-rel X lex with Y ≟ X
  end-rel .Y lex | yes refl = refl
  end-rel X lex | no neq = rel (punchOut Y X neq)
    (trans (lookup-remove-punchOut Y X (slotsOf Ψ) neq) lex)

route-reenter-lex : ∀ {Θ Δ}
    {slots : Vec.Vec (Maybe (TyVar Θ)) (suc Δ)}
    {bound : TyVar Θ} (Y X : TyVar (suc Δ))
  → Vec.lookup slots Y ≡ just bound
  → Vec.lookup slots X ≡ nothing
  → route-end Y (λ Z → just (punchIn Y Z)) X ≡ just X
route-reenter-lex {slots = slots} Y X slot-eq lex with Y ≟ X
route-reenter-lex Y .Y slot-eq lex | yes refl =
  ⊥-elim (just≢nothing (trans (sym slot-eq) lex))
  where
  just≢nothing : ∀ {X : Set} {x : X} → just x ≢ nothing
  just≢nothing ()
route-reenter-lex Y X slot-eq lex | no neq
    rewrite punchIn-punchOut Y X neq = refl

scanRep?-target-cong : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (left right : TyEnv Θ Δ σ)
    (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → scanRep? resolve left current anchor-map route a
    ≡ scanRep? resolve right current anchor-map route a
scanRep?-target-cong resolve left right ∅ anchor-map route ()
scanRep?-target-cong resolve left right
    (Ψ ,begin[ Y ≔ q ]⟨ fresh ⟩) anchor-map route a =
  scanRep?-target-cong resolve left right Ψ anchor-map
    (λ X → route (punchIn Y X)) a
scanRep?-target-cong resolve left right (Ψ ,typ) anchor-map route a =
  scanRep?-target-cong resolve left right Ψ anchor-map
    (λ X → route (suc X)) a
scanRep?-target-cong resolve left right (Ψ ,:= A) anchor-map route zero = refl
scanRep?-target-cong resolve left right (Ψ ,:= A) anchor-map route (suc a) =
  scanRep?-target-cong resolve left right Ψ
    (λ q → anchor-map (suc q)) route a
scanRep?-target-cong resolve left right (Ψ ,end[ Y ]) anchor-map route a =
  scanRep?-target-cong resolve left right Ψ anchor-map
    (route-end Y route) a

scanRep?-target-cong≡ : ∀ {Θ Δ σ τ Θ₀ Δ₀ σ₀}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (left : TyEnv Θ Δ σ) (right : TyEnv Θ Δ τ)
    (slots-eq : σ ≡ τ) (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → scanRep? resolve left current anchor-map route a
    ≡ scanRep? resolve right current anchor-map route a
scanRep?-target-cong≡ resolve left right refl current anchor-map route a =
  scanRep?-target-cong resolve left right current anchor-map route a

repFuel?-reenter : ∀ fuel {Θ Δ σ}
    (Ψ : TyEnv Θ (suc Δ) σ) (Y : TyVar (suc Δ))
    (a : TyVar Θ) {bound : TyVar Θ}
    (slot-eq : Vec.lookup σ Y ≡ just bound)
    (fresh : bound ∉ᵛ removeᵛ Y σ)
  → repFuel? fuel (Ψ ,end[ Y ] ,begin[ Y ≔ bound ]⟨ fresh ⟩) a
    ≡ repFuel? fuel Ψ a
repFuel?-reenter zero Ψ Y a slot-eq fresh = refl
repFuel?-reenter (suc fuel) {σ = σ} Ψ Y a
    {bound = bound} slot-eq fresh =
  trans (scanRep?-route-lex
      (repFuel? fuel (Ψ ,end[ Y ] ,begin[ Y ≔ bound ]⟨ fresh ⟩))
      (Ψ ,end[ Y ] ,begin[ Y ≔ bound ]⟨ fresh ⟩) Ψ (λ q → q)
      (route-end Y (λ Z → just (punchIn Y Z))) (λ Z → just Z) a
      (λ X lex → route-reenter-lex {slots = σ} Y X slot-eq lex))
    (trans (scanRep?-resolve-cong
        (Ψ ,end[ Y ] ,begin[ Y ≔ bound ]⟨ fresh ⟩)
        Ψ (λ q → q) (λ Z → just Z) a
        (λ q → repFuel?-reenter fuel Ψ Y q slot-eq fresh))
      (scanRep?-target-cong≡ (repFuel? fuel Ψ)
        (Ψ ,end[ Y ] ,begin[ Y ≔ bound ]⟨ fresh ⟩) Ψ
        (reinsert-alias slot-eq) Ψ (λ q → q) (λ Z → just Z) a))

rep?-reenter : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {Y : TyVar (suc Δ)} {a bound : TyVar Θ} {A : Ty (suc Δ)}
    {fresh : bound ∉ᵛ removeᵛ Y σ}
  → Vec.lookup σ Y ≡ just bound
  → rep? Ψ a ≡ just A
  → rep? (Ψ ,end[ Y ] ,begin[ Y ≔ bound ]⟨ fresh ⟩) a ≡ just A
rep?-reenter {Θ = Θ} {Ψ = Ψ} {Y = Y} {a = a}
    {fresh = fresh} slot-eq eq =
  trans (repFuel?-reenter (Θ ∸ toℕ a) Ψ Y a slot-eq fresh) eq

------------------------------------------------------------------------
-- Stable evaluator cases for balanced extension
------------------------------------------------------------------------

rename-id↪ᵗ : ∀ {Δ} (A : Ty Δ)
  → renameᵗ (toRenameᵗ id↪ᵗ) A ≡ A
rename-id↪ᵗ A =
  trans (renameᵗ-cong A toRename-id-eq) (renameᵗ-id A)

rename-skip : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (skip ρ)) A
    ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ρ) A)
rename-skip ρ A =
  trans (renameᵗ-cong A (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ ρ) suc A))

rep?-≼-refl : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {a : TyVar Θ} {A : Ty Δ}
  → rep? Ψ a ≡ just A
  → rep? Ψ a
    ≡ just (renameᵗ (toRenameᵗ id↪ᵗ) A)
rep?-≼-refl {A = A} eq = trans eq (cong just (sym (rename-id↪ᵗ A)))

rep?-ν-explicit : ∀ {Θ Δ σ} (Ψ : TyEnv Θ Δ σ)
    (B : Ty Δ) (a : TyVar Θ) (A : Ty Δ)
  → rep? Ψ a ≡ just A
  → rep? (Ψ ,:= B) (suc a) ≡ just A
rep?-ν-explicit {Θ = Θ} Ψ B a A eq =
  rep?-ν {Θ = Θ} {Ψ = Ψ} {B = B} {a = a} {A = A} eq

rep?-typ-explicit : ∀ {Θ Δ σ} (Ψ : TyEnv Θ Δ σ)
    (a : TyVar Θ) (A : Ty Δ)
  → rep? Ψ a ≡ just A
  → rep? (Ψ ,typ) a ≡ just (⇑ᵗ A)
rep?-typ-explicit {Θ = Θ} Ψ a A eq =
  rep?-typ {Θ = Θ} {Ψ = Ψ} {α = a} {A = A} eq

rep?-≼-ν : ∀ {Θ Θ′ Δ Δ′ σ σ′ k} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    {B : Ty Δ′} {a : TyVar Θ} {A : Ty Δ}
    (extension : Ψ ≼[ k , ρ ] Φ)
  → rep? Φ (shiftAlong extension a)
      ≡ just (renameᵗ (toRenameᵗ ρ) A)
  → rep? (Φ ,:= B) (suc (shiftAlong extension a))
      ≡ just (renameᵗ (toRenameᵗ ρ) A)
rep?-≼-ν {ρ = ρ} {Φ = Φ} {B = B} {a = a} {A = A}
    extension eq =
  rep?-ν-explicit Φ B (shiftAlong extension a)
    (renameᵗ (toRenameᵗ ρ) A) eq

rep?-≼-typ : ∀ {Θ Θ′ Δ Δ′ σ σ′ k} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    {a : TyVar Θ} {A : Ty Δ}
    (extension : Ψ ≼[ k , ρ ] Φ)
  → rep? Φ (shiftAlong extension a)
      ≡ just (renameᵗ (toRenameᵗ ρ) A)
  → rep? (Φ ,typ) (shiftAlong extension a)
      ≡ just (renameᵗ (toRenameᵗ (skip ρ)) A)
rep?-≼-typ {Θ′ = Θ′} {ρ = ρ} {Φ = Φ} {a = a} {A = A}
    extension eq =
  trans (rep?-typ-explicit {Θ = Θ′} Φ (shiftAlong extension a)
      (renameᵗ (toRenameᵗ ρ) A) eq)
    (cong just (sym (rename-skip ρ A)))

scanRep?-current-≼ : ∀ {Θ Θ′ Ω Δ Δ′ D σ σ′ τ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ}
    {Φ : TyEnv Θ′ Δ′ σ′} (extension : Ψ ≼[ k , ρ ] Φ)
    (resolve : TyVar Ω → Maybe (Ty D)) (target : TyEnv Ω D τ)
    (source-map : TyVar Θ → TyVar Ω)
    (target-map : TyVar Θ′ → TyVar Ω)
    (source-route : TyVar Δ → Maybe (TyVar D))
    (target-route : TyVar Δ′ → Maybe (TyVar D))
    (a : TyVar Θ)
  → (∀ q → target-map (shiftAlong extension q) ≡ source-map q)
  → (∀ X → Vec.lookup σ X ≡ nothing
      → target-route (toRenameᵗ ρ X) ≡ source-route X)
  → scanRep? resolve target Φ target-map target-route
      (shiftAlong extension a)
    ≡ scanRep? resolve target Ψ source-map source-route a
scanRep?-current-≼ {Ψ = Ψ} ≼-refl resolve target source-map target-map
    source-route target-route a anchor-eq route-eq =
  trans (scanRep?-anchor-cong resolve target Ψ target-map source-map
      target-route a anchor-eq)
    (scanRep?-route-lex resolve target Ψ source-map target-route
      source-route a (λ X lex → trans
        (cong target-route (sym (toRename-id-eq X)))
        (route-eq X lex)))
scanRep?-current-≼ (≼-ν extension) resolve target source-map
    target-map source-route target-route a anchor-eq route-eq =
  scanRep?-current-≼ extension resolve target source-map
    (λ q → target-map (suc q)) source-route target-route a
    anchor-eq route-eq
scanRep?-current-≼ (≼-typ extension) resolve target source-map
    target-map source-route target-route a anchor-eq route-eq =
  scanRep?-current-≼ extension resolve target source-map target-map
    source-route (λ X → target-route (suc X)) a anchor-eq route-eq
scanRep?-current-≼
    {σ = source-slots}
    (≼-begin-end {ρ = ρ} {η = η} {Ψ′ = Ψ′} {Z = pivot}
      extension region)
    resolve target
    source-map target-map source-route target-route a
    anchor-eq route-eq =
  trans
    (scanRep?-current-≼ region resolve target region-map target-map
      region-route (route-end target-slot target-route)
      (shiftAlong extension a) (λ q → refl) (λ X lex → refl))
    (scanRep?-current-≼ extension resolve target source-map region-map
      source-route after-begin-route a anchor-eq extension-route)
  where
  target-slot = toRenameᵗ η pivot

  region-map = λ q → target-map (shiftAlong region q)

  region-route = λ X →
    route-end target-slot target-route (toRenameᵗ η X)

  after-begin-route = λ X → region-route (punchIn pivot X)

  extension-route : ∀ X → Vec.lookup source-slots X ≡ nothing
    → after-begin-route (toRenameᵗ ρ X) ≡ source-route X
  extension-route X lex =
    trans (cong (route-end target-slot target-route)
        (delete-punchIn η pivot (toRenameᵗ ρ X)))
      (trans (route-end-punchIn target-slot target-route
          (toRenameᵗ (delete↪ᵗ η pivot) (toRenameᵗ ρ X)))
        (trans (cong target-route
            (sym (toRename-compose ρ (delete↪ᵗ η pivot) X)))
          (route-eq X lex)))
scanRep?-current-≼
    {σ = source-slots}
    (≼-end-begin {ρ = ρ} {η = η} {X = pivot}
      slot-eq extension region shifted)
    resolve target
    source-map target-map source-route target-route a
    anchor-eq route-eq =
  trans
    (scanRep?-current-≼ region resolve target region-map target-map
      region-route after-final-route (shiftAlong extension a)
      (λ q → refl) (λ X lex → refl))
    (scanRep?-current-≼ extension resolve target source-map region-map
      source-route after-end-route a anchor-eq extension-route)
  where
  old = toRenameᵗ ρ pivot
  combined = delete↪ᵗ ρ pivot ⨟↪ᵗ η
  inserted = insert↪ᵗ combined pivot
  new = toRenameᵗ inserted pivot

  region-map = λ q → target-map (shiftAlong region q)

  after-final-route = λ X → target-route (punchIn new X)

  region-route = λ X →
    target-route (punchIn new (toRenameᵗ η X))

  after-end-route = route-end old region-route

  just≢nothing : ∀ {n} {x : TyVar n} → just x ≢ nothing
  just≢nothing ()

  pivot≢lexical : ∀ X → Vec.lookup source-slots X ≡ nothing
    → pivot ≢ X
  pivot≢lexical X lex eq =
    just≢nothing
      (trans (sym slot-eq)
        (trans (cong (Vec.lookup source-slots) eq) lex))

  extension-route : ∀ X → Vec.lookup source-slots X ≡ nothing
    → after-end-route (toRenameᵗ ρ X) ≡ source-route X
  extension-route X lex =
    trans (reentry-route ρ η pivot X (pivot≢lexical X lex)
        target-route)
      (route-eq X lex)

renameCtx-wk-eq : ∀ {Δ} (Γ : TermCtx Δ)
  → renameCtx (toRenameᵗ wk↪ᵗ) Γ ≡ renameCtx suc Γ
renameCtx-wk-eq [] = refl
renameCtx-wk-eq (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-wk-eq A) (renameCtx-wk-eq Γ)

scanRep?-target-≼ : ∀ {Θ Θ′ Θ₀ Δ Δ′ Δ₀ σ σ′ σ₀ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (extension : Ψ ≼[ k , ρ ] Φ)
    (source-resolve : TyVar Θ → Maybe (Ty Δ))
    (target-resolve : TyVar Θ′ → Maybe (Ty Δ′))
    (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → (∀ q → target-resolve (shiftAlong extension q)
      ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (source-resolve q))
  → scanRep? target-resolve Φ current
      (λ q → shiftAlong extension (anchor-map q))
      (route-map ρ route) a
    ≡ mapMaybe (renameᵗ (toRenameᵗ ρ))
        (scanRep? source-resolve Ψ current anchor-map route a)
scanRep?-target-≼ extension source-resolve target-resolve ∅
    anchor-map route () resolve-eq
scanRep?-target-≼ extension source-resolve target-resolve
    (current ,begin[ Y ≔ q ]⟨ fresh ⟩) anchor-map route a resolve-eq =
  scanRep?-target-≼ extension source-resolve target-resolve current
    anchor-map (λ X → route (punchIn Y X)) a resolve-eq
scanRep?-target-≼ extension source-resolve target-resolve (current ,typ)
    anchor-map route a resolve-eq =
  scanRep?-target-≼ extension source-resolve target-resolve current
    anchor-map (λ X → route (suc X)) a resolve-eq
scanRep?-target-≼ extension source-resolve target-resolve
    (current ,:= A) anchor-map route zero resolve-eq =
  repoint?-≼ zero extension source-resolve target-resolve
    (slotsOf current) anchor-map route A resolve-eq
scanRep?-target-≼ extension source-resolve target-resolve
    (current ,:= A) anchor-map route (suc a) resolve-eq =
  scanRep?-target-≼ extension source-resolve target-resolve current
    (λ q → anchor-map (suc q)) route a resolve-eq
scanRep?-target-≼ {ρ = ρ} {Φ = Φ} extension source-resolve target-resolve
    (current ,end[ Y ]) anchor-map route a resolve-eq =
  trans (scanRep?-route-cong target-resolve Φ current
      (λ q → shiftAlong extension (anchor-map q))
      (route-end Y (route-map ρ route))
      (route-map ρ (route-end Y route)) a
      (route-end-map ρ Y route))
    (scanRep?-target-≼ extension source-resolve target-resolve current
      anchor-map (route-end Y route) a resolve-eq)

repFuel?-≼ : ∀ fuel {Θ Θ′ Δ Δ′ σ σ′ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (extension : Ψ ≼[ k , ρ ] Φ) a
  → repFuel? fuel Φ (shiftAlong extension a)
    ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (repFuel? fuel Ψ a)
repFuel?-≼ zero extension a = refl
repFuel?-≼ (suc fuel) {ρ = ρ} {Ψ = Ψ} {Φ = Φ} extension a =
  trans (scanRep?-current-≼ extension (repFuel? fuel Φ) Φ
      (shiftAlong extension) (λ q → q)
      (route-map ρ (λ X → just X)) (λ X → just X) a
      (λ q → refl) (λ X lex → refl))
    (scanRep?-target-≼ extension (repFuel? fuel Ψ) (repFuel? fuel Φ)
      Ψ (λ q → q) (λ X → just X) a
      (λ q → repFuel?-≼ fuel extension q))

shifted-fuel : ∀ {Θ Θ′ k} {a : TyVar Θ} {b : TyVar Θ′}
  → Shifted k a b
  → Θ′ ∸ toℕ b ≡ Θ ∸ toℕ a
shifted-fuel shifted-zero = refl
shifted-fuel (shifted-suc shifted) = shifted-fuel shifted

rep?-≼-equation : ∀ {Θ Θ′ Δ Δ′ σ σ′ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (extension : Ψ ≼[ k , ρ ] Φ) a
  → rep? Φ (shiftAlong extension a)
    ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (rep? Ψ a)
rep?-≼-equation {Θ = Θ} {Θ′ = Θ′} extension a
    rewrite shifted-fuel (shiftAlong-shifted extension a) =
  repFuel?-≼ (Θ ∸ toℕ a) extension a

rep?-≼ : ∀ {Θ Θ′ Δ Δ′ σ σ′ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (extension : Ψ ≼[ k , ρ ] Φ) {a A}
  → rep? Ψ a ≡ just A
  → rep? Φ (shiftAlong extension a)
    ≡ just (renameᵗ (toRenameᵗ ρ) A)
rep?-≼ extension eq =
  trans (rep?-≼-equation extension _)
    (cong (mapMaybe (renameᵗ _)) eq)
