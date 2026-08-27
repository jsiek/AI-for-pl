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
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; +-suc)
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

mapMaybe-suc-ext : ∀ {Θ Θ′} (φ : TyVar Θ → TyVar Θ′)
    (m : Maybe (TyVar Θ))
  → mapMaybe suc (mapMaybe φ m)
    ≡ mapMaybe (extᵗ φ) (mapMaybe suc m)
mapMaybe-suc-ext φ nothing = refl
mapMaybe-suc-ext φ (just a) = refl

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

slotsOf : ∀ {Θ Δ σ} → TyEnv Θ Δ σ
  → Vec.Vec (Maybe (TyVar Θ)) Δ
slotsOf {σ = σ} Ψ = σ

fresh-zero-map-suc : ∀ {Θ Δ}
    {slots : Vec.Vec (Maybe (TyVar Θ)) Δ}
  → zero ∉ᵛ mapᵛ (mapMaybe suc) slots
fresh-zero-map-suc {slots = Vec.[]} ()
fresh-zero-map-suc {slots = nothing Vec.∷ slots} zero ()
fresh-zero-map-suc {slots = just a Vec.∷ slots} zero ()
fresh-zero-map-suc {slots = head Vec.∷ slots} (suc Y) eq =
  fresh-zero-map-suc {slots = slots} Y eq

liveSlot?-allocate : ∀ {Θ Δ}
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ) (a : TyVar Θ)
  → liveSlot?
      (just zero Vec.∷ mapᵛ (mapMaybe suc) slots) (suc a)
    ≡ liveSlot? (nothing Vec.∷ slots) a
liveSlot?-allocate slots a with suc a ≟ zero
liveSlot?-allocate slots a | yes ()
liveSlot?-allocate slots a | no _ rewrite liveSlot?-shift slots a = refl

aliasResult?-allocate : ∀ {Θ Δ Δout}
    (old : TyVar Θ → Maybe (Ty (suc Δ)))
    (new : TyVar (suc Θ) → Maybe (Ty (suc Δ)))
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (live-ren : TyVar (suc Δ) → TyVar Δout) (a : TyVar Θ)
  → (∀ q → new (suc q) ≡ old q)
  → aliasResult? new
      (just zero Vec.∷ mapᵛ (mapMaybe suc) slots) live-ren (suc a)
    ≡ aliasResult? old (nothing Vec.∷ slots) live-ren a
aliasResult?-allocate old new slots live-ren a eq
    rewrite liveSlot?-allocate slots a
    with liveSlot? (nothing Vec.∷ slots) a
aliasResult?-allocate old new slots live-ren a eq | just Y = refl
aliasResult?-allocate old new slots live-ren a eq | nothing
    rewrite eq a = refl

repoint?-allocate : ∀ {Θ₀ Θ Δ₀ Δ Δout}
    (old : TyVar Θ → Maybe (Ty (suc Δ)))
    (new : TyVar (suc Θ) → Maybe (Ty (suc Δ)))
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar (suc Δ) → TyVar Δout) (A : Ty Δ₀)
  → (∀ q → new (suc q) ≡ old q)
  → repoint? new (just zero Vec.∷ mapᵛ (mapMaybe suc) slots) birth
      (λ q → suc (anchor-map q)) route live-ren A
    ≡ repoint? old (nothing Vec.∷ slots) birth anchor-map route live-ren A
repoint?-allocate old new slots birth anchor-map route live-ren (＇ X) eq
    with Vec.lookup birth X
repoint?-allocate old new slots birth anchor-map route live-ren (＇ X) eq
    | nothing = refl
repoint?-allocate old new slots birth anchor-map route live-ren (＇ X) eq
    | just q = aliasResult?-allocate old new slots live-ren
      (anchor-map (suc q)) eq
repoint?-allocate old new slots birth anchor-map route live-ren (‵ ι) eq = refl
repoint?-allocate old new slots birth anchor-map route live-ren ★ eq = refl
repoint?-allocate old new slots birth anchor-map route live-ren (A ⇒ B) eq =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-allocate old new slots birth anchor-map route live-ren A eq)
        (repoint?-allocate old new slots birth anchor-map route live-ren B eq))
      (sym (repoint?-arrow _ _ _ _ _ _ A B)))
repoint?-allocate old new slots birth anchor-map route live-ren (`∀ A) eq =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (repoint?-allocate old new slots (nothing Vec.∷ birth)
          anchor-map (ext-route route) (λ X → suc (live-ren X)) A eq))
      (sym (repoint?-all _ _ _ _ _ _ A)))

scanRep?-allocate : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
    (old : TyVar Θ → Maybe (Ty (suc Δ)))
    (new : TyVar (suc Θ) → Maybe (Ty (suc Δ)))
    (target : TyEnv Θ Δ σ) (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar (suc Δ))) (a : TyVar Θ₀)
  → (∀ q → new (suc q) ≡ old q)
  → scanRep? new
      ((target ,:= ‵ `ℕ)
        ,begin[ zero ≔ zero ]⟨ fresh-zero-map-suc {slots = σ} ⟩)
      current (λ q → suc (anchor-map q)) route a
    ≡ scanRep? old (target ,typ) current anchor-map route a
scanRep?-allocate old new target ∅ anchor-map route () eq
scanRep?-allocate old new target
    (Ψ ,begin[ Y ≔ q ]⟨ fresh ⟩) anchor-map route a eq =
  scanRep?-allocate old new target Ψ anchor-map
    (λ X → route (punchIn Y X)) a eq
scanRep?-allocate old new target (Ψ ,typ) anchor-map route a eq =
  scanRep?-allocate old new target Ψ anchor-map (λ X → route (suc X)) a eq
scanRep?-allocate old new target (Ψ ,:= A) anchor-map route zero eq =
  repoint?-allocate old new (slotsOf target) (slotsOf Ψ) anchor-map route
    (λ X → X) A eq
scanRep?-allocate old new target (Ψ ,:= A) anchor-map route (suc a) eq =
  scanRep?-allocate old new target Ψ (λ q → anchor-map (suc q)) route a eq
scanRep?-allocate old new target (Ψ ,end[ Y ]) anchor-map route a eq =
  scanRep?-allocate old new target Ψ anchor-map (route-end Y route) a eq

repFuel?-allocate : ∀ fuel {Θ Δ σ} (Ψ : TyEnv Θ Δ σ)
    (C : Ty Δ) (a : TyVar Θ)
  → repFuel? fuel
      ((Ψ ,:= C)
        ,begin[ zero ≔ zero ]⟨ fresh-zero-map-suc {slots = σ} ⟩) (suc a)
    ≡ repFuel? fuel (Ψ ,typ) a
repFuel?-allocate zero Ψ C a = refl
repFuel?-allocate (suc fuel) {σ = σ} Ψ C a =
  scanRep?-allocate (repFuel? fuel (Ψ ,typ))
    (repFuel? fuel
      ((Ψ ,:= C)
        ,begin[ zero ≔ zero ]⟨ fresh-zero-map-suc {slots = σ} ⟩))
    Ψ Ψ (λ q → q) (λ X → just (suc X)) a
    (repFuel?-allocate fuel Ψ C)

rep?-allocate : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {C : Ty Δ}
    (a : TyVar Θ)
  → rep? ((Ψ ,:= C)
      ,begin[ zero ≔ zero ]⟨ fresh-zero-map-suc {slots = σ} ⟩)
      (suc a)
    ≡ rep? (Ψ ,typ) a
rep?-allocate {Θ = Θ} {Ψ = Ψ} {C = C} a =
  repFuel?-allocate (Θ ∸ toℕ a) Ψ C a

rep?-allocate-lexical : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {a : TyVar Θ} {A C : Ty Δ}
  → rep? Ψ a ≡ just A
  → rep? ((Ψ ,:= C)
      ,begin[ zero ≔ zero ]⟨ fresh-zero-map-suc {slots = σ} ⟩)
      (suc a) ≡ just (⇑ᵗ A)
rep?-allocate-lexical {Θ = Θ} {Ψ = Ψ} {a = a} {A = A} {C = C} eq =
  trans (rep?-allocate {Θ = Θ} {Ψ = Ψ} {C = C} a)
    (rep?-typ {Θ = Θ} {Ψ = Ψ} {α = a} {A = A} eq)

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

lexSlots : ∀ {Θ Δ} (n : TyCtx)
  → Vec.Vec (Maybe (TyVar Θ)) Δ
  → Vec.Vec (Maybe (TyVar Θ)) (n + Δ)
lexSlots zero slots = slots
lexSlots (suc n) slots = nothing Vec.∷ lexSlots n slots

lexSlots-just : ∀ {Θ Δ} (n : TyCtx)
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ) {X q}
  → Vec.lookup (lexSlots n slots) X ≡ just q
  → ∃[ Y ] (X ≡ raise n Y × Vec.lookup slots Y ≡ just q)
lexSlots-just zero slots {X = X} eq = X , refl , eq
lexSlots-just (suc n) slots {X = zero} ()
lexSlots-just (suc n) slots {X = suc X} eq
    with lexSlots-just n slots eq
lexSlots-just (suc n) slots {X = suc .(raise n Y)} eq
    | Y , refl , lookup-eq = Y , refl , lookup-eq

ext-route-id : ∀ {Δ} (X : TyVar (suc Δ))
  → ext-route (λ Y → just Y) X ≡ just X
ext-route-id zero = refl
ext-route-id (suc X) = refl

-- Reading the freshly appended ν itself returns its birth payload.  Under a
-- type binder, `lexSlots` and `raise` keep the same statement structural.
repoint?-newest : ∀ {Θ Δ σ} (n : TyCtx) (Ψ : TyEnv Θ Δ σ)
    (resolve : TyVar (suc Θ) → Maybe (Ty Δ))
    (A : Ty (n + Δ))
  → repoint? resolve (mapᵛ (mapMaybe suc) σ) (lexSlots n σ)
      (λ q → q) (λ X → just X) (raise n) A
    ≡ just A
repoint?-newest {σ = σ} n Ψ resolve (＇ X)
    with Vec.lookup (lexSlots n σ) X in lookup-eq
repoint?-newest {σ = σ} n Ψ resolve (＇ X) | nothing = refl
repoint?-newest {σ = σ} n Ψ resolve (＇ X) | just q
    with lexSlots-just n σ lookup-eq
repoint?-newest {σ = σ} n Ψ resolve (＇ .(raise n Y)) | just q
    | Y , refl , source-eq
    rewrite liveSlot?-shift σ q
          | liveSlot?-complete σ (aliases-unique Ψ) source-eq = refl
repoint?-newest n Ψ resolve (‵ ι) = refl
repoint?-newest n Ψ resolve ★ = refl
repoint?-newest n Ψ resolve (A ⇒ B) =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-newest n Ψ resolve A)
        (repoint?-newest n Ψ resolve B)) refl)
repoint?-newest n Ψ resolve (`∀ A) =
  trans (repoint?-all _ _ _ _ _ _ A)
    (cong all?
      (trans (repoint?-route-cong resolve _ _ (λ q → q)
          (ext-route (λ X → just X)) (λ X → just X)
          (raise (suc n)) A ext-route-id)
        (repoint?-newest (suc n) Ψ resolve A)))

rep?-here : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {A : Ty Δ}
  → rep? (Ψ ,:= A) zero ≡ just A
rep?-here {Θ = Θ} {Ψ = Ψ} {A = A} =
  repoint?-newest zero Ψ (repFuel? Θ (Ψ ,:= A)) A

insertUnder : ∀ {Δ} (n : TyCtx) (X : TyVar (suc Δ))
  → TyVar (n + Δ) → TyVar (n + suc Δ)
insertUnder zero X Y = punchIn X Y
insertUnder (suc n) X zero = zero
insertUnder (suc n) X (suc Y) = suc (insertUnder n X Y)

raise-punch : ∀ {Δ} (n : TyCtx) (X : TyVar (suc Δ)) (Y : TyVar Δ)
  → raise n (punchIn X Y) ≡ insertUnder n X (raise n Y)
raise-punch zero X Y = refl
raise-punch (suc n) X Y = cong suc (raise-punch n X Y)

ext-route-insertUnder : ∀ {Δ} (n : TyCtx) (X : TyVar (suc Δ))
    (Y : TyVar (suc (n + Δ)))
  → ext-route (λ Z → just (insertUnder n X Z)) Y
    ≡ just (insertUnder (suc n) X Y)
ext-route-insertUnder n X zero = refl
ext-route-insertUnder n X (suc Y) = refl

ext-insertUnder : ∀ {Δ} (n : TyCtx) (X : TyVar (suc Δ))
    (Y : TyVar (suc (n + Δ)))
  → extᵗ (insertUnder n X) Y ≡ insertUnder (suc n) X Y
ext-insertUnder n X zero = refl
ext-insertUnder n X (suc Y) = refl

newest-begin-target-lookup : ∀ {Θ Δ}
    (σ : Vec.Vec (Maybe (TyVar Θ)) Δ) (X : TyVar (suc Δ))
    (b : TyVar (suc Θ)) {Y q}
  → Vec.lookup σ Y ≡ just q
  → Vec.lookup (insertᵛ X (just b) (mapᵛ (mapMaybe suc) σ))
      (punchIn X Y) ≡ just (suc q)
newest-begin-target-lookup σ X b {Y = Y} source-eq =
  trans (lookup-insert-punch X (just b) (mapᵛ (mapMaybe suc) σ) Y)
    (trans (lookup-mapᵛ (mapMaybe suc) σ Y)
      (cong (mapMaybe suc) source-eq))

-- A begin for an anchor fresh at the new ν's birth acts on that ν's payload
-- as the corresponding regular insertion.  This is the exact evaluator fact
-- used when a boundary rule crosses a freshly allocated representation.
repoint?-newest-begin : ∀ {Θ Δ σ} (n : TyCtx)
    (Ψ : TyEnv Θ Δ σ) (C : Ty Δ) (X : TyVar (suc Δ))
    (b : TyVar (suc Θ)) (fresh : b ∉ᵛ mapᵛ (mapMaybe suc) σ)
    (resolve : TyVar (suc Θ) → Maybe (Ty (suc Δ)))
    (A : Ty (n + Δ))
  → repoint? resolve
      (insertᵛ X (just b) (mapᵛ (mapMaybe suc) σ))
      (lexSlots n σ) (λ q → q)
      (λ Y → just (insertUnder n X Y)) (raise n) A
    ≡ just (renameᵗ (insertUnder n X) A)
repoint?-newest-begin {σ = σ} n Ψ C X b fresh resolve (＇ Y)
    with Vec.lookup (lexSlots n σ) Y in lookup-eq
repoint?-newest-begin n Ψ C X b fresh resolve (＇ Y) | nothing = refl
repoint?-newest-begin {σ = σ} n Ψ C X b fresh resolve (＇ Y)
    | just q with lexSlots-just n σ lookup-eq
repoint?-newest-begin {σ = σ} n Ψ C X b fresh resolve
    (＇ .(raise n z)) | just q | z , refl , source-eq
    rewrite liveSlot?-complete
      (insertᵛ X (just b) (mapᵛ (mapMaybe suc) σ))
      (aliases-unique ((Ψ ,:= C) ,begin[ X ≔ b ]⟨ fresh ⟩))
      (newest-begin-target-lookup σ X b source-eq)
    | raise-punch n X z = refl
repoint?-newest-begin n Ψ C X b fresh resolve (‵ ι) = refl
repoint?-newest-begin n Ψ C X b fresh resolve ★ = refl
repoint?-newest-begin n Ψ C X b fresh resolve (A ⇒ B) =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-newest-begin n Ψ C X b fresh resolve A)
        (repoint?-newest-begin n Ψ C X b fresh resolve B)) refl)
repoint?-newest-begin n Ψ C X b fresh resolve (`∀ A) =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (repoint?-route-cong resolve _ _ (λ q → q)
          (ext-route (λ Y → just (insertUnder n X Y)))
          (λ Y → just (insertUnder (suc n) X Y))
          (raise (suc n)) A (ext-route-insertUnder n X)))
      (trans (cong all?
          (repoint?-newest-begin (suc n) Ψ C X b fresh resolve A))
        (cong (λ D → just (`∀ D))
          (renameᵗ-cong A (λ Y → sym (ext-insertUnder n X Y))))))

rep?-here-begin : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {C : Ty Δ}
    {X : TyVar (suc Δ)} {b : TyVar (suc Θ)}
    {fresh : b ∉ᵛ mapᵛ (mapMaybe suc) σ}
  → rep? ((Ψ ,:= C) ,begin[ X ≔ b ]⟨ fresh ⟩) zero
    ≡ just (wkᵗ X C)
rep?-here-begin {Θ = Θ} {Ψ = Ψ} {C = C} {X = X}
    {b = b} {fresh = fresh} =
  repoint?-newest-begin zero Ψ C X b fresh
    (repFuel? Θ ((Ψ ,:= C) ,begin[ X ≔ b ]⟨ fresh ⟩)) C

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

------------------------------------------------------------------------
-- Regular-context insertion through a telescope
------------------------------------------------------------------------

-- A regular injection inserts only lexical slots.  These four equations
-- commute that insertion through each telescope constructor.  Keeping them
-- separate makes the begin/end cases of typing transport read directly as
-- the corresponding Vec computation.

renameSlots-wk : ∀ {Θ Δ}
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → renameSlots wk↪ᵗ slots ≡ insertᵛ zero nothing slots
renameSlots-wk slots = cong (nothing Vec.∷_) (renameSlots-id slots)

renameSlots-insert : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ)) (entry : Maybe (TyVar Θ))
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → renameSlots (insert↪ᵗ ρ Y) (insertᵛ Y entry slots)
    ≡ insertᵛ (toRenameᵗ (insert↪ᵗ ρ Y) Y) entry
        (renameSlots ρ slots)
renameSlots-insert ρ zero entry slots = refl
renameSlots-insert (keep ρ) (suc Y) entry (slot Vec.∷ slots) =
  cong (slot Vec.∷_) (renameSlots-insert ρ Y entry slots)
renameSlots-insert (skip ρ) (suc Y) entry slots =
  cong (nothing Vec.∷_) (renameSlots-insert ρ (suc Y) entry slots)

renameSlots-typ : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → renameSlots (keep ρ) (insertᵛ zero nothing slots)
    ≡ insertᵛ zero nothing (renameSlots ρ slots)
renameSlots-typ ρ slots = refl

renameSlots-anchor-shift : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → renameSlots ρ (mapᵛ (mapMaybe suc) slots)
    ≡ mapᵛ (mapMaybe suc) (renameSlots ρ slots)
renameSlots-anchor-shift {Δ′ = zero} empty Vec.[] = refl
renameSlots-anchor-shift {Δ′ = suc Δ′} empty Vec.[] =
  cong (nothing Vec.∷_)
    (renameSlots-anchor-shift {Δ′ = Δ′} empty Vec.[])
renameSlots-anchor-shift (skip ρ) slots =
  cong (nothing Vec.∷_) (renameSlots-anchor-shift ρ slots)
renameSlots-anchor-shift (keep ρ) (slot Vec.∷ slots) =
  cong (mapMaybe suc slot Vec.∷_)
    (renameSlots-anchor-shift ρ slots)

renameSlots-remove : ∀ {Θ Δ Δ′}
    (ρ : suc Δ ↪ᵗ suc Δ′) (Y : TyVar (suc Δ))
    (slots : Vec.Vec (Maybe (TyVar Θ)) (suc Δ))
  → renameSlots (delete↪ᵗ ρ Y) (removeᵛ Y slots)
    ≡ removeᵛ (toRenameᵗ ρ Y) (renameSlots ρ slots)
renameSlots-remove (keep ρ) zero (slot Vec.∷ slots) = refl
renameSlots-remove {Δ = suc Δ} (keep (keep ρ)) (suc Y)
    (slot Vec.∷ slots)
    rewrite renameSlots-remove (keep ρ) Y slots = refl
renameSlots-remove {Δ = suc Δ} (keep (skip ρ)) (suc Y)
    (slot Vec.∷ slots)
    rewrite renameSlots-remove (skip ρ) Y slots = refl
renameSlots-remove (skip (keep ρ)) Y slots =
  cong (nothing Vec.∷_) (renameSlots-remove (keep ρ) Y slots)
renameSlots-remove (skip (skip ρ)) Y slots =
  cong (nothing Vec.∷_) (renameSlots-remove (skip ρ) Y slots)

fresh-renameSlots : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {slots : Vec.Vec (Maybe (TyVar Θ)) Δ} {a : TyVar Θ}
  → a ∉ᵛ slots
  → a ∉ᵛ renameSlots ρ slots
fresh-renameSlots {Δ′ = zero} empty {slots = Vec.[]} fresh ()
fresh-renameSlots {Δ′ = suc Δ′} empty {slots = Vec.[]} fresh zero ()
fresh-renameSlots {Δ′ = suc Δ′} empty {slots = Vec.[]} fresh (suc Y) =
  fresh-renameSlots {Δ′ = Δ′} empty {slots = Vec.[]} fresh Y
fresh-renameSlots (skip ρ) fresh zero ()
fresh-renameSlots (skip ρ) fresh (suc Y) =
  fresh-renameSlots ρ fresh Y
fresh-renameSlots (keep ρ) {slots = slot Vec.∷ slots} fresh zero = fresh zero
fresh-renameSlots (keep ρ) {slots = slot Vec.∷ slots} fresh (suc Y) =
  fresh-renameSlots ρ (λ X → fresh (suc X)) Y

-- `RenameTarget` records the same lexical insertion as it moves through the
-- telescope exposed by a typing derivation.  Begins and ends are transported
-- at their indexed images; ν entries transport their payloads.  This is the
-- regular-context analogue of `_≼[_,_]_`, but it changes no anchors.

data RenameTarget : ∀ {Θ Δ Δ′ σ σ′}
    (ρ : Δ ↪ᵗ Δ′) → TyEnv Θ Δ σ → TyEnv Θ Δ′ σ′ → Set where
  literal-wk-target : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      ------------------------------------------------
    → RenameTarget wk↪ᵗ Ψ (Ψ ,typ)

  target-begin : ∀ {Θ Δ Δ′ σ σ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′}
      {Y : TyVar (suc Δ)} {a : TyVar Θ}
      {fresh : a ∉ᵛ σ} {fresh′ : a ∉ᵛ σ′}
    → RenameTarget ρ Ψ Φ
      ------------------------------------------------------------
    → RenameTarget (insert↪ᵗ ρ Y)
        (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩)
        (Φ ,begin[
          toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ a
        ]⟨ fresh′ ⟩)

  target-typ : ∀ {Θ Δ Δ′ σ σ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′}
    → RenameTarget ρ Ψ Φ
      -----------------------------------------------
    → RenameTarget (keep ρ) (Ψ ,typ) (Φ ,typ)

  target-ν : ∀ {Θ Δ Δ′ σ σ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′} {A : Ty Δ}
    → RenameTarget ρ Ψ Φ
      --------------------------------------------------
    → RenameTarget ρ (Ψ ,:= A)
        (Φ ,:= renameᵗ (toRenameᵗ ρ) A)

  target-end : ∀ {Θ Δ Δ′ σ σ′}
      {ρ : suc Δ ↪ᵗ suc Δ′}
      {Ψ : TyEnv Θ (suc Δ) σ} {Φ : TyEnv Θ (suc Δ′) σ′}
      {Y : TyVar (suc Δ)}
    → RenameTarget ρ Ψ Φ
      ------------------------------------------------------------
    → RenameTarget (delete↪ᵗ ρ Y) (Ψ ,end[ Y ])
        (Φ ,end[ toRenameᵗ ρ Y ])

renameTarget-slots : ∀ {Θ Δ Δ′ σ σ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′}
  → RenameTarget ρ Ψ Φ
  → σ′ ≡ renameSlots ρ σ
renameTarget-slots {σ = slots} literal-wk-target =
  sym (renameSlots-wk slots)
renameTarget-slots
    (target-begin {ρ = ρ} {Y = Y} {a = a} target)
    rewrite renameTarget-slots target =
  sym (renameSlots-insert ρ Y (just a) _)
renameTarget-slots (target-typ {ρ = ρ} {Ψ = source} target)
    rewrite renameTarget-slots target =
  sym (renameSlots-typ ρ (slotsOf source))
renameTarget-slots (target-ν {ρ = ρ} {Ψ = source} target)
    rewrite renameTarget-slots target =
  sym (renameSlots-anchor-shift ρ (slotsOf source))
renameTarget-slots
    (target-end {ρ = ρ} {Ψ = source} {Y = Y} target)
    rewrite renameTarget-slots target =
  sym (renameSlots-remove ρ Y (slotsOf source))

fresh-RenameTarget : ∀ {Θ Δ Δ′ σ σ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′} {a : TyVar Θ}
  → RenameTarget ρ Ψ Φ
  → a ∉ᵛ σ
  → a ∉ᵛ σ′
fresh-RenameTarget {ρ = ρ} target fresh =
  subst≡ (λ slots → _ ∉ᵛ slots) (sym (renameTarget-slots target))
    (fresh-renameSlots ρ fresh)

renameTarget-begin : ∀ {Θ Δ Δ′ σ σ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′}
    {Y : TyVar (suc Δ)} {a : TyVar Θ} {fresh : a ∉ᵛ σ}
  → (target : RenameTarget ρ Ψ Φ)
  → RenameTarget (insert↪ᵗ ρ Y)
      (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩)
      (Φ ,begin[ toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ a
        ]⟨ fresh-RenameTarget target fresh ⟩)
renameTarget-begin target = target-begin target

lookup-renameSlots-image : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ) X
  → Vec.lookup (renameSlots ρ slots) (toRenameᵗ ρ X)
    ≡ Vec.lookup slots X
lookup-renameSlots-image empty Vec.[] ()
lookup-renameSlots-image (skip ρ) slots X =
  lookup-renameSlots-image ρ slots X
lookup-renameSlots-image (keep ρ) (slot Vec.∷ slots) zero = refl
lookup-renameSlots-image (keep ρ) (slot Vec.∷ slots) (suc X) =
  lookup-renameSlots-image ρ slots X

-- Repointing a birth type is insensitive to lexical slots inserted in its
-- birth scope, provided the accumulated position route agrees on the old
-- variables.  Crossing variables are unaffected: their payload transport is
-- selected by anchor identity in the query telescope.
repoint?-birth-rename : ∀ {Θ₀ Θ Δ₀ Δ₀′ Δ Δout}
    (η : Δ₀ ↪ᵗ Δ₀′)
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δout))
    (route′ : TyVar Δ₀′ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A : Ty Δ₀)
  → (∀ X → route′ (toRenameᵗ η X) ≡ route X)
  → repoint? resolve target (renameSlots η birth) anchor-map route′
      live-ren (renameᵗ (toRenameᵗ η) A)
    ≡ repoint? resolve target birth anchor-map route live-ren A
repoint?-birth-rename η resolve target birth anchor-map route route′
    live-ren (＇ X) route-eq
    rewrite lookup-renameSlots-image η birth X
    with Vec.lookup birth X
repoint?-birth-rename η resolve target birth anchor-map route route′
    live-ren (＇ X) route-eq | nothing
    rewrite route-eq X = refl
repoint?-birth-rename η resolve target birth anchor-map route route′
    live-ren (＇ X) route-eq | just q = refl
repoint?-birth-rename η resolve target birth anchor-map route route′
    live-ren (‵ ι) route-eq = refl
repoint?-birth-rename η resolve target birth anchor-map route route′
    live-ren ★ route-eq = refl
repoint?-birth-rename η resolve target birth anchor-map route route′
    live-ren (A ⇒ B) route-eq =
  trans (repoint?-arrow resolve target (renameSlots η birth) anchor-map
      route′ live-ren (renameᵗ (toRenameᵗ η) A)
      (renameᵗ (toRenameᵗ η) B))
    (trans (cong₂ _⇒?_
        (repoint?-birth-rename η resolve target birth anchor-map
          route route′ live-ren A route-eq)
        (repoint?-birth-rename η resolve target birth anchor-map
          route route′ live-ren B route-eq))
      (sym (repoint?-arrow resolve target birth anchor-map route
        live-ren A B)))
repoint?-birth-rename η resolve target birth anchor-map route route′
    live-ren (`∀ A) route-eq =
  trans (repoint?-all resolve target (renameSlots η birth) anchor-map
      route′ live-ren (renameᵗ (extᵗ (toRenameᵗ η)) A))
    (trans (cong all? body-eq)
      (sym (repoint?-all resolve target birth anchor-map route live-ren A)))
  where
  ext-route-eq : ∀ X
    → ext-route route′ (toRenameᵗ (keep η) X) ≡ ext-route route X
  ext-route-eq zero = refl
  ext-route-eq (suc X) = cong (mapMaybe suc) (route-eq X)

  renamed-body-eq : renameᵗ (toRenameᵗ (keep η)) A
    ≡ renameᵗ (extᵗ (toRenameᵗ η)) A
  renamed-body-eq = renameᵗ-cong A (toRename-keep-eq η)

  canonical-body-eq = repoint?-birth-rename (keep η) resolve target
    (nothing Vec.∷ birth) anchor-map (ext-route route)
    (ext-route route′) (λ X → suc (live-ren X)) A ext-route-eq

  body-eq = subst≡
    (λ B → repoint? resolve target
        (nothing Vec.∷ renameSlots η birth) anchor-map
        (ext-route route′) (λ X → suc (live-ren X)) B
      ≡ repoint? resolve target (nothing Vec.∷ birth) anchor-map
          (ext-route route) (λ X → suc (live-ren X)) A)
    renamed-body-eq canonical-body-eq

repoint?-outer-RenameTarget : ∀ {Θ₀ Θ Δ₀ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′}
    (target-rel : RenameTarget ρ Ψ Φ)
    (source-resolve : TyVar Θ → Maybe (Ty Δ))
    (target-resolve : TyVar Θ → Maybe (Ty Δ′))
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (source-route : TyVar Δ₀ → Maybe (TyVar Δ))
    (target-route : TyVar Δ₀ → Maybe (TyVar Δ′)) (A : Ty Δ₀)
  → (∀ q → target-resolve q
      ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (source-resolve q))
  → (∀ X → target-route X
      ≡ mapMaybe (toRenameᵗ ρ) (source-route X))
  → repoint? target-resolve σ′ birth anchor-map target-route
      (λ X → X) A
    ≡ mapMaybe (renameᵗ (toRenameᵗ ρ))
        (repoint? source-resolve σ birth anchor-map source-route
          (λ X → X) A)
repoint?-outer-RenameTarget {ρ = ρ} {Ψ = source} {Φ = target}
    target-rel source-resolve target-resolve
    birth anchor-map source-route target-route A resolve-eq route-eq =
  subst≡
    (λ slots → repoint? target-resolve slots birth anchor-map
        target-route (λ X → X) A
      ≡ mapMaybe (renameᵗ (toRenameᵗ ρ))
          (repoint? source-resolve (slotsOf source) birth anchor-map
            source-route (λ X → X) A))
    (sym (renameTarget-slots target-rel)) canonical
  where
  mapped-resolve = λ q →
    mapMaybe (renameᵗ (toRenameᵗ ρ)) (source-resolve q)
  mapped-route = route-map ρ source-route

  canonical =
    trans (repoint?-resolve-cong (renameSlots ρ (slotsOf source)) birth
        anchor-map target-route (λ X → X) A resolve-eq)
      (trans (repoint?-route-cong mapped-resolve
          (renameSlots ρ (slotsOf source)) birth anchor-map target-route
          mapped-route (λ X → X) A route-eq)
        (repoint?-rename zero ρ source-resolve (slotsOf source) birth
          anchor-map source-route A))

scanRep?-outer-RenameTarget : ∀ {Θ Θ₀ Δ Δ′ Δ₀ σ σ′ σ₀}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′}
    (target-rel : RenameTarget ρ Ψ Φ)
    (source-resolve : TyVar Θ → Maybe (Ty Δ))
    (target-resolve : TyVar Θ → Maybe (Ty Δ′))
    (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (source-route : TyVar Δ₀ → Maybe (TyVar Δ))
    (target-route : TyVar Δ₀ → Maybe (TyVar Δ′))
    (a : TyVar Θ₀)
  → (∀ q → target-resolve q
      ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (source-resolve q))
  → (∀ X → target-route X
      ≡ mapMaybe (toRenameᵗ ρ) (source-route X))
  → scanRep? target-resolve Φ current anchor-map target-route a
    ≡ mapMaybe (renameᵗ (toRenameᵗ ρ))
        (scanRep? source-resolve Ψ current anchor-map source-route a)
scanRep?-outer-RenameTarget target-rel source-resolve target-resolve ∅
    anchor-map source-route target-route () resolve-eq route-eq
scanRep?-outer-RenameTarget target-rel source-resolve target-resolve
    (current ,begin[ Y ≔ q ]⟨ fresh ⟩) anchor-map source-route
    target-route a resolve-eq route-eq =
  scanRep?-outer-RenameTarget target-rel source-resolve target-resolve
    current anchor-map (λ X → source-route (punchIn Y X))
    (λ X → target-route (punchIn Y X)) a resolve-eq
    (λ X → route-eq (punchIn Y X))
scanRep?-outer-RenameTarget target-rel source-resolve target-resolve
    (current ,typ) anchor-map source-route target-route a
    resolve-eq route-eq =
  scanRep?-outer-RenameTarget target-rel source-resolve target-resolve
    current anchor-map (λ X → source-route (suc X))
    (λ X → target-route (suc X)) a resolve-eq
    (λ X → route-eq (suc X))
scanRep?-outer-RenameTarget target-rel source-resolve target-resolve
    (current ,:= A) anchor-map source-route target-route zero
    resolve-eq route-eq =
  repoint?-outer-RenameTarget target-rel source-resolve target-resolve
    (slotsOf current) anchor-map source-route target-route A
    resolve-eq route-eq
scanRep?-outer-RenameTarget target-rel source-resolve target-resolve
    (current ,:= A) anchor-map source-route target-route (suc a)
    resolve-eq route-eq =
  scanRep?-outer-RenameTarget target-rel source-resolve target-resolve
    current (λ q → anchor-map (suc q)) source-route target-route a
    resolve-eq route-eq
scanRep?-outer-RenameTarget {ρ = ρ} target-rel source-resolve target-resolve
    (current ,end[ Y ]) anchor-map source-route target-route a
    resolve-eq route-eq =
  scanRep?-outer-RenameTarget target-rel source-resolve target-resolve
    current anchor-map (route-end Y source-route)
    (route-end Y target-route) a resolve-eq end-route-eq
  where
  end-route-eq : ∀ X
    → route-end Y target-route X
      ≡ mapMaybe (toRenameᵗ ρ) (route-end Y source-route X)
  end-route-eq X with Y ≟ X
  end-route-eq .Y | yes refl = refl
  end-route-eq X | no Y≢X = route-eq (punchOut Y X Y≢X)

repoint?-current-RenameTarget : ∀ {Θ₀ Θ Δ₀ Δ₀′ Δ σ₀ σ₀′}
    {η : Δ₀ ↪ᵗ Δ₀′}
    {source : TyEnv Θ₀ Δ₀ σ₀} {current : TyEnv Θ₀ Δ₀′ σ₀′}
    (current-rel : RenameTarget η source current)
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (source-route : TyVar Δ₀ → Maybe (TyVar Δ))
    (target-route : TyVar Δ₀′ → Maybe (TyVar Δ))
    (A : Ty Δ₀)
  → (∀ X → target-route (toRenameᵗ η X) ≡ source-route X)
  → repoint? resolve target σ₀′ anchor-map target-route (λ X → X)
      (renameᵗ (toRenameᵗ η) A)
    ≡ repoint? resolve target σ₀ anchor-map source-route (λ X → X) A
repoint?-current-RenameTarget {η = η} {source = source}
    current-rel resolve target anchor-map source-route target-route
    A route-eq =
  subst≡
    (λ slots → repoint? resolve target slots anchor-map target-route
        (λ X → X) (renameᵗ (toRenameᵗ η) A)
      ≡ repoint? resolve target (slotsOf source) anchor-map source-route
          (λ X → X) A)
    (sym (renameTarget-slots current-rel))
    (repoint?-birth-rename η resolve target (slotsOf source)
      anchor-map source-route target-route (λ X → X) A route-eq)

route-end-image : ∀ {Δ Δ′ D} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ))
    (source-route : TyVar Δ → Maybe (TyVar D))
    (target-route : TyVar Δ′ → Maybe (TyVar D))
  → (∀ X → target-route (toRenameᵗ (delete↪ᵗ ρ Y) X)
      ≡ source-route X)
  → ∀ X
  → route-end (toRenameᵗ ρ Y) target-route (toRenameᵗ ρ X)
    ≡ route-end Y source-route X
route-end-image ρ Y source-route target-route route-eq X
    with Y ≟ X | toRenameᵗ ρ Y ≟ toRenameᵗ ρ X
route-end-image ρ Y source-route target-route route-eq .Y
    | yes refl | yes refl = refl
route-end-image ρ Y source-route target-route route-eq .Y
    | yes refl | no image≢image = ⊥-elim (image≢image refl)
route-end-image ρ Y source-route target-route route-eq X
    | no Y≢X | yes image-eq =
  ⊥-elim (Y≢X (toRename-injective ρ image-eq))
route-end-image ρ Y source-route target-route route-eq X
    | no Y≢X | no image-neq =
  trans (cong target-route deleted-eq)
    (route-eq (punchOut Y X Y≢X))
  where
  reduced = punchOut Y X Y≢X
  source-rebuild : punchIn Y reduced ≡ X
  source-rebuild = punchIn-punchOut Y X Y≢X

  deleted-eq : punchOut (toRenameᵗ ρ Y) (toRenameᵗ ρ X) image-neq
      ≡ toRenameᵗ (delete↪ᵗ ρ Y) reduced
  deleted-eq = punchIn-injectiveᵗ (toRenameᵗ ρ Y)
    (trans (punchIn-punchOut (toRenameᵗ ρ Y)
        (toRenameᵗ ρ X) image-neq)
      (trans (cong (toRenameᵗ ρ) (sym source-rebuild))
        (delete-punchIn ρ Y reduced)))

scanRep?-current-RenameTarget : ∀ {Θ Θ₀ Δ Δ₀ Δ₀′ σ σ₀ σ₀′}
    {η : Δ₀ ↪ᵗ Δ₀′}
    {source : TyEnv Θ₀ Δ₀ σ₀} {current : TyEnv Θ₀ Δ₀′ σ₀′}
    (current-rel : RenameTarget η source current)
    (resolve : TyVar Θ → Maybe (Ty Δ)) (target : TyEnv Θ Δ σ)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (source-route : TyVar Δ₀ → Maybe (TyVar Δ))
    (target-route : TyVar Δ₀′ → Maybe (TyVar Δ))
    (a : TyVar Θ₀)
  → (∀ X → target-route (toRenameᵗ η X) ≡ source-route X)
  → scanRep? resolve target current anchor-map target-route a
    ≡ scanRep? resolve target source anchor-map source-route a
scanRep?-current-RenameTarget {source = source} literal-wk-target
    resolve target anchor-map source-route target-route a route-eq =
  scanRep?-route-cong resolve target source anchor-map
    (λ X → target-route (suc X)) source-route a adjusted-route
  where
  adjusted-route : ∀ X → target-route (suc X) ≡ source-route X
  adjusted-route X =
    trans (cong target-route (sym (toRename-wk-eq X))) (route-eq X)
scanRep?-current-RenameTarget
    (target-begin {ρ = ρ} {Y = Y} current-rel)
    resolve target anchor-map source-route target-route a route-eq =
  scanRep?-current-RenameTarget current-rel resolve target anchor-map
    (λ X → source-route (punchIn Y X))
    (λ X → target-route (punchIn target-Y X)) a begin-route
  where
  target-Y = toRenameᵗ (insert↪ᵗ ρ Y) Y

  begin-route : ∀ X
    → target-route (punchIn target-Y (toRenameᵗ ρ X))
      ≡ source-route (punchIn Y X)
  begin-route X =
    trans (cong target-route (sym (insert-punchIn ρ Y X)))
      (route-eq (punchIn Y X))
scanRep?-current-RenameTarget (target-typ current-rel)
    resolve target anchor-map source-route target-route a route-eq =
  scanRep?-current-RenameTarget current-rel resolve target anchor-map
    (λ X → source-route (suc X)) (λ X → target-route (suc X))
    a (λ X → route-eq (suc X))
scanRep?-current-RenameTarget
    (target-ν {ρ = ρ} {Ψ = source} {Φ = current} {A = A} current-rel)
    resolve target anchor-map source-route target-route zero route-eq =
  repoint?-current-RenameTarget current-rel resolve (slotsOf target)
    anchor-map source-route target-route A route-eq
scanRep?-current-RenameTarget
    (target-ν current-rel) resolve target anchor-map source-route
    target-route (suc a) route-eq =
  scanRep?-current-RenameTarget current-rel resolve target
    (λ q → anchor-map (suc q)) source-route target-route a route-eq
scanRep?-current-RenameTarget
    (target-end {ρ = ρ} {Y = Y} current-rel)
    resolve target anchor-map source-route target-route a route-eq =
  scanRep?-current-RenameTarget current-rel resolve target anchor-map
    (route-end Y source-route)
    (route-end (toRenameᵗ ρ Y) target-route) a
    (route-end-image ρ Y source-route target-route route-eq)

repFuel?-RenameTarget : ∀ fuel {Θ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′}
    (target : RenameTarget ρ Ψ Φ) a
  → repFuel? fuel Φ a
    ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (repFuel? fuel Ψ a)
repFuel?-RenameTarget zero target a = refl
repFuel?-RenameTarget (suc fuel) {ρ = ρ} {Ψ = Ψ} {Φ = Φ}
    target a =
  trans (scanRep?-current-RenameTarget target (repFuel? fuel Φ) Φ
      (λ q → q) (route-map ρ (λ X → just X)) (λ X → just X)
      a (λ X → refl))
    (scanRep?-outer-RenameTarget target (repFuel? fuel Ψ)
      (repFuel? fuel Φ) Ψ (λ q → q) (λ X → just X)
      (route-map ρ (λ X → just X)) a
      (λ q → repFuel?-RenameTarget fuel target q) (λ X → refl))

rep?-RenameTarget-equation : ∀ {Θ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′}
    (target : RenameTarget ρ Ψ Φ) a
  → rep? Φ a
    ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (rep? Ψ a)
rep?-RenameTarget-equation {Θ = Θ} target a =
  repFuel?-RenameTarget (Θ ∸ toℕ a) target a

rep?-RenameTarget : ∀ {Θ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′}
    (target : RenameTarget ρ Ψ Φ) (a : TyVar Θ) {A}
  → rep? Ψ a ≡ just A
  → rep? Φ a ≡ just (renameᵗ (toRenameᵗ ρ) A)
rep?-RenameTarget target a eq =
  trans (rep?-RenameTarget-equation target a)
    (cong (mapMaybe (renameᵗ _)) eq)

slot-RenameTarget : ∀ {Θ Δ Δ′ σ σ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′} {a}
  → (target : RenameTarget ρ Ψ Φ) (X : TyVar Δ)
  → Vec.lookup σ X ≡ just a
  → Vec.lookup σ′ (toRenameᵗ ρ X) ≡ just a
slot-RenameTarget {ρ = ρ} {Ψ = source} target X lookup-eq =
  trans (cong (λ target-slots →
      Vec.lookup target-slots (toRenameᵗ ρ X))
      (renameTarget-slots target))
    (trans (lookup-renameSlots-image ρ (slotsOf source) X) lookup-eq)

renameCtx-keep-shift : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Γ : TermCtx Δ)
  → renameCtx (toRenameᵗ (keep ρ)) (renameCtx suc Γ)
    ≡ renameCtx suc (renameCtx (toRenameᵗ ρ) Γ)
renameCtx-keep-shift ρ [] = refl
renameCtx-keep-shift ρ (A ∷ Γ) =
  cong₂ _∷_
    (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
      (renameᵗ-shift (toRenameᵗ ρ) A))
    (renameCtx-keep-shift ρ Γ)

rename-open↪ᵗ : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (C : Ty (suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ ρ) (C [ A ]ᵗ)
    ≡ renameᵗ (toRenameᵗ (keep ρ)) C
        [ renameᵗ (toRenameᵗ ρ) A ]ᵗ
rename-open↪ᵗ ρ C A =
  trans (renameᵗ-subst (toRenameᵗ ρ) (singleSubᵗ A) C)
    (trans (substᵗ-cong C env-eq)
      (sym (substᵗ-rename
        (singleSubᵗ (renameᵗ (toRenameᵗ ρ) A))
        (toRenameᵗ (keep ρ)) C)))
  where
  env-eq : ∀ X
    → renameᵗ (toRenameᵗ ρ) (singleSubᵗ A X)
      ≡ singleSubᵗ (renameᵗ (toRenameᵗ ρ) A)
          (toRenameᵗ (keep ρ) X)
  env-eq zero = refl
  env-eq (suc X) = refl

------------------------------------------------------------------------
-- Type-variable renaming preserves typing
------------------------------------------------------------------------

⊢renameᵗᵐ-target : ∀ {Θ Δ Δ′ σ σ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ′ σ′} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → RenameTarget ρ Ψ Φ
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ M ⦂ renameᵗ (toRenameᵗ ρ) A
⊢renameᵗᵐ-target target (⊢` x∈) = ⊢` (renameᵗ-∋ _ x∈)
⊢renameᵗᵐ-target target (⊢ƛ M⊢) =
  ⊢ƛ (⊢renameᵗᵐ-target target M⊢)
⊢renameᵗᵐ-target target (⊢· L⊢ M⊢) =
  ⊢· (⊢renameᵗᵐ-target target L⊢)
    (⊢renameᵗᵐ-target target M⊢)
⊢renameᵗᵐ-target {ρ = ρ} {Φ = Φ} {Γ = Γ}
    target (⊢Λ {A = A} M⊢) =
  ⊢Λ body⊢
  where
  renamed-body⊢ = ⊢renameᵗᵐ-target (target-typ target) M⊢

  body-context⊢ = subst≡
    (λ Γ′ → Φ ,typ ∣ Γ′ ⊢ renameᵗᵐ (keep ρ) _ ⦂ _)
    (renameCtx-keep-shift ρ Γ) renamed-body⊢

  body⊢ = subst≡
    (λ B → Φ ,typ ∣ renameCtx suc (renameCtx (toRenameᵗ ρ) Γ)
      ⊢ renameᵗᵐ (keep ρ) _ ⦂ B)
    (renameᵗ-cong A (toRename-keep-eq ρ)) body-context⊢
⊢renameᵗᵐ-target {ρ = ρ} {Φ = Φ} {Γ = Γ}
    {M = L ⦂∀ C [ A ]} target (⊢⦂∀ L⊢) =
  subst≡
    (λ B → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ L ⦂∀ renameᵗ (toRenameᵗ (keep ρ)) C
        [ renameᵗ (toRenameᵗ ρ) A ] ⦂ B)
    (sym (rename-open↪ᵗ ρ C A)) (⊢⦂∀ body⊢)
  where
  body-eq = renameᵗ-cong C (toRename-keep-eq ρ)
  body⊢ = subst≡
    (λ B → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ L ⦂ `∀ B)
    (sym body-eq) (⊢renameᵗᵐ-target target L⊢)
⊢renameᵗᵐ-target {ρ = ρ} target (⊢$ κ) =
  subst≡ (λ A → _ ∣ _ ⊢ $ κ ⦂ A)
    (constTy-renameᵗ (toRenameᵗ ρ) κ) (⊢$ κ)
⊢renameᵗᵐ-target target (⊢⊕ addℕ L⊢ M⊢) =
  ⊢⊕ addℕ (⊢renameᵗᵐ-target target L⊢)
    (⊢renameᵗᵐ-target target M⊢)
⊢renameᵗᵐ-target target (⊢⊕ and𝔹 L⊢ M⊢) =
  ⊢⊕ and𝔹 (⊢renameᵗᵐ-target target L⊢)
    (⊢renameᵗᵐ-target target M⊢)
⊢renameᵗᵐ-target {ρ = ρ} target (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢renameᵗᵐ-target target M⊢) (renameᵐᶜ ρ c)
⊢renameᵗᵐ-target target (⊢ν M⊢) =
  ⊢ν (⊢renameᵗᵐ-target (target-ν target) M⊢)
⊢renameᵗᵐ-target {ρ = ρ} {Φ = Φ} target
    (⊢reveal {A = A} {B = B} {C = C} {Y = Y} {α = α}
      {fresh = fresh} α-eq c⊢ M⊢) =
  ⊢reveal (rep?-RenameTarget target α α-eq) conversion⊢ body⊢
  where
  ρ⁺ = insert↪ᵗ ρ Y
  Y′ = toRenameᵗ ρ⁺ Y

  body⊢ = ⊢renameᵗᵐ-target (renameTarget-begin target) M⊢

  conversion-representation⊢ = subst≡
    (λ R → ⊢↑[ Y′ ⦂ R ] _
      ⦂ renameᵗ (toRenameᵗ ρ⁺) A
      ↝ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y B))
    (rename-insert-wk ρ Y C)
    (rename-⊢↑ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ = subst≡
    (λ B′ → ⊢↑[ Y′
        ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ ρ) C) ] _
      ⦂ renameᵗ (toRenameᵗ ρ⁺) A ↝ B′)
    (rename-insert-wk ρ Y B) conversion-representation⊢
⊢renameᵗᵐ-target {ρ = ρ⁺@(keep ρ)} target
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} {α = α}
      slot-eq α-eq c⊢ M⊢) =
  ⊢conceal target-slot target-rep conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  ended-target = target-end target

  target-slot = slot-RenameTarget target Y slot-eq
  target-rep = rep?-RenameTarget ended-target α α-eq
  body⊢ = ⊢renameᵗᵐ-target ended-target M⊢

  conversion-representation⊢ = subst≡
    (λ R → ⊢↓[ Y′ ⦂ R ] _
      ⦂ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y A)
      ↝ renameᵗ (toRenameᵗ ρ⁺) B)
    (rename-delete-wk ρ⁺ Y C)
    (rename-⊢↓ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ = subst≡
    (λ A′ → ⊢↓[ Y′
        ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ deleted) C) ] _
      ⦂ A′ ↝ renameᵗ (toRenameᵗ ρ⁺) B)
    (rename-delete-wk ρ⁺ Y A) conversion-representation⊢
⊢renameᵗᵐ-target {ρ = ρ⁺@(skip ρ)} target
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} {α = α}
      slot-eq α-eq c⊢ M⊢) =
  ⊢conceal target-slot target-rep conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  ended-target = target-end target

  target-slot = slot-RenameTarget target Y slot-eq
  target-rep = rep?-RenameTarget ended-target α α-eq
  body⊢ = ⊢renameᵗᵐ-target ended-target M⊢

  conversion-representation⊢ = subst≡
    (λ R → ⊢↓[ Y′ ⦂ R ] _
      ⦂ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y A)
      ↝ renameᵗ (toRenameᵗ ρ⁺) B)
    (rename-delete-wk ρ⁺ Y C)
    (rename-⊢↓ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ = subst≡
    (λ A′ → ⊢↓[ Y′
        ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ deleted) C) ] _
      ⦂ A′ ↝ renameᵗ (toRenameᵗ ρ⁺) B)
    (rename-delete-wk ρ⁺ Y A) conversion-representation⊢
⊢renameᵗᵐ-target target ⊢blame = ⊢blame

------------------------------------------------------------------------
-- Literal regular-context weakening at zero
------------------------------------------------------------------------

⊢weakenᵗᵐ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Ψ ,typ ∣ renameCtx suc Γ
      ⊢ weakenᵗᵐ zero M ⦂ ⇑ᵗ A
⊢weakenᵗᵐ {Ψ = Ψ} {Γ = Γ} {M = M} {A = A} M⊢ =
  subst≡
    (λ B → Ψ ,typ ∣ renameCtx suc Γ
      ⊢ weakenᵗᵐ zero M ⦂ B)
    (renameᵗ-wk-eq A)
    (subst≡
      (λ Γ′ → Ψ ,typ ∣ Γ′
        ⊢ weakenᵗᵐ zero M ⦂ renameᵗ (toRenameᵗ wk↪ᵗ) A)
      (renameCtx-wk-eq Γ)
      (⊢renameᵗᵐ-target literal-wk-target M⊢))

------------------------------------------------------------------------
-- Parallel and single term substitution
------------------------------------------------------------------------

exts-∋ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {Γ Γ′ : TermCtx Δ}
    {environment : Subst Θ Δ} {A : Ty Δ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Ψ ∣ Γ′ ⊢ environment x ⦂ B)
  → ∀ {x B}
  → A ∷ Γ ∋ x ⦂ B
  → Ψ ∣ A ∷ Γ′ ⊢ exts environment x ⦂ B
exts-∋ environment⊢ Z = ⊢` Z
exts-∋ environment⊢ (S x∈) = ⊢rename-suc (environment⊢ x∈)

liftˢ-∋ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {Γ Γ′ : TermCtx Δ}
    {environment : Subst Θ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Ψ ∣ Γ′ ⊢ environment x ⦂ A)
  → ∀ {x A}
  → renameCtx suc Γ ∋ x ⦂ A
  → Ψ ,typ ∣ renameCtx suc Γ′ ⊢ liftˢ environment x ⦂ A
liftˢ-∋ environment⊢ x∈ with lookup-renameCtx-inv x∈
liftˢ-∋ environment⊢ x∈ | B , B∈ , refl =
  ⊢weakenᵗᵐ (environment⊢ B∈)

⊢subst : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {Γ Γ′ : TermCtx Δ}
    {environment : Subst Θ Δ} {M : Term Θ Δ} {A : Ty Δ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Ψ ∣ Γ′ ⊢ environment x ⦂ B)
  → Ψ ∣ Γ ⊢ M ⦂ A
    --------------------------
  → Ψ ∣ Γ′ ⊢ subst environment M ⦂ A
⊢subst environment⊢ (⊢` x∈) = environment⊢ x∈
⊢subst environment⊢ (⊢ƛ M⊢) =
  ⊢ƛ (⊢subst (exts-∋ environment⊢) M⊢)
⊢subst environment⊢ (⊢· L⊢ M⊢) =
  ⊢· (⊢subst environment⊢ L⊢) (⊢subst environment⊢ M⊢)
⊢subst environment⊢ (⊢Λ M⊢) =
  ⊢Λ (⊢subst (liftˢ-∋ environment⊢) M⊢)
⊢subst environment⊢ (⊢⦂∀ L⊢) = ⊢⦂∀ (⊢subst environment⊢ L⊢)
⊢subst environment⊢ (⊢$ κ) = ⊢$ κ
⊢subst environment⊢ (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢subst environment⊢ L⊢) (⊢subst environment⊢ M⊢)
⊢subst environment⊢ (⊢⟨⟩ M⊢ c) = ⊢⟨⟩ (⊢subst environment⊢ M⊢) c
⊢subst environment⊢ (⊢ν M⊢) = ⊢ν M⊢
⊢subst environment⊢ (⊢reveal α-eq c⊢ M⊢) =
  ⊢reveal α-eq c⊢ M⊢
⊢subst environment⊢ (⊢conceal slot-eq α-eq c⊢ M⊢) =
  ⊢conceal slot-eq α-eq c⊢ M⊢
⊢subst environment⊢ ⊢blame = ⊢blame

⊢[] : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {Γ : TermCtx Δ}
    {M N : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ A ∷ Γ ⊢ M ⦂ B
  → Ψ ∣ Γ ⊢ N ⦂ A
    ---------------------
  → Ψ ∣ Γ ⊢ M [ N ] ⦂ B
⊢[] {Ψ = Ψ} {Γ = Γ} {N = N} {A = A} M⊢ N⊢ =
  ⊢subst single⊢ M⊢
  where
  single⊢ : ∀ {x C}
    → A ∷ Γ ∋ x ⦂ C
    → Ψ ∣ Γ ⊢ singleSub N x ⦂ C
  single⊢ Z = N⊢
  single⊢ (S x∈) = ⊢` x∈

------------------------------------------------------------------------
-- Typing transport along balanced extension
------------------------------------------------------------------------

-- A typing derivation descends below syntax already present on both sides of
-- a balanced extension.  `TypingTarget` closes a `_≼[_,_]_` witness under
-- those matching telescope constructors.  Its two maps are exactly the maps
-- applied to terms: a regular injection on type slots and an anchor map.

data TypingTarget : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    (ρ : Δ ↪ᵗ Δ′) (φ : TyVar Θ → TyVar Θ′)
    → TyEnv Θ Δ σ → TyEnv Θ′ Δ′ σ′ → Set where
  balanced-target : ∀ {Θ Θ′ Δ Δ′ σ σ′ k} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
      (extension : Ψ ≼[ k , ρ ] Φ)
      -----------------------------------------------------
    → TypingTarget ρ (shiftAlong extension) Ψ Φ

  typing-target-begin : ∀ {Θ Θ′ Δ Δ′ σ σ′}
      {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
      {Y : TyVar (suc Δ)} {a : TyVar Θ}
      {fresh : a ∉ᵛ σ} {fresh′ : φ a ∉ᵛ σ′}
    → TypingTarget ρ φ Ψ Φ
      ------------------------------------------------------------
    → TypingTarget (insert↪ᵗ ρ Y) φ
        (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩)
        (Φ ,begin[
          toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ φ a
        ]⟨ fresh′ ⟩)

  typing-target-typ : ∀ {Θ Θ′ Δ Δ′ σ σ′}
      {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    → TypingTarget ρ φ Ψ Φ
      ---------------------------------------------------
    → TypingTarget (keep ρ) φ (Ψ ,typ) (Φ ,typ)

  typing-target-ν : ∀ {Θ Θ′ Δ Δ′ σ σ′}
      {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′} {A : Ty Δ}
    → TypingTarget ρ φ Ψ Φ
      --------------------------------------------------
    → TypingTarget ρ (extᵗ φ) (Ψ ,:= A)
        (Φ ,:= renameᵗ (toRenameᵗ ρ) A)

  typing-target-end : ∀ {Θ Θ′ Δ Δ′ σ σ′}
      {ρ : suc Δ ↪ᵗ suc Δ′} {φ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ (suc Δ) σ} {Φ : TyEnv Θ′ (suc Δ′) σ′}
      {Y : TyVar (suc Δ)}
    → TypingTarget ρ φ Ψ Φ
      ------------------------------------------------------------
    → TypingTarget (delete↪ᵗ ρ Y) φ (Ψ ,end[ Y ])
        (Φ ,end[ toRenameᵗ ρ Y ])

extᵗ-injective′ : ∀ {Θ Θ′} {φ : TyVar Θ → TyVar Θ′}
  → (∀ {a b} → φ a ≡ φ b → a ≡ b)
  → ∀ {a b} → extᵗ φ a ≡ extᵗ φ b → a ≡ b
extᵗ-injective′ injective {zero} {zero} eq = refl
extᵗ-injective′ injective {zero} {suc b} ()
extᵗ-injective′ injective {suc a} {zero} ()
extᵗ-injective′ injective {suc a} {suc b} eq =
  cong suc (injective (suc-injective eq))

TypingTarget-anchor-injective : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
  → TypingTarget ρ φ Ψ Φ
  → ∀ {a b} → φ a ≡ φ b → a ≡ b
TypingTarget-anchor-injective (balanced-target extension) =
  shiftAlong-injective extension
TypingTarget-anchor-injective (typing-target-begin target) =
  TypingTarget-anchor-injective target
TypingTarget-anchor-injective (typing-target-typ target) =
  TypingTarget-anchor-injective target
TypingTarget-anchor-injective (typing-target-ν target) =
  extᵗ-injective′ (TypingTarget-anchor-injective target)
TypingTarget-anchor-injective (typing-target-end target) =
  TypingTarget-anchor-injective target

mutual
  slot-forward-TypingTarget : ∀ {Θ Θ′ Δ Δ′ σ σ′}
      {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
      (target : TypingTarget ρ φ Ψ Φ) {X a}
    → Vec.lookup σ X ≡ just a
    → Vec.lookup σ′ (toRenameᵗ ρ X) ≡ just (φ a)
  slot-forward-TypingTarget (balanced-target extension) lookup-eq =
    slot-forward-≼ extension lookup-eq
  slot-forward-TypingTarget
      (typing-target-begin {ρ = ρ} {Y = pivot} target)
      {X = X} lookup-eq with pivot ≟ X
  slot-forward-TypingTarget
      (typing-target-begin {ρ = ρ} {Y = pivot} target)
      {X = .pivot} lookup-eq | yes refl =
    trans (lookup-insert-here target-pivot _ _)
      (cong just (cong _ (sym anchor-eq)))
    where
    target-pivot = toRenameᵗ (insert↪ᵗ ρ pivot) pivot
    anchor-eq = just-injective
      (trans (sym lookup-eq) (lookup-insert-here pivot _ _))
  slot-forward-TypingTarget
      {φ = φ}
      (typing-target-begin {ρ = ρ} {Φ = result} {Y = pivot}
        {a = bound} target)
      {X = X} lookup-eq | no pivot≢X =
    trans (cong (Vec.lookup
        (insertᵛ target-pivot (just (φ bound)) (slotsOf result)))
        (sym position-eq))
      (trans (lookup-insert-punch target-pivot (just (φ bound))
          (slotsOf result) source-image)
        (slot-forward-TypingTarget target source-lookup))
    where
    reduced = punchOut pivot X pivot≢X
    source-image = toRenameᵗ ρ reduced
    target-pivot = toRenameᵗ (insert↪ᵗ ρ pivot) pivot
    source-rebuild = punchIn-punchOut pivot X pivot≢X
    position-eq : punchIn target-pivot source-image
      ≡ toRenameᵗ (insert↪ᵗ ρ pivot) X
    position-eq = trans (sym (insert-punchIn ρ pivot reduced))
      (cong (toRenameᵗ (insert↪ᵗ ρ pivot)) source-rebuild)
    source-lookup = trans
      (sym (lookup-insert-other pivot X _ _ pivot≢X)) lookup-eq
  slot-forward-TypingTarget (typing-target-typ target)
      {X = zero} ()
  slot-forward-TypingTarget (typing-target-typ target)
      {X = suc X} lookup-eq =
    slot-forward-TypingTarget target lookup-eq
  slot-forward-TypingTarget
      (typing-target-ν {Ψ = source} {Φ = result} target)
      {X = X} {a = zero} lookup-eq =
    ⊥-elim (mapMaybe-suc≢zero (Vec.lookup (slotsOf source) X)
      (trans (sym (lookup-mapᵛ (mapMaybe suc) (slotsOf source) X))
        lookup-eq))
  slot-forward-TypingTarget
      (typing-target-ν {Ψ = source} {Φ = result} target)
      {X = X} {a = suc a} lookup-eq =
    trans (lookup-mapᵛ (mapMaybe suc) (slotsOf result) _)
      (cong (mapMaybe suc)
        (slot-forward-TypingTarget target source-lookup))
    where
    source-lookup = mapMaybe-suc-just-injective
      (trans (sym (lookup-mapᵛ (mapMaybe suc) (slotsOf source) X))
        lookup-eq)
  slot-forward-TypingTarget
      (typing-target-end {ρ = ρ} {Ψ = source} {Φ = result}
        {Y = pivot} target)
      {X = X} lookup-eq =
    trans (lookup-remove-punch target-pivot (slotsOf result) target-X)
      (trans (cong (Vec.lookup (slotsOf result)) position-eq)
        (slot-forward-TypingTarget target source-lookup))
    where
    source-X = punchIn pivot X
    target-X = toRenameᵗ (delete↪ᵗ ρ pivot) X
    target-pivot = toRenameᵗ ρ pivot
    position-eq = sym (delete-punchIn ρ pivot X)
    source-lookup = trans
      (sym (lookup-remove-punch pivot (slotsOf source) X)) lookup-eq

  slot-backward-TypingTarget : ∀ {Θ Θ′ Δ Δ′ σ σ′}
      {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
      (target : TypingTarget ρ φ Ψ Φ) {Y a}
    → Vec.lookup σ′ Y ≡ just (φ a)
    → ∃[ X ] (Y ≡ toRenameᵗ ρ X × Vec.lookup σ X ≡ just a)
  slot-backward-TypingTarget (balanced-target extension) lookup-eq =
    slot-backward-≼ extension lookup-eq
  slot-backward-TypingTarget
      (typing-target-begin {ρ = ρ} {Y = pivot} target)
      {Y = Y} lookup-eq with target-pivot ≟ Y
    where
    target-pivot = toRenameᵗ (insert↪ᵗ ρ pivot) pivot
  slot-backward-TypingTarget
      (typing-target-begin {ρ = ρ} {Y = pivot} target)
      {Y = .(toRenameᵗ (insert↪ᵗ ρ pivot) pivot)} lookup-eq
      | yes refl =
    pivot , refl , trans (lookup-insert-here pivot _ _)
      (cong just (TypingTarget-anchor-injective target anchor-eq))
    where
    target-pivot = toRenameᵗ (insert↪ᵗ ρ pivot) pivot
    anchor-eq = just-injective
      (trans (sym (lookup-insert-here target-pivot _ _)) lookup-eq)
  slot-backward-TypingTarget
      (typing-target-begin {ρ = ρ} {Y = pivot} target)
      {Y = Y} lookup-eq | no target-pivot≢Y
      with slot-backward-TypingTarget target target-prefix-lookup
    where
    target-pivot = toRenameᵗ (insert↪ᵗ ρ pivot) pivot
    reduced = punchOut target-pivot Y target-pivot≢Y
    target-prefix-lookup = trans
      (sym (lookup-insert-other target-pivot Y _ _ target-pivot≢Y))
      lookup-eq
  slot-backward-TypingTarget
      (typing-target-begin {ρ = ρ} {Y = pivot} target)
      {Y = Y} lookup-eq | no target-pivot≢Y
      | X , position-eq , source-lookup =
    punchIn pivot X , final-position ,
      trans (lookup-insert-punch pivot _ _ X) source-lookup
    where
    target-pivot = toRenameᵗ (insert↪ᵗ ρ pivot) pivot
    final-position = trans (sym (punchIn-punchOut target-pivot Y
      target-pivot≢Y))
      (trans (cong (punchIn target-pivot) position-eq)
        (sym (insert-punchIn ρ pivot X)))
  slot-backward-TypingTarget (typing-target-typ target)
      {Y = zero} ()
  slot-backward-TypingTarget (typing-target-typ target)
      {Y = suc Y} lookup-eq
      with slot-backward-TypingTarget target lookup-eq
  slot-backward-TypingTarget (typing-target-typ target)
      {Y = suc Y} lookup-eq | X , position-eq , source-lookup =
    suc X , cong suc position-eq , source-lookup
  slot-backward-TypingTarget
      (typing-target-ν {Ψ = source} {Φ = result} target)
      {Y = Y} {a = zero} lookup-eq =
    ⊥-elim (mapMaybe-suc≢zero (Vec.lookup (slotsOf result) Y)
      (trans (sym (lookup-mapᵛ (mapMaybe suc) (slotsOf result) Y))
        lookup-eq))
  slot-backward-TypingTarget
      (typing-target-ν {Ψ = source} {Φ = result} target)
      {Y = Y} {a = suc a} lookup-eq
      with slot-backward-TypingTarget target target-prefix-lookup
    where
    target-prefix-lookup = mapMaybe-suc-just-injective
      (trans (sym (lookup-mapᵛ (mapMaybe suc) (slotsOf result) Y))
        lookup-eq)
  slot-backward-TypingTarget
      (typing-target-ν {Ψ = source} {Φ = result} target)
      {Y = Y} {a = suc a} lookup-eq
      | X , position-eq , source-lookup =
    X , position-eq , trans
      (lookup-mapᵛ (mapMaybe suc) (slotsOf source) X)
      (cong (mapMaybe suc) source-lookup)
  slot-backward-TypingTarget
      (typing-target-end {ρ = ρ} {Ψ = source} {Φ = result}
        {Y = pivot} target)
      {Y = Y} lookup-eq
      with slot-backward-TypingTarget target target-prefix-lookup
    where
    target-pivot = toRenameᵗ ρ pivot
    target-prefix-lookup = trans
      (sym (lookup-remove-punch target-pivot (slotsOf result) Y)) lookup-eq
  slot-backward-TypingTarget
      (typing-target-end {ρ = ρ} {Ψ = source} {Φ = result}
        {Y = pivot} target)
      {Y = Y} lookup-eq
      | source-prefix , position-eq , source-lookup with pivot ≟ source-prefix
  slot-backward-TypingTarget
      (typing-target-end {ρ = ρ} {Ψ = source} {Φ = result}
        {Y = pivot} target)
      {Y = Y} lookup-eq
      | .pivot , position-eq , source-lookup | yes refl =
    ⊥-elim (punchIn≢ (toRenameᵗ ρ pivot) Y (sym position-eq))
  slot-backward-TypingTarget
      (typing-target-end {ρ = ρ} {Ψ = source} {Φ = result}
        {Y = pivot} target)
      {Y = Y} lookup-eq
      | source-prefix , position-eq , source-lookup | no pivot≢source =
    reduced , final-position , source-ended-lookup
    where
    reduced = punchOut pivot source-prefix pivot≢source
    rebuild = punchIn-punchOut pivot source-prefix pivot≢source
    source-ended-lookup = trans
      (lookup-remove-punchOut pivot source-prefix (slotsOf source)
        pivot≢source) source-lookup
    final-position = punchIn-injectiveᵗ (toRenameᵗ ρ pivot)
      (trans position-eq
        (trans (cong (toRenameᵗ ρ) (sym rebuild))
          (delete-punchIn ρ pivot reduced)))

liveSlot?-TypingTarget : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (target : TypingTarget ρ φ Ψ Φ) a
  → liveSlot? σ′ (φ a)
    ≡ mapMaybe (toRenameᵗ ρ) (liveSlot? σ a)
liveSlot?-TypingTarget {σ = source} {σ′ = result} {ρ = ρ}
    {φ = φ} {Ψ = Ψ} {Φ = Φ} target a
    with liveSlot? source a in source-live
       | liveSlot? result (φ a) in target-live
liveSlot?-TypingTarget {σ = source} {σ′ = result} {ρ = ρ}
    {Ψ = Ψ} {Φ = Φ} target a | nothing | nothing = refl
liveSlot?-TypingTarget {σ = source} {σ′ = result} {ρ = ρ}
    {Ψ = Ψ} {Φ = Φ} target a | nothing | just Y =
  ⊥-elim (nothing≢just (trans (sym source-live) source-complete))
  where
  target-lookup = liveSlot?-sound result _ Y target-live
  source-image = slot-backward-TypingTarget target target-lookup
  X = proj₁ source-image
  source-lookup = proj₂ (proj₂ source-image)
  source-complete = liveSlot?-complete source (aliases-unique Ψ)
    source-lookup
  nothing≢just : ∀ {A : Set} {x : A} → nothing ≢ just x
  nothing≢just ()
liveSlot?-TypingTarget {σ = source} {σ′ = result} {ρ = ρ}
    {Ψ = Ψ} {Φ = Φ} target a | just X | nothing =
  ⊥-elim (nothing≢just (trans (sym target-live) target-complete))
  where
  source-lookup = liveSlot?-sound source a X source-live
  target-lookup = slot-forward-TypingTarget target source-lookup
  target-complete = liveSlot?-complete result (aliases-unique Φ)
    target-lookup
  nothing≢just : ∀ {A : Set} {x : A} → nothing ≢ just x
  nothing≢just ()
liveSlot?-TypingTarget {σ = source} {σ′ = result} {ρ = ρ}
    {Ψ = Ψ} {Φ = Φ} target a | just X | just Y =
  cong just (liveSlot?-unique {σ = result} target-live target-complete)
  where
  source-lookup = liveSlot?-sound source a X source-live
  target-lookup = slot-forward-TypingTarget target source-lookup
  target-complete = liveSlot?-complete result (aliases-unique Φ)
    target-lookup

slot-image-≼ : ∀ {Θ Θ′ Δ Δ′ σ σ′ k}
    {ρ : Δ ↪ᵗ Δ′} {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (extension : Ψ ≼[ k , ρ ] Φ) X
  → Vec.lookup σ′ (toRenameᵗ ρ X)
    ≡ mapMaybe (shiftAlong extension) (Vec.lookup σ X)
slot-image-≼ {σ = slots} ≼-refl X
    rewrite toRename-id-eq X
    with Vec.lookup slots X
slot-image-≼ ≼-refl X | nothing = refl
slot-image-≼ ≼-refl X | just a = refl
slot-image-≼
    (≼-ν {ρ = ρ} {Ψ = source} {Ψ′ = result} {B = B} extension) X =
  trans (lookup-mapᵛ (mapMaybe suc) (slotsOf result) _)
    (trans (cong (mapMaybe suc) (slot-image-≼ extension X))
      map-compose)
  where
  map-compose : mapMaybe suc
      (mapMaybe (shiftAlong extension) (Vec.lookup (slotsOf source) X))
    ≡ mapMaybe (shiftAlong (≼-ν {B = B} extension))
        (Vec.lookup (slotsOf source) X)
  map-compose with Vec.lookup (slotsOf source) X
  map-compose | nothing = refl
  map-compose | just a = refl
slot-image-≼ (≼-typ extension) X = slot-image-≼ extension X
slot-image-≼
    (≼-begin-end {ρ = ρ} {η = η} {Ψ = source}
      {Ψ′ = middle} {Ψ″ = result}
      {Z = pivot} extension region) X =
  trans (lookup-remove-punch target-pivot (slotsOf result) final-X)
    (trans (cong (Vec.lookup (slotsOf result))
        (begin-end-old-position ρ η pivot X))
      (trans (slot-image-≼ region (punchIn pivot (toRenameᵗ ρ X)))
        (trans (cong (mapMaybe (shiftAlong region))
            (lookup-insert-punch pivot _ (slotsOf middle)
              (toRenameᵗ ρ X)))
          (trans (cong (mapMaybe (shiftAlong region))
              (slot-image-≼ extension X)) map-compose))))
  where
  target-pivot = toRenameᵗ η pivot
  final-X = toRenameᵗ (ρ ⨟↪ᵗ delete↪ᵗ η pivot) X
  map-compose : mapMaybe (shiftAlong region)
      (mapMaybe (shiftAlong extension) (Vec.lookup (slotsOf source) X))
    ≡ mapMaybe (shiftAlong (≼-begin-end extension region))
        (Vec.lookup (slotsOf source) X)
  map-compose with Vec.lookup (slotsOf source) X
  map-compose | nothing = refl
  map-compose | just a = refl
slot-image-≼
    (≼-end-begin {ρ = ρ} {η = η} {Ψ = source}
      {Ψ′ = middle} {Ψ″ = result}
      {X = pivot} {fresh = fresh} slot-eq extension region shifted)
    X with pivot ≟ X
slot-image-≼
    (≼-end-begin {ρ = ρ} {η = η} {Ψ = source}
      {Ψ′ = middle} {Ψ″ = result}
      {X = pivot} {fresh = fresh} slot-eq extension region shifted)
    .pivot | yes refl =
  trans (lookup-insert-here new _ (slotsOf result))
    (trans (cong just (shifted-along full shifted))
      (cong (mapMaybe (shiftAlong full)) (sym slot-eq)))
  where
  full = ≼-end-begin {fresh = fresh} slot-eq extension region shifted
  inserted = insert↪ᵗ (delete↪ᵗ ρ pivot ⨟↪ᵗ η) pivot
  new = toRenameᵗ inserted pivot
slot-image-≼
    (≼-end-begin {ρ = ρ} {η = η} {Ψ = source}
      {Ψ′ = middle} {Ψ″ = result}
      {X = pivot} {fresh = fresh} slot-eq extension region shifted)
    X | no pivot≢X =
  trans (cong (Vec.lookup final-slots) (sym final-position))
    (trans (lookup-insert-punch new _ (slotsOf result) routed)
      (trans (slot-image-≼ region ended)
        (trans (cong (mapMaybe (shiftAlong region))
            (lookup-remove-punchOut old image (slotsOf middle) image-neq))
          (trans (cong (mapMaybe (shiftAlong region))
              (slot-image-≼ extension X)) map-compose))))
  where
  full = ≼-end-begin {fresh = fresh} slot-eq extension region shifted
  old = toRenameᵗ ρ pivot
  image = toRenameᵗ ρ X
  image-neq : old ≢ image
  image-neq eq = pivot≢X (toRename-injective ρ eq)
  ended = punchOut old image image-neq
  routed = toRenameᵗ η ended
  inserted = insert↪ᵗ (delete↪ᵗ ρ pivot ⨟↪ᵗ η) pivot
  new = toRenameᵗ inserted pivot
  final-slots = insertᵛ new _ (slotsOf result)
  final-position = end-begin-old-position ρ η pivot X pivot≢X image-neq
  map-compose : mapMaybe (shiftAlong region)
      (mapMaybe (shiftAlong extension) (Vec.lookup (slotsOf source) X))
    ≡ mapMaybe (shiftAlong full) (Vec.lookup (slotsOf source) X)
  map-compose with Vec.lookup (slotsOf source) X
  map-compose | nothing = refl
  map-compose | just a = refl

slot-image-TypingTarget : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (target : TypingTarget ρ φ Ψ Φ) X
  → Vec.lookup σ′ (toRenameᵗ ρ X)
    ≡ mapMaybe φ (Vec.lookup σ X)
slot-image-TypingTarget (balanced-target extension) X =
  slot-image-≼ extension X
slot-image-TypingTarget
    (typing-target-begin {ρ = ρ} {φ = φ} {Ψ = source} {Φ = result}
      {Y = pivot} {a = a} target) X
    with pivot ≟ X
slot-image-TypingTarget
    (typing-target-begin {ρ = ρ} {φ = φ} {Ψ = source} {Φ = result}
      {Y = pivot} {a = a} target) .pivot
    | yes refl =
  trans (lookup-insert-here target-pivot (just (φ a)) (slotsOf result))
    (cong (mapMaybe φ)
      (sym (lookup-insert-here pivot (just a) (slotsOf source))))
  where
  target-pivot = toRenameᵗ (insert↪ᵗ ρ pivot) pivot
slot-image-TypingTarget
    (typing-target-begin {ρ = ρ} {φ = φ} {Ψ = source} {Φ = result}
      {Y = pivot} {a = a} target) X
    | no pivot≢X =
  trans (cong (Vec.lookup target-slots) (sym position-eq))
    (trans (lookup-insert-punch target-pivot (just (φ a))
        (slotsOf result) source-image)
      (trans (slot-image-TypingTarget target reduced)
        (cong (mapMaybe φ) (sym source-lookup))))
  where
  reduced = punchOut pivot X pivot≢X
  source-image = toRenameᵗ ρ reduced
  target-pivot = toRenameᵗ (insert↪ᵗ ρ pivot) pivot
  target-slots = insertᵛ target-pivot (just (φ a)) (slotsOf result)
  source-lookup = lookup-insert-other pivot X (just a)
    (slotsOf source) pivot≢X
  position-eq = trans (sym (insert-punchIn ρ pivot reduced))
    (cong (toRenameᵗ (insert↪ᵗ ρ pivot))
      (punchIn-punchOut pivot X pivot≢X))
slot-image-TypingTarget (typing-target-typ target) zero = refl
slot-image-TypingTarget (typing-target-typ target) (suc X) =
  slot-image-TypingTarget target X
slot-image-TypingTarget
    (typing-target-ν {φ = φ} {Ψ = source} {Φ = result} target) X =
  trans (lookup-mapᵛ (mapMaybe suc) (slotsOf result) _)
    (trans (cong (mapMaybe suc) (slot-image-TypingTarget target X))
      map-compose)
  where
  map-compose : mapMaybe suc
      (mapMaybe φ (Vec.lookup (slotsOf source) X))
    ≡ mapMaybe (extᵗ φ)
        (Vec.lookup (mapᵛ (mapMaybe suc) (slotsOf source)) X)
  map-compose = trans
    (mapMaybe-suc-ext φ (Vec.lookup (slotsOf source) X))
    (cong (mapMaybe (extᵗ φ))
      (sym (lookup-mapᵛ (mapMaybe suc) (slotsOf source) X)))
slot-image-TypingTarget
    (typing-target-end {ρ = ρ} {Ψ = source} {Φ = result}
      {Y = pivot} target) X =
  trans (lookup-remove-punch target-pivot (slotsOf result) target-X)
    (trans (cong (Vec.lookup (slotsOf result))
        (sym (delete-punchIn ρ pivot X)))
      (trans (slot-image-TypingTarget target (punchIn pivot X))
        (cong (mapMaybe _)
          (sym (lookup-remove-punch pivot (slotsOf source) X)))))
  where
  target-pivot = toRenameᵗ ρ pivot
  target-X = toRenameᵗ (delete↪ᵗ ρ pivot) X

repoint?-TypingTarget : ∀ {Ω Θ Θ′ D Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (n : TyCtx) (target-rel : TypingTarget ρ φ Ψ Φ)
    (source-resolve : TyVar Θ → Maybe (Ty Δ))
    (target-resolve : TyVar Θ′ → Maybe (Ty Δ′))
    (birth : Vec.Vec (Maybe (TyVar Ω)) D)
    (anchor-map : TyVar (suc Ω) → TyVar Θ)
    (route : TyVar D → Maybe (TyVar (n + Δ))) (A : Ty D)
  → (∀ q → target-resolve (φ q)
      ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (source-resolve q))
  → repoint? target-resolve σ′ birth (λ q → φ (anchor-map q))
      (route-mapⁿ n ρ route) (raise n) A
    ≡ mapMaybe (renameᵗ (toRenameᵗ (lift↪ᵗ n ρ)))
        (repoint? source-resolve σ birth anchor-map route (raise n) A)
repoint?-TypingTarget n target-rel source-resolve target-resolve birth
    anchor-map route (＇ X) resolve-eq with Vec.lookup birth X
repoint?-TypingTarget n target-rel source-resolve target-resolve birth
    anchor-map route (＇ X) resolve-eq | nothing with route X
repoint?-TypingTarget n target-rel source-resolve target-resolve birth
    anchor-map route (＇ X) resolve-eq | nothing | nothing = refl
repoint?-TypingTarget n target-rel source-resolve target-resolve birth
    anchor-map route (＇ X) resolve-eq | nothing | just Y = refl
repoint?-TypingTarget {ρ = ρ} {Ψ = source} n target-rel
    source-resolve target-resolve
    birth anchor-map route (＇ X) resolve-eq | just q
    rewrite liveSlot?-TypingTarget target-rel (anchor-map (suc q))
    with liveSlot? (slotsOf source) (anchor-map (suc q))
repoint?-TypingTarget {ρ = ρ} {Ψ = source} n target-rel
    source-resolve target-resolve
    birth anchor-map route (＇ X) resolve-eq | just q | just Y =
  cong (λ Z → just (＇ Z)) (sym (raise-rename n ρ Y))
repoint?-TypingTarget {ρ = ρ} {φ = φ} {Ψ = source} n target-rel source-resolve
    target-resolve birth anchor-map route (＇ X) resolve-eq
    | just q | nothing
    with source-resolve (anchor-map (suc q))
       | target-resolve (φ (anchor-map (suc q)))
       | resolve-eq (anchor-map (suc q))
repoint?-TypingTarget n target-rel source-resolve target-resolve birth
    anchor-map route (＇ X) resolve-eq | just q | nothing
    | nothing | .nothing | refl = refl
repoint?-TypingTarget {ρ = ρ} n target-rel source-resolve target-resolve
    birth anchor-map route (＇ X) resolve-eq | just q | nothing
    | just B | .(just (renameᵗ (toRenameᵗ ρ) B)) | refl =
  cong just (sym (rename-raise n ρ B))
repoint?-TypingTarget n target-rel source-resolve target-resolve birth
    anchor-map route (‵ ι) resolve-eq = refl
repoint?-TypingTarget n target-rel source-resolve target-resolve birth
    anchor-map route ★ resolve-eq = refl
repoint?-TypingTarget n target-rel source-resolve target-resolve birth
    anchor-map route (A ⇒ B) resolve-eq =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-TypingTarget n target-rel source-resolve target-resolve
          birth anchor-map route A resolve-eq)
        (repoint?-TypingTarget n target-rel source-resolve target-resolve
          birth anchor-map route B resolve-eq))
      (trans (rename-⇒? _
          (repoint? source-resolve _ birth anchor-map route (raise n) A)
          (repoint? source-resolve _ birth anchor-map route (raise n) B))
        (cong (mapMaybe (renameᵗ (toRenameᵗ (lift↪ᵗ n _))))
          (sym (repoint?-arrow _ _ _ _ _ _ A B)))))
repoint?-TypingTarget {ρ = ρ} n target-rel source-resolve target-resolve
    birth anchor-map route (`∀ A) resolve-eq =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (trans (repoint?-route-cong _ _ _ _ _ _ _ A
            (route-map-ext n ρ route))
          (repoint?-TypingTarget (suc n) target-rel source-resolve
            target-resolve (nothing Vec.∷ birth) anchor-map
            (ext-route route) A resolve-eq)))
      (trans (rename-all?-keep (lift↪ᵗ n ρ)
          (repoint? source-resolve _ (nothing Vec.∷ birth) anchor-map
            (ext-route route) (raise (suc n)) A))
        (cong (mapMaybe (renameᵗ (toRenameᵗ (lift↪ᵗ n ρ))))
          (sym (repoint?-all _ _ _ _ _ _ A)))))

repoint?-current-TypingTarget : ∀ {Θ Θ′ Ω Δ Δ′ D σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {source : TyEnv Θ Δ σ} {current : TyEnv Θ′ Δ′ σ′}
    (n : TyCtx) (current-rel : TypingTarget ρ φ source current)
    (resolve : TyVar Ω → Maybe (Ty D))
    (target : Vec.Vec (Maybe (TyVar Ω)) D)
    (source-anchor : TyVar (suc Θ) → TyVar Ω)
    (target-anchor : TyVar (suc Θ′) → TyVar Ω)
    (source-route : TyVar Δ → Maybe (TyVar (n + D)))
    (target-route : TyVar Δ′ → Maybe (TyVar (n + D)))
    (A : Ty Δ)
  → (∀ q → target-anchor (suc (φ q)) ≡ source-anchor (suc q))
  → (∀ X → target-route (toRenameᵗ ρ X) ≡ source-route X)
  → repoint? resolve target σ′ target-anchor target-route (raise n)
      (renameᵗ (toRenameᵗ ρ) A)
    ≡ repoint? resolve target σ source-anchor source-route (raise n) A
repoint?-current-TypingTarget {σ = source-slots} n current-rel resolve target source-anchor
    target-anchor source-route target-route (＇ X) anchor-eq route-eq
    rewrite slot-image-TypingTarget current-rel X
    with Vec.lookup source-slots X
repoint?-current-TypingTarget n current-rel resolve target source-anchor
    target-anchor source-route target-route (＇ X) anchor-eq route-eq
    | nothing rewrite route-eq X = refl
repoint?-current-TypingTarget n current-rel resolve target source-anchor
    target-anchor source-route target-route (＇ X) anchor-eq route-eq
    | just q rewrite anchor-eq q = refl
repoint?-current-TypingTarget n current-rel resolve target source-anchor
    target-anchor source-route target-route (‵ ι) anchor-eq route-eq = refl
repoint?-current-TypingTarget n current-rel resolve target source-anchor
    target-anchor source-route target-route ★ anchor-eq route-eq = refl
repoint?-current-TypingTarget {ρ = ρ} {source = source}
    {current = current} n current-rel resolve target source-anchor
    target-anchor source-route target-route (A ⇒ B) anchor-eq route-eq =
  trans (repoint?-arrow resolve target (slotsOf current) target-anchor
      target-route (raise n) (renameᵗ (toRenameᵗ ρ) A)
      (renameᵗ (toRenameᵗ ρ) B))
    (trans (cong₂ _⇒?_
        (repoint?-current-TypingTarget n current-rel resolve target
          source-anchor target-anchor source-route target-route A
          anchor-eq route-eq)
        (repoint?-current-TypingTarget n current-rel resolve target
          source-anchor target-anchor source-route target-route B
          anchor-eq route-eq))
      (sym (repoint?-arrow resolve target (slotsOf source) source-anchor
        source-route (raise n) A B)))
repoint?-current-TypingTarget {ρ = ρ} {source = source}
    {current = current} n current-rel resolve target
    source-anchor target-anchor source-route target-route (`∀ A)
    anchor-eq route-eq =
  trans (repoint?-all resolve target (slotsOf current) target-anchor
      target-route (raise n)
      (renameᵗ (extᵗ (toRenameᵗ ρ)) A))
    (trans (cong all?
        (trans body-transport
          (repoint?-current-TypingTarget (suc n)
            (typing-target-typ current-rel)
            resolve target source-anchor target-anchor
            (ext-route source-route) (ext-route target-route) A
            anchor-eq extended-route)))
      (sym (repoint?-all resolve target (slotsOf source) source-anchor
        source-route (raise n) A)))
  where
  body-eq = renameᵗ-cong A (toRename-keep-eq ρ)

  body-transport = cong
    (repoint? resolve target (nothing Vec.∷ slotsOf current)
      target-anchor (ext-route target-route)
      (λ X → suc (raise n X)))
    (sym body-eq)

  extended-route : ∀ X
    → ext-route target-route (toRenameᵗ (keep ρ) X)
      ≡ ext-route source-route X
  extended-route zero = refl
  extended-route (suc X) = cong (mapMaybe suc) (route-eq X)

scanRep?-current-TypingTarget : ∀ {Θ Θ′ Ω Δ Δ′ D σ σ′ τ}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {source : TyEnv Θ Δ σ} {current : TyEnv Θ′ Δ′ σ′}
    (current-rel : TypingTarget ρ φ source current)
    (resolve : TyVar Ω → Maybe (Ty D)) (target : TyEnv Ω D τ)
    (source-anchor : TyVar Θ → TyVar Ω)
    (target-anchor : TyVar Θ′ → TyVar Ω)
    (source-route : TyVar Δ → Maybe (TyVar D))
    (target-route : TyVar Δ′ → Maybe (TyVar D))
    (a : TyVar Θ)
  → (∀ q → target-anchor (φ q) ≡ source-anchor q)
  → (∀ X → target-route (toRenameᵗ ρ X) ≡ source-route X)
  → scanRep? resolve target current target-anchor target-route (φ a)
    ≡ scanRep? resolve target source source-anchor source-route a
scanRep?-current-TypingTarget
    (balanced-target extension) resolve target source-anchor target-anchor
    source-route target-route a anchor-eq route-eq =
  scanRep?-current-≼ extension resolve target source-anchor target-anchor
    source-route target-route a anchor-eq (λ X lex → route-eq X)
scanRep?-current-TypingTarget
    (typing-target-begin {ρ = ρ} {Y = pivot} current-rel)
    resolve target source-anchor target-anchor source-route target-route a
    anchor-eq route-eq =
  scanRep?-current-TypingTarget current-rel resolve target source-anchor
    target-anchor (λ X → source-route (punchIn pivot X))
    (λ X → target-route (punchIn target-pivot X)) a anchor-eq begin-route
  where
  target-pivot = toRenameᵗ (insert↪ᵗ ρ pivot) pivot
  begin-route : ∀ X
    → target-route (punchIn target-pivot (toRenameᵗ ρ X))
      ≡ source-route (punchIn pivot X)
  begin-route X = trans
    (cong target-route (sym (insert-punchIn ρ pivot X)))
    (route-eq (punchIn pivot X))
scanRep?-current-TypingTarget (typing-target-typ current-rel)
    resolve target source-anchor target-anchor source-route target-route a
    anchor-eq route-eq =
  scanRep?-current-TypingTarget current-rel resolve target source-anchor
    target-anchor (λ X → source-route (suc X))
    (λ X → target-route (suc X)) a anchor-eq (λ X → route-eq (suc X))
scanRep?-current-TypingTarget
    (typing-target-ν {ρ = ρ} {A = A} current-rel)
    resolve target source-anchor target-anchor source-route target-route zero
    anchor-eq route-eq =
  repoint?-current-TypingTarget zero current-rel resolve (slotsOf target)
    source-anchor target-anchor source-route target-route A
    (λ q → anchor-eq (suc q)) route-eq
scanRep?-current-TypingTarget (typing-target-ν current-rel)
    resolve target source-anchor target-anchor source-route target-route
    (suc a) anchor-eq route-eq =
  scanRep?-current-TypingTarget current-rel resolve target
    (λ q → source-anchor (suc q)) (λ q → target-anchor (suc q))
    source-route target-route a (λ q → anchor-eq (suc q)) route-eq
scanRep?-current-TypingTarget
    (typing-target-end {ρ = ρ} {Y = pivot} current-rel)
    resolve target source-anchor target-anchor source-route target-route a
    anchor-eq route-eq =
  scanRep?-current-TypingTarget current-rel resolve target source-anchor
    target-anchor (route-end pivot source-route)
    (route-end (toRenameᵗ ρ pivot) target-route) a anchor-eq
    (route-end-image ρ pivot source-route target-route route-eq)

scanRep?-outer-TypingTarget : ∀ {Θ Θ′ Θ₀ Δ Δ′ Δ₀ σ σ′ σ₀}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (target-rel : TypingTarget ρ φ Ψ Φ)
    (source-resolve : TyVar Θ → Maybe (Ty Δ))
    (target-resolve : TyVar Θ′ → Maybe (Ty Δ′))
    (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (source-route : TyVar Δ₀ → Maybe (TyVar Δ))
    (target-route : TyVar Δ₀ → Maybe (TyVar Δ′))
    (a : TyVar Θ₀)
  → (∀ q → target-resolve (φ q)
      ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (source-resolve q))
  → (∀ X → target-route X
      ≡ mapMaybe (toRenameᵗ ρ) (source-route X))
  → scanRep? target-resolve Φ current (λ q → φ (anchor-map q))
      target-route a
    ≡ mapMaybe (renameᵗ (toRenameᵗ ρ))
        (scanRep? source-resolve Ψ current anchor-map source-route a)
scanRep?-outer-TypingTarget target-rel source-resolve target-resolve ∅
    anchor-map source-route target-route () resolve-eq route-eq
scanRep?-outer-TypingTarget target-rel source-resolve target-resolve
    (current ,begin[ Y ≔ q ]⟨ fresh ⟩) anchor-map source-route
    target-route a resolve-eq route-eq =
  scanRep?-outer-TypingTarget target-rel source-resolve target-resolve
    current anchor-map (λ X → source-route (punchIn Y X))
    (λ X → target-route (punchIn Y X)) a resolve-eq
    (λ X → route-eq (punchIn Y X))
scanRep?-outer-TypingTarget target-rel source-resolve target-resolve
    (current ,typ) anchor-map source-route target-route a
    resolve-eq route-eq =
  scanRep?-outer-TypingTarget target-rel source-resolve target-resolve
    current anchor-map (λ X → source-route (suc X))
    (λ X → target-route (suc X)) a resolve-eq
    (λ X → route-eq (suc X))
scanRep?-outer-TypingTarget {ρ = ρ} {φ = φ} {Φ = Φ} target-rel source-resolve
    target-resolve (current ,:= A) anchor-map source-route target-route zero
    resolve-eq route-eq =
  trans (repoint?-route-cong target-resolve (slotsOf Φ)
      (slotsOf current) (λ q → φ (anchor-map q)) target-route
      (route-map ρ source-route) (λ X → X) A route-eq)
    (repoint?-TypingTarget zero target-rel source-resolve target-resolve
      (slotsOf current) anchor-map source-route A resolve-eq)
scanRep?-outer-TypingTarget target-rel source-resolve target-resolve
    (current ,:= A) anchor-map source-route target-route (suc a)
    resolve-eq route-eq =
  scanRep?-outer-TypingTarget target-rel source-resolve target-resolve
    current (λ q → anchor-map (suc q)) source-route target-route a
    resolve-eq route-eq
scanRep?-outer-TypingTarget {ρ = ρ} target-rel source-resolve
    target-resolve (current ,end[ Y ]) anchor-map source-route
    target-route a resolve-eq route-eq =
  scanRep?-outer-TypingTarget target-rel source-resolve target-resolve
    current anchor-map (route-end Y source-route)
    (route-end Y target-route) a resolve-eq end-route-eq
  where
  end-route-eq : ∀ X
    → route-end Y target-route X
      ≡ mapMaybe (toRenameᵗ ρ) (route-end Y source-route X)
  end-route-eq X with Y ≟ X
  end-route-eq .Y | yes refl = refl
  end-route-eq X | no Y≢X = route-eq (punchOut Y X Y≢X)

-- Increasing the evaluator fuel cannot change a successful lookup.  This is
-- the small saturation fact needed when a matched ν sits outside a balanced
-- extension: the corresponding fresh anchors have different absolute birth
-- depths, although both computations have already reached the same ν entry.

repoint?-success : ∀ {Θ₀ Θ Δ₀ Δ Δout}
    {left right : TyVar Θ → Maybe (Ty Δ)}
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A : Ty Δ₀) {B}
  → (∀ q {C} → left q ≡ just C → right q ≡ just C)
  → repoint? left target birth anchor-map route live-ren A ≡ just B
  → repoint? right target birth anchor-map route live-ren A ≡ just B
repoint?-success target birth anchor-map route live-ren (＇ X)
    resolve-success eq with Vec.lookup birth X
repoint?-success target birth anchor-map route live-ren (＇ X)
    resolve-success eq | nothing with route X
repoint?-success target birth anchor-map route live-ren (＇ X)
    resolve-success () | nothing | nothing
repoint?-success target birth anchor-map route live-ren (＇ X)
    resolve-success eq | nothing | just Y = eq
repoint?-success target birth anchor-map route live-ren (＇ X)
    resolve-success eq | just q with liveSlot? target (anchor-map (suc q))
repoint?-success target birth anchor-map route live-ren (＇ X)
    resolve-success eq | just q | just Y = eq
repoint?-success {left = left} {right = right} target birth anchor-map
    route live-ren (＇ X) resolve-success eq | just q | nothing
    with left (anchor-map (suc q)) in left-eq
repoint?-success target birth anchor-map route live-ren (＇ X)
    resolve-success () | just q | nothing | nothing
repoint?-success {left = left} target birth anchor-map route live-ren (＇ X)
    resolve-success eq | just q | nothing | just C
    rewrite resolve-success (anchor-map (suc q)) left-eq = eq
repoint?-success target birth anchor-map route live-ren (‵ ι)
    resolve-success eq = eq
repoint?-success target birth anchor-map route live-ren ★
    resolve-success eq = eq
repoint?-success {left = left} target birth anchor-map route live-ren
    (A ⇒ B) resolve-success eq with repoint? left target birth anchor-map
      route live-ren A in left-A
repoint?-success target birth anchor-map route live-ren (A ⇒ B)
    resolve-success () | nothing
repoint?-success {left = left} target birth anchor-map route live-ren
    (A ⇒ B) resolve-success eq | just A′
    with repoint? left target birth anchor-map route live-ren B in left-B
repoint?-success target birth anchor-map route live-ren (A ⇒ B)
    resolve-success () | just A′ | nothing
repoint?-success target birth anchor-map route live-ren (A ⇒ B)
    resolve-success refl | just A′ | just B′
    rewrite repoint?-success target birth anchor-map route live-ren A
              resolve-success left-A
          | repoint?-success target birth anchor-map route live-ren B
              resolve-success left-B = refl
repoint?-success {left = left} target birth anchor-map route live-ren
    (`∀ A) resolve-success eq
    with repoint? left target (nothing Vec.∷ birth) anchor-map
      (ext-route route) (λ X → suc (live-ren X)) A in left-A
repoint?-success target birth anchor-map route live-ren (`∀ A)
    resolve-success () | nothing
repoint?-success target birth anchor-map route live-ren (`∀ A)
    resolve-success refl | just A′
    rewrite repoint?-success target (nothing Vec.∷ birth) anchor-map
      (ext-route route) (λ X → suc (live-ren X)) A resolve-success left-A = refl

scanRep?-success : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
    {left right : TyVar Θ → Maybe (Ty Δ)}
    (target : TyEnv Θ Δ σ) (current : TyEnv Θ₀ Δ₀ σ₀)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀) {A}
  → (∀ q {C} → left q ≡ just C → right q ≡ just C)
  → scanRep? left target current anchor-map route a ≡ just A
  → scanRep? right target current anchor-map route a ≡ just A
scanRep?-success target ∅ anchor-map route () resolve-success eq
scanRep?-success target (current ,begin[ Y ≔ q ]⟨ fresh ⟩)
    anchor-map route a resolve-success eq =
  scanRep?-success target current anchor-map
    (λ X → route (punchIn Y X)) a resolve-success eq
scanRep?-success target (current ,typ) anchor-map route a
    resolve-success eq =
  scanRep?-success target current anchor-map (λ X → route (suc X))
    a resolve-success eq
scanRep?-success target (current ,:= B) anchor-map route zero
    resolve-success eq =
  repoint?-success (slotsOf target) (slotsOf current) anchor-map route
    (λ X → X) B resolve-success eq
scanRep?-success target (current ,:= B) anchor-map route (suc a)
    resolve-success eq =
  scanRep?-success target current (λ q → anchor-map (suc q)) route a
    resolve-success eq
scanRep?-success target (current ,end[ Y ]) anchor-map route a
    resolve-success eq =
  scanRep?-success target current anchor-map (route-end Y route) a
    resolve-success eq

repFuel?-success-step : ∀ fuel {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {a A}
  → repFuel? fuel Ψ a ≡ just A
  → repFuel? (suc fuel) Ψ a ≡ just A
repFuel?-success-step zero ()
repFuel?-success-step (suc fuel) {Ψ = Ψ} eq =
  scanRep?-success Ψ Ψ (λ q → q) (λ X → just X) _
    (λ q success → repFuel?-success-step fuel success) eq

repFuel?-success-add : ∀ extra fuel {Θ Δ σ}
    {Ψ : TyEnv Θ Δ σ} {a A}
  → repFuel? fuel Ψ a ≡ just A
  → repFuel? (extra + fuel) Ψ a ≡ just A
repFuel?-success-add zero fuel eq = eq
repFuel?-success-add (suc extra) fuel eq =
  repFuel?-success-step (extra + fuel)
    (repFuel?-success-add extra fuel eq)

≼-anchor-count : ∀ {Θ Θ′ Δ Δ′ σ σ′ k} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
  → Ψ ≼[ k , ρ ] Φ
  → Θ′ ≡ k + Θ
≼-anchor-count ≼-refl = refl
≼-anchor-count (≼-ν extension) = cong suc (≼-anchor-count extension)
≼-anchor-count (≼-typ extension) = ≼-anchor-count extension
≼-anchor-count {Θ = Θ}
    (≼-begin-end {k = k} {k′ = k′} extension region) =
  trans (≼-anchor-count region)
    (trans (cong (k′ +_) (≼-anchor-count extension))
      (trans (sym (+-assoc k′ k Θ))
        (cong (_+ Θ) (+-comm k′ k))))
≼-anchor-count {Θ = Θ}
    (≼-end-begin {k = k} {k′ = k′}
      slot-eq extension region shifted) =
  trans (≼-anchor-count region)
    (trans (cong (k′ +_) (≼-anchor-count extension))
      (trans (sym (+-assoc k′ k Θ))
        (cong (_+ Θ) (+-comm k′ k))))

TypingTarget-anchor-count : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
  → TypingTarget ρ φ Ψ Φ
  → ∃[ extra ] Θ′ ≡ extra + Θ
TypingTarget-anchor-count (balanced-target extension) =
  _ , ≼-anchor-count extension
TypingTarget-anchor-count (typing-target-begin target) =
  TypingTarget-anchor-count target
TypingTarget-anchor-count (typing-target-typ target) =
  TypingTarget-anchor-count target
TypingTarget-anchor-count (typing-target-ν target)
    with TypingTarget-anchor-count target
TypingTarget-anchor-count (typing-target-ν target) | extra , count =
  extra , trans (cong suc count) (sym (+-suc extra _))
TypingTarget-anchor-count (typing-target-end target) =
  TypingTarget-anchor-count target

TypingTarget-fuel-offset : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (target : TypingTarget ρ φ Ψ Φ) (a : TyVar Θ)
  → ∃[ extra ] (Θ′ ∸ toℕ (φ a)) ≡ extra + (Θ ∸ toℕ a)
TypingTarget-fuel-offset (balanced-target extension) a =
  zero , shifted-fuel (shiftAlong-shifted extension a)
TypingTarget-fuel-offset (typing-target-begin target) a =
  TypingTarget-fuel-offset target a
TypingTarget-fuel-offset (typing-target-typ target) a =
  TypingTarget-fuel-offset target a
TypingTarget-fuel-offset {Θ = suc Θ} {Θ′ = suc Θ′}
    (typing-target-ν target) zero with TypingTarget-anchor-count target
TypingTarget-fuel-offset (typing-target-ν target) zero
    | extra , count = extra , trans (cong suc count) (sym (+-suc extra _))
TypingTarget-fuel-offset (typing-target-ν target) (suc a) =
  TypingTarget-fuel-offset target a
TypingTarget-fuel-offset (typing-target-end target) a =
  TypingTarget-fuel-offset target a

repFuel?-TypingTarget : ∀ fuel {Θ Θ′ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (target : TypingTarget ρ φ Ψ Φ) a
  → repFuel? fuel Φ (φ a)
    ≡ mapMaybe (renameᵗ (toRenameᵗ ρ)) (repFuel? fuel Ψ a)
repFuel?-TypingTarget zero target a = refl
repFuel?-TypingTarget (suc fuel) {ρ = ρ} {φ = φ}
    {Ψ = Ψ} {Φ = Φ} target a =
  trans (scanRep?-current-TypingTarget target (repFuel? fuel Φ) Φ
      φ (λ q → q) (route-map ρ (λ X → just X))
      (λ X → just X) a (λ q → refl) (λ X → refl))
    (scanRep?-outer-TypingTarget target (repFuel? fuel Ψ)
      (repFuel? fuel Φ) Ψ (λ q → q) (λ X → just X)
      (route-map ρ (λ X → just X)) a
      (λ q → repFuel?-TypingTarget fuel target q) (λ X → refl))

rep?-TypingTarget : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    (target : TypingTarget ρ φ Ψ Φ) (a : TyVar Θ) {A}
  → rep? Ψ a ≡ just A
  → rep? Φ (φ a) ≡ just (renameᵗ (toRenameᵗ ρ) A)
rep?-TypingTarget {Θ = Θ} {ρ = ρ} target a eq
    with TypingTarget-fuel-offset target a
rep?-TypingTarget {Θ = Θ} {ρ = ρ} target a eq
    | extra , fuel-eq rewrite fuel-eq =
  trans (repFuel?-TypingTarget (extra + (Θ ∸ toℕ a)) target a)
    (cong (mapMaybe (renameᵗ (toRenameᵗ ρ)))
      (repFuel?-success-add extra (Θ ∸ toℕ a) eq))

fresh-TypingTarget : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′} {a}
  → TypingTarget ρ φ Ψ Φ
  → a ∉ᵛ σ
  → φ a ∉ᵛ σ′
fresh-TypingTarget target fresh Y target-lookup
    with slot-backward-TypingTarget target target-lookup
fresh-TypingTarget target fresh .(toRenameᵗ _ X) target-lookup
    | X , refl , source-lookup = fresh X source-lookup

typingTarget-begin : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    {Y : TyVar (suc Δ)} {a : TyVar Θ} {fresh : a ∉ᵛ σ}
  → (target : TypingTarget ρ φ Ψ Φ)
  → TypingTarget (insert↪ᵗ ρ Y) φ
      (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩)
      (Φ ,begin[ toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ φ a
        ]⟨ fresh-TypingTarget target fresh ⟩)
typingTarget-begin target = typing-target-begin target

------------------------------------------------------------------------
-- Master typing transport
------------------------------------------------------------------------

⊢transport-target : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → TypingTarget ρ φ Ψ Φ
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ (renameᶿ φ M) ⦂ renameᵗ (toRenameᵗ ρ) A
⊢transport-target target (⊢` x∈) = ⊢` (renameᵗ-∋ _ x∈)
⊢transport-target target (⊢ƛ M⊢) =
  ⊢ƛ (⊢transport-target target M⊢)
⊢transport-target target (⊢· L⊢ M⊢) =
  ⊢· (⊢transport-target target L⊢)
    (⊢transport-target target M⊢)
⊢transport-target {ρ = ρ} {Φ = Φ} {Γ = Γ}
    target (⊢Λ {A = A} M⊢) =
  ⊢Λ body⊢
  where
  renamed-body⊢ = ⊢transport-target (typing-target-typ target) M⊢

  body-context⊢ = subst≡
    (λ Γ′ → Φ ,typ ∣ Γ′
      ⊢ renameᵗᵐ (keep ρ) (renameᶿ _ _) ⦂ _)
    (renameCtx-keep-shift ρ Γ) renamed-body⊢

  body⊢ = subst≡
    (λ B → Φ ,typ ∣ renameCtx suc (renameCtx (toRenameᵗ ρ) Γ)
      ⊢ renameᵗᵐ (keep ρ) (renameᶿ _ _) ⦂ B)
    (renameᵗ-cong A (toRename-keep-eq ρ)) body-context⊢
⊢transport-target {ρ = ρ} {Φ = Φ} {Γ = Γ}
    {M = L ⦂∀ C [ A ]} target (⊢⦂∀ L⊢) =
  subst≡
    (λ B → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ (renameᶿ _ L) ⦂∀
          renameᵗ (toRenameᵗ (keep ρ)) C
          [ renameᵗ (toRenameᵗ ρ) A ] ⦂ B)
    (sym (rename-open↪ᵗ ρ C A)) (⊢⦂∀ body⊢)
  where
  body-eq = renameᵗ-cong C (toRename-keep-eq ρ)
  body⊢ = subst≡
    (λ B → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ (renameᶿ _ L) ⦂ `∀ B)
    (sym body-eq) (⊢transport-target target L⊢)
⊢transport-target {ρ = ρ} target (⊢$ κ) =
  subst≡ (λ A → _ ∣ _ ⊢ $ κ ⦂ A)
    (constTy-renameᵗ (toRenameᵗ ρ) κ) (⊢$ κ)
⊢transport-target target (⊢⊕ addℕ L⊢ M⊢) =
  ⊢⊕ addℕ (⊢transport-target target L⊢)
    (⊢transport-target target M⊢)
⊢transport-target target (⊢⊕ and𝔹 L⊢ M⊢) =
  ⊢⊕ and𝔹 (⊢transport-target target L⊢)
    (⊢transport-target target M⊢)
⊢transport-target {ρ = ρ} target (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢transport-target target M⊢) (renameᵐᶜ ρ c)
⊢transport-target target (⊢ν M⊢) =
  ⊢ν (⊢transport-target (typing-target-ν target) M⊢)
⊢transport-target {ρ = ρ} {φ = φ} {Φ = Φ} target
    (⊢reveal {A = A} {B = B} {C = C} {Y = Y} {α = α}
      {fresh = fresh} α-eq c⊢ M⊢) =
  ⊢reveal (rep?-TypingTarget target α α-eq) conversion⊢ body⊢
  where
  ρ⁺ = insert↪ᵗ ρ Y
  Y′ = toRenameᵗ ρ⁺ Y

  body⊢ = ⊢transport-target (typingTarget-begin target) M⊢

  conversion-representation⊢ = subst≡
    (λ R → ⊢↑[ Y′ ⦂ R ] _
      ⦂ renameᵗ (toRenameᵗ ρ⁺) A
      ↝ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y B))
    (rename-insert-wk ρ Y C)
    (rename-⊢↑ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ = subst≡
    (λ B′ → ⊢↑[ Y′
        ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ ρ) C) ] _
      ⦂ renameᵗ (toRenameᵗ ρ⁺) A ↝ B′)
    (rename-insert-wk ρ Y B) conversion-representation⊢
⊢transport-target {ρ = ρ⁺@(keep ρ)} {φ = φ} target
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} {α = α}
      slot-eq α-eq c⊢ M⊢) =
  ⊢conceal target-slot target-rep conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  ended-target = typing-target-end target

  target-slot = slot-forward-TypingTarget target slot-eq
  target-rep = rep?-TypingTarget ended-target α α-eq
  body⊢ = ⊢transport-target ended-target M⊢

  conversion-representation⊢ = subst≡
    (λ R → ⊢↓[ Y′ ⦂ R ] _
      ⦂ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y A)
      ↝ renameᵗ (toRenameᵗ ρ⁺) B)
    (rename-delete-wk ρ⁺ Y C)
    (rename-⊢↓ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ = subst≡
    (λ A′ → ⊢↓[ Y′
        ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ deleted) C) ] _
      ⦂ A′ ↝ renameᵗ (toRenameᵗ ρ⁺) B)
    (rename-delete-wk ρ⁺ Y A) conversion-representation⊢
⊢transport-target {ρ = ρ⁺@(skip ρ)} {φ = φ} target
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} {α = α}
      slot-eq α-eq c⊢ M⊢) =
  ⊢conceal target-slot target-rep conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  ended-target = typing-target-end target

  target-slot = slot-forward-TypingTarget target slot-eq
  target-rep = rep?-TypingTarget ended-target α α-eq
  body⊢ = ⊢transport-target ended-target M⊢

  conversion-representation⊢ = subst≡
    (λ R → ⊢↓[ Y′ ⦂ R ] _
      ⦂ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y A)
      ↝ renameᵗ (toRenameᵗ ρ⁺) B)
    (rename-delete-wk ρ⁺ Y C)
    (rename-⊢↓ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ = subst≡
    (λ A′ → ⊢↓[ Y′
        ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ deleted) C) ] _
      ⦂ A′ ↝ renameᵗ (toRenameᵗ ρ⁺) B)
    (rename-delete-wk ρ⁺ Y A) conversion-representation⊢
⊢transport-target target ⊢blame = ⊢blame

⊢≼ : ∀ {Θ Θ′ Δ Δ′ σ σ′ k} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    {M : Term Θ Δ} {A : Ty Δ}
  → (extension : Ψ ≼[ k , ρ ] Φ)
  → Ψ ∣ [] ⊢ M ⦂ A
  → Φ ∣ [] ⊢ renameᵗᵐ ρ (renameᶿ (shiftAlong extension) M)
      ⦂ renameᵗ (toRenameᵗ ρ) A
⊢≼ extension M⊢ = ⊢transport-target (balanced-target extension) M⊢

------------------------------------------------------------------------
-- Exact transport when the regular injection is pointwise identity
------------------------------------------------------------------------

renameᵗ-pointwise-id : ∀ {Δ} {ρ : Δ ⇒ʳ Δ} (A : Ty Δ)
  → (∀ X → ρ X ≡ X)
  → renameᵗ ρ A ≡ A
renameᵗ-pointwise-id A eq =
  trans (renameᵗ-cong A eq) (renameᵗ-id A)

renameᶿ-pointwise-id : ∀ {Θ Δ} {φ : TyVar Θ → TyVar Θ}
  → (∀ a → φ a ≡ a)
  → (M : Term Θ Δ)
  → renameᶿ φ M ≡ M
renameᶿ-pointwise-id eq (` x) = refl
renameᶿ-pointwise-id eq (ƛ A ˙ M) =
  cong (ƛ A ˙_) (renameᶿ-pointwise-id eq M)
renameᶿ-pointwise-id eq (L · M) =
  cong₂ _·_ (renameᶿ-pointwise-id eq L)
    (renameᶿ-pointwise-id eq M)
renameᶿ-pointwise-id eq (Λ M) =
  cong Λ_ (renameᶿ-pointwise-id eq M)
renameᶿ-pointwise-id eq (L ⦂∀ C [ A ]) =
  cong (λ N → N ⦂∀ C [ A ]) (renameᶿ-pointwise-id eq L)
renameᶿ-pointwise-id eq ($ κ) = refl
renameᶿ-pointwise-id eq (L ⊕[ op ] M) =
  cong₂ (λ N P → N ⊕[ op ] P) (renameᶿ-pointwise-id eq L)
    (renameᶿ-pointwise-id eq M)
renameᶿ-pointwise-id eq (M ⟨ c ⟩) =
  cong (_⟨ c ⟩) (renameᶿ-pointwise-id eq M)
renameᶿ-pointwise-id eq (M ↑[ Y ≔ a ] c) =
  cong₂ (λ N b → N ↑[ Y ≔ b ] c)
    (renameᶿ-pointwise-id eq M) (eq a)
renameᶿ-pointwise-id eq (M ↓[ Y ≔ a ] c) =
  cong₂ (λ N b → N ↓[ Y ≔ b ] c)
    (renameᶿ-pointwise-id eq M) (eq a)
renameᶿ-pointwise-id eq (ν[ A ] M) =
  cong (ν[ A ]_) (renameᶿ-pointwise-id ext-eq M)
  where
  ext-eq : ∀ a → extᵗ _ a ≡ a
  ext-eq zero = refl
  ext-eq (suc a) = cong suc (eq a)
renameᶿ-pointwise-id eq blame = refl

keep-pointwise-id : ∀ {Δ} {ρ : Δ ↪ᵗ Δ}
  → (∀ X → toRenameᵗ ρ X ≡ X)
  → ∀ X → toRenameᵗ (keep ρ) X ≡ X
keep-pointwise-id eq zero = refl
keep-pointwise-id eq (suc X) = cong suc (eq X)

insert-here-pointwise-id : ∀ {Δ} {ρ : Δ ↪ᵗ Δ}
    (Y : TyVar (suc Δ))
  → (∀ X → toRenameᵗ ρ X ≡ X)
  → toRenameᵗ (insert↪ᵗ ρ Y) Y ≡ Y
insert-here-pointwise-id {ρ = ρ} zero eq = refl
insert-here-pointwise-id {ρ = keep ρ} (suc Y) eq =
  cong suc (insert-here-pointwise-id Y (λ X → fin-suc-injective (eq (suc X))))
insert-here-pointwise-id {ρ = skip ρ} (suc Y) eq =
  ⊥-elim (zero≢suc (sym (eq zero)))
  where
  zero≢suc : ∀ {n} {X : TyVar n} → zero ≢ suc X
  zero≢suc ()

insert-pointwise-id : ∀ {Δ} {ρ : Δ ↪ᵗ Δ}
    (Y : TyVar (suc Δ))
  → (∀ X → toRenameᵗ ρ X ≡ X)
  → ∀ X → toRenameᵗ (insert↪ᵗ ρ Y) X ≡ X
insert-pointwise-id {ρ = ρ} Y eq X with Y ≟ X
insert-pointwise-id {ρ = ρ} Y eq .Y | yes refl =
  insert-here-pointwise-id Y eq
insert-pointwise-id {ρ = ρ} Y eq X | no Y≢X =
  trans (cong (toRenameᵗ (insert↪ᵗ ρ Y))
      (sym (punchIn-punchOut Y X Y≢X)))
    (trans (insert-punchIn ρ Y (punchOut Y X Y≢X))
      (trans (cong₂ punchIn
          (insert-here-pointwise-id Y eq)
          (eq (punchOut Y X Y≢X)))
        (punchIn-punchOut Y X Y≢X)))

delete-pointwise-id : ∀ {Δ} {ρ : suc Δ ↪ᵗ suc Δ}
    (Y : TyVar (suc Δ))
  → (∀ X → toRenameᵗ ρ X ≡ X)
  → ∀ X → toRenameᵗ (delete↪ᵗ ρ Y) X ≡ X
delete-pointwise-id {ρ = ρ} Y eq X =
  punchIn-injectiveᵗ Y
    (trans (sym (inserted-image))
      (trans (sym (delete-punchIn ρ Y X))
        (eq (punchIn Y X))))
  where
  inserted-image : punchIn (toRenameᵗ ρ Y)
      (toRenameᵗ (delete↪ᵗ ρ Y) X)
    ≡ punchIn Y (toRenameᵗ (delete↪ᵗ ρ Y) X)
  inserted-image = cong
    (λ Z → punchIn Z (toRenameᵗ (delete↪ᵗ ρ Y) X)) (eq Y)

⊢transport-id : ∀ {Θ Θ′ Δ σ σ′} {ρ : Δ ↪ᵗ Δ}
    {φ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ σ′} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → (target : TypingTarget ρ φ Ψ Φ)
  → (idρ : ∀ X → toRenameᵗ ρ X ≡ X)
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Φ ∣ Γ ⊢ renameᶿ φ M ⦂ A
⊢transport-id target idρ (⊢` x∈) = ⊢` x∈
⊢transport-id target idρ (⊢ƛ M⊢) =
  ⊢ƛ (⊢transport-id target idρ M⊢)
⊢transport-id target idρ (⊢· L⊢ M⊢) =
  ⊢· (⊢transport-id target idρ L⊢)
    (⊢transport-id target idρ M⊢)
⊢transport-id target idρ (⊢Λ M⊢) =
  ⊢Λ (⊢transport-id (typing-target-typ target)
    (keep-pointwise-id idρ) M⊢)
⊢transport-id target idρ (⊢⦂∀ L⊢) =
  ⊢⦂∀ (⊢transport-id target idρ L⊢)
⊢transport-id target idρ (⊢$ κ) = ⊢$ κ
⊢transport-id target idρ (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢transport-id target idρ L⊢)
    (⊢transport-id target idρ M⊢)
⊢transport-id target idρ (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢transport-id target idρ M⊢) c
⊢transport-id {ρ = ρ} {φ = φ} {Ψ = Ψ} {Φ = Φ}
    target idρ (⊢ν {A = A} M⊢) =
  ⊢ν (⊢transport-id ν-target idρ M⊢)
  where
  ν-target = subst≡
    (λ B → TypingTarget ρ (extᵗ φ) (Ψ ,:= A) (Φ ,:= B))
    (renameᵗ-pointwise-id A idρ)
    (typing-target-ν {ρ = ρ} {A = A} target)
⊢transport-id {ρ = ρ} {φ = φ} {Φ = Φ} target idρ
    (⊢reveal {C = C} {Y = Y} {α = α} {fresh = fresh}
      α-eq c⊢ M⊢) =
  ⊢reveal target-rep c⊢ body-exact
  where
  position = insert-here-pointwise-id Y idρ
  target-fresh = fresh-TypingTarget target fresh
  target-rep = trans (rep?-TypingTarget target α α-eq)
    (cong just (renameᵗ-pointwise-id C idρ))
  body⊢ = ⊢transport-id (typingTarget-begin target)
    (insert-pointwise-id Y idρ) M⊢
  body-exact = subst≡
    (λ Z → Φ ,begin[ Z ≔ φ α ]⟨ target-fresh ⟩ ∣ []
      ⊢ renameᶿ φ _ ⦂ _)
    position body⊢
⊢transport-id {ρ = ρ} {φ = φ} {Φ = Φ} target idρ
    (⊢conceal {C = C} {Y = Y} {α = α}
      slot-eq α-eq c⊢ M⊢) =
  ⊢conceal target-slot target-rep c⊢ body-exact
  where
  position = idρ Y
  ended-target = typing-target-end target
  target-slot-mapped = slot-forward-TypingTarget target slot-eq
  target-slot = trans
    (cong (Vec.lookup (slotsOf Φ)) (sym position))
    target-slot-mapped
  target-rep-mapped = trans (rep?-TypingTarget ended-target α α-eq)
    (cong just (renameᵗ-pointwise-id C (delete-pointwise-id Y idρ)))
  target-rep = subst≡
    (λ Z → rep? (Φ ,end[ Z ]) (φ α) ≡ just C)
    position target-rep-mapped
  body⊢ = ⊢transport-id ended-target (delete-pointwise-id Y idρ) M⊢
  body-exact = subst≡
    (λ Z → Φ ,end[ Z ] ∣ [] ⊢ renameᶿ φ _ ⦂ _)
    position body⊢
⊢transport-id target idρ ⊢blame = ⊢blame

⊢≼-id : ∀ {Θ Θ′ Δ σ σ′ k} {ρ : Δ ↪ᵗ Δ}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ σ′}
    {M : Term Θ Δ} {A : Ty Δ}
  → (extension : Ψ ≼[ k , ρ ] Φ)
  → (∀ X → toRenameᵗ ρ X ≡ X)
  → Ψ ∣ [] ⊢ M ⦂ A
  → Φ ∣ [] ⊢ renameᶿ (shiftAlong extension) M ⦂ A
⊢≼-id extension idρ M⊢ =
  ⊢transport-id (balanced-target extension) idρ M⊢

fresh-after-end : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {Y : TyVar (suc Δ)} {a : TyVar Θ}
  → Vec.lookup σ Y ≡ just a
  → a ∉ᵛ removeᵛ Y σ
fresh-after-end {Ψ = Ψ} {Y = Y} slot-eq X ended-eq =
  punchIn≢ Y X (aliases-unique Ψ slot-eq source-eq)
  where
  source-eq = trans
    (sym (lookup-remove-punch Y (slotsOf Ψ) X)) ended-eq

fresh-zero-after-ν : ∀ {Θ Δ} {σ : Vec.Vec (Maybe (TyVar Θ)) Δ}
  → zero ∉ᵛ mapᵛ (mapMaybe suc) σ
fresh-zero-after-ν {σ = Vec.[]} ()
fresh-zero-after-ν {σ = nothing Vec.∷ σ} zero ()
fresh-zero-after-ν {σ = just a Vec.∷ σ} zero ()
fresh-zero-after-ν {σ = head Vec.∷ σ} (suc Y) eq =
  fresh-zero-after-ν {σ = σ} Y eq

fresh-insert-other : ∀ {Θ Δ σ} {a b : TyVar Θ}
    (Y : TyVar (suc Δ))
  → a ≢ b
  → a ∉ᵛ σ
  → a ∉ᵛ insertᵛ Y (just b) σ
fresh-insert-other Y a≢b fresh z eq with Y ≟ z
fresh-insert-other Y a≢b fresh .Y eq | yes refl =
  a≢b (just-injective (trans (sym eq)
    (lookup-insert-here Y (just _) _)))
fresh-insert-other Y a≢b fresh z eq | no Y≢z =
  fresh (punchOut Y z Y≢z)
    (trans (sym (lookup-insert-other Y z (just _) _ Y≢z)) eq)

bracket-injection-id : ∀ {Δ} (Y : TyVar (suc Δ)) X
  → toRenameᵗ (id↪ᵗ ⨟↪ᵗ delete↪ᵗ id↪ᵗ Y) X ≡ X
bracket-injection-id Y X =
  trans (toRename-compose id↪ᵗ (delete↪ᵗ id↪ᵗ Y) X)
    (trans (cong (toRenameᵗ (delete↪ᵗ id↪ᵗ Y))
        (toRename-id-eq X))
      (delete-pointwise-id Y toRename-id-eq X))

reenter-middle-id : ∀ {Δ} (Y : TyVar (suc Δ)) X
  → toRenameᵗ (delete↪ᵗ id↪ᵗ Y ⨟↪ᵗ id↪ᵗ) X ≡ X
reenter-middle-id Y X =
  trans (toRename-compose (delete↪ᵗ id↪ᵗ Y) id↪ᵗ X)
    (trans (toRename-id-eq _)
      (delete-pointwise-id Y toRename-id-eq X))

reenter-injection-id : ∀ {Δ} (Y : TyVar (suc Δ)) X
  → toRenameᵗ
      (insert↪ᵗ (delete↪ᵗ id↪ᵗ Y ⨟↪ᵗ id↪ᵗ) Y) X ≡ X
reenter-injection-id Y =
  insert-pointwise-id Y (reenter-middle-id Y)

⊢shiftᶿ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Ψ ,:= B ∣ Γ ⊢ shiftᶿ M ⦂ A
⊢shiftᶿ M⊢ = ⊢transport-id
  (balanced-target (≼-ν ≼-refl)) toRename-id-eq M⊢

⊢bracket : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {M : Term Θ Δ} {A : Ty Δ} {Y : TyVar (suc Δ)}
    {a : TyVar Θ} (fresh : a ∉ᵛ σ)
  → Ψ ∣ [] ⊢ M ⦂ A
  → Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩ ,end[ Y ] ∣ [] ⊢ M ⦂ A
⊢bracket {Ψ = Ψ} {M = M} {A = A} {Y = Y} {a = a} fresh M⊢ =
  subst≡ (λ N → Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩ ,end[ Y ]
      ∣ [] ⊢ N ⦂ A)
    (renameᶿ-pointwise-id (λ q → refl) M) position-typed
  where
  extension = ≼-begin-end ≼-refl ≼-refl
  mapped = toRenameᵗ id↪ᵗ Y
  typed = ⊢≼-id extension (bracket-injection-id Y) M⊢
  position-typed = subst≡
    (λ Z → Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩ ,end[ Z ]
      ∣ [] ⊢ renameᶿ (shiftAlong extension) M ⦂ A)
    (toRename-id-eq Y) typed

shifted-zero-eq : ∀ {Θ} {a b : TyVar Θ}
  → Shifted zero a b
  → a ≡ b
shifted-zero-eq shifted-zero = refl

rep?-bracket : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {Y : TyVar (suc Δ)} {a q : TyVar Θ} {A : Ty Δ}
    (fresh : a ∉ᵛ σ)
  → rep? Ψ q ≡ just A
  → rep? (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩ ,end[ Y ]) q ≡ just A
rep?-bracket {Ψ = Ψ} {Y = Y} {a = a} {q = q} {A = A} fresh eq =
  subst≡
    (λ Z → rep? (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩ ,end[ Z ]) q ≡ just A)
    (toRename-id-eq Y) anchor-typed
  where
  target = Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩
    ,end[ toRenameᵗ id↪ᵗ Y ]
  extension : Ψ ≼[ zero , id↪ᵗ ⨟↪ᵗ delete↪ᵗ id↪ᵗ Y ] target
  extension = ≼-begin-end ≼-refl ≼-refl
  anchor-id : shiftAlong extension q ≡ q
  anchor-id = sym (shifted-zero-eq
    (shiftAlong-shifted extension q))
  transported : rep? target (shiftAlong extension q) ≡ just A
  transported = trans (rep?-≼ extension {a = q} {A = A} eq)
    (cong just (renameᵗ-pointwise-id A (bracket-injection-id Y)))
  anchor-typed = subst≡
    (λ b → rep? target b ≡ just A) anchor-id transported

------------------------------------------------------------------------
-- Erasing an adjacent balanced bracket
------------------------------------------------------------------------

-- An adjacent begin/end pair has no observable effect on representation
-- lookup.  `UnbracketTarget` closes that one erasure under identical
-- telescope suffixes, which is exactly what typing induction needs.
remove-insert-here : ∀ {n} {X : Set} (Y : TyVar (suc n))
    (value : X) (values : Vec.Vec X n)
  → removeᵛ Y (insertᵛ Y value values) ≡ values
remove-insert-here zero value values = refl
remove-insert-here (suc Y) value (head Vec.∷ values) =
  cong (head Vec.∷_) (remove-insert-here Y value values)

data UnbracketTarget : ∀ {Θ Δ σ τ}
    → TyEnv Θ Δ σ → TyEnv Θ Δ τ → Set where
  unbracket-base : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {Y : TyVar (suc Δ)} {a : TyVar Θ} {fresh : a ∉ᵛ σ}
    → UnbracketTarget
        (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩ ,end[ Y ]) Ψ

  unbracket-fresh-before-begin : ∀ {Θ Δ σ}
      {Ψ : TyEnv Θ Δ σ} {X : TyVar (suc Δ)} {a b : TyVar Θ}
      {fresh-a : a ∉ᵛ σ} {fresh-b : b ∉ᵛ σ} {a≢b : a ≢ b}
    → UnbracketTarget
        (Ψ ,begin[ X ≔ a ]⟨ fresh-a ⟩)
        (Ψ ,begin[ zero ≔ b ]⟨ fresh-b ⟩
          ,begin[ suc X ≔ a
            ]⟨ fresh-insert-other zero a≢b fresh-a ⟩
          ,end[ zero ])

  unbracket-begin : ∀ {Θ Δ σ τ}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ τ}
      {Y : TyVar (suc Δ)} {a : TyVar Θ}
      {fresh : a ∉ᵛ σ} {fresh′ : a ∉ᵛ τ}
    → UnbracketTarget Ψ Φ
    → UnbracketTarget
        (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩)
        (Φ ,begin[ Y ≔ a ]⟨ fresh′ ⟩)

  unbracket-typ : ∀ {Θ Δ σ τ}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ τ}
    → UnbracketTarget Ψ Φ
    → UnbracketTarget (Ψ ,typ) (Φ ,typ)

  unbracket-ν : ∀ {Θ Δ σ τ}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ Δ τ} {A : Ty Δ}
    → UnbracketTarget Ψ Φ
    → UnbracketTarget (Ψ ,:= A) (Φ ,:= A)

  unbracket-end : ∀ {Θ Δ σ τ}
      {Ψ : TyEnv Θ (suc Δ) σ} {Φ : TyEnv Θ (suc Δ) τ}
      {Y : TyVar (suc Δ)}
    → UnbracketTarget Ψ Φ
    → UnbracketTarget (Ψ ,end[ Y ]) (Φ ,end[ Y ])

unbracket-slots : ∀ {Θ Δ σ τ}
    {left : TyEnv Θ Δ σ} {right : TyEnv Θ Δ τ}
  → UnbracketTarget left right
  → σ ≡ τ
unbracket-slots (unbracket-base {Y = Y} {a = a}) =
  remove-insert-here Y (just a) _
unbracket-slots unbracket-fresh-before-begin = refl
unbracket-slots (unbracket-begin same) =
  cong (insertᵛ _ (just _)) (unbracket-slots same)
unbracket-slots (unbracket-typ same) =
  cong (insertᵛ zero nothing) (unbracket-slots same)
unbracket-slots (unbracket-ν same) =
  cong (mapᵛ (mapMaybe suc)) (unbracket-slots same)
unbracket-slots (unbracket-end {Y = Y} same) =
  cong (removeᵛ Y) (unbracket-slots same)

unbracket-fresh : ∀ {Θ Δ σ τ}
    {left : TyEnv Θ Δ σ} {right : TyEnv Θ Δ τ} {a : TyVar Θ}
  → UnbracketTarget left right
  → a ∉ᵛ σ
  → a ∉ᵛ τ
unbracket-fresh same fresh
    rewrite sym (unbracket-slots same) = fresh

unbracket-slot : ∀ {Θ Δ σ τ}
    {left : TyEnv Θ Δ σ} {right : TyEnv Θ Δ τ}
    (same : UnbracketTarget left right) {Y a}
  → Vec.lookup σ Y ≡ just a
  → Vec.lookup τ Y ≡ just a
unbracket-slot same slot-eq rewrite sym (unbracket-slots same) = slot-eq

repoint?-birth-cong≡ : ∀ {Θ₀ Θ Δ₀ Δ Δout}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : Vec.Vec (Maybe (TyVar Θ)) Δ)
    (left : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (right : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
  → left ≡ right
  → (anchor-map : TyVar (suc Θ₀) → TyVar Θ)
  → (route : TyVar Δ₀ → Maybe (TyVar Δout))
  → (live-ren : TyVar Δ → TyVar Δout) (A : Ty Δ₀)
  → repoint? resolve target left anchor-map route live-ren A
    ≡ repoint? resolve target right anchor-map route live-ren A
repoint?-birth-cong≡ resolve target left .left refl anchor-map route
    live-ren A = refl

punch-zero-exchange : ∀ {Δ} (X : TyVar (suc Δ)) (Y : TyVar Δ)
  → punchIn zero (punchIn X Y)
    ≡ punchIn (suc X) (punchIn zero Y)
punch-zero-exchange X zero = refl
punch-zero-exchange X (suc Y) = refl

scanRep?-unbracket : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀ τ₀}
    (resolve : TyVar Θ → Maybe (Ty Δ))
    (target : TyEnv Θ Δ σ)
    {left : TyEnv Θ₀ Δ₀ σ₀} {right : TyEnv Θ₀ Δ₀ τ₀}
    (same : UnbracketTarget left right)
    (anchor-map : TyVar Θ₀ → TyVar Θ)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → scanRep? resolve target left anchor-map route a
    ≡ scanRep? resolve target right anchor-map route a
scanRep?-unbracket resolve target
    (unbracket-base {Ψ = Ψ} {Y = Y}) anchor-map route a =
  scanRep?-route-cong resolve target Ψ anchor-map
    (λ X → route-end Y route (punchIn Y X)) route a
    (route-end-punchIn Y route)
scanRep?-unbracket resolve target
    (unbracket-fresh-before-begin {Ψ = Ψ} {X = X})
    anchor-map route a =
  scanRep?-route-cong resolve target Ψ anchor-map
    (λ Y → route (punchIn X Y))
    (λ Y → route-end zero route
      (punchIn (suc X) (punchIn zero Y))) a route-eq
  where
  route-eq : ∀ Y → route (punchIn X Y)
    ≡ route-end zero route (punchIn (suc X) (punchIn zero Y))
  route-eq Y = sym
    (trans (cong (route-end zero route) (sym (punch-zero-exchange X Y)))
      (route-end-punchIn zero route (punchIn X Y)))
scanRep?-unbracket resolve target (unbracket-begin same)
    anchor-map route a =
  scanRep?-unbracket resolve target same anchor-map
    (λ X → route (punchIn _ X)) a
scanRep?-unbracket resolve target (unbracket-typ same)
    anchor-map route a =
  scanRep?-unbracket resolve target same anchor-map
    (λ X → route (suc X)) a
scanRep?-unbracket resolve target
    (unbracket-ν {Ψ = left} {Φ = right} {A = A} same)
    anchor-map route zero =
  repoint?-birth-cong≡ resolve (slotsOf target)
    (slotsOf left) (slotsOf right) (unbracket-slots same)
    anchor-map route (λ X → X) A
scanRep?-unbracket resolve target (unbracket-ν same)
    anchor-map route (suc a) =
  scanRep?-unbracket resolve target same
    (λ q → anchor-map (suc q)) route a
scanRep?-unbracket resolve target (unbracket-end {Y = Y} same)
    anchor-map route a =
  scanRep?-unbracket resolve target same anchor-map
    (route-end Y route) a

repFuel?-unbracket : ∀ fuel {Θ Δ σ τ}
    {left : TyEnv Θ Δ σ} {right : TyEnv Θ Δ τ}
  → UnbracketTarget left right
  → ∀ a → repFuel? fuel left a ≡ repFuel? fuel right a
repFuel?-unbracket zero same a = refl
repFuel?-unbracket (suc fuel) {left = left} {right = right} same a =
  trans (scanRep?-resolve-cong left left (λ q → q) (λ X → just X) a
      (repFuel?-unbracket fuel same))
    (trans (scanRep?-target-cong≡ (repFuel? fuel right)
        left right (unbracket-slots same) left
        (λ q → q) (λ X → just X) a)
      (scanRep?-unbracket (repFuel? fuel right) right same
        (λ q → q) (λ X → just X) a))

rep?-unbracket : ∀ {Θ Δ σ τ}
    {left : TyEnv Θ Δ σ} {right : TyEnv Θ Δ τ}
  → UnbracketTarget left right
  → ∀ a → rep? left a ≡ rep? right a
rep?-unbracket {Θ = Θ} same a =
  repFuel?-unbracket (Θ ∸ toℕ a) same a

⊢unbracket-target : ∀ {Θ Δ σ τ}
    {left : TyEnv Θ Δ σ} {right : TyEnv Θ Δ τ}
    {Γ : TermCtx Δ} {M : Term Θ Δ} {A : Ty Δ}
  → UnbracketTarget left right
  → left ∣ Γ ⊢ M ⦂ A
  → right ∣ Γ ⊢ M ⦂ A
⊢unbracket-target same (⊢` x∈) = ⊢` x∈
⊢unbracket-target same (⊢ƛ M⊢) =
  ⊢ƛ (⊢unbracket-target same M⊢)
⊢unbracket-target same (⊢· L⊢ M⊢) =
  ⊢· (⊢unbracket-target same L⊢) (⊢unbracket-target same M⊢)
⊢unbracket-target same (⊢Λ M⊢) =
  ⊢Λ (⊢unbracket-target (unbracket-typ same) M⊢)
⊢unbracket-target same (⊢⦂∀ M⊢) =
  ⊢⦂∀ (⊢unbracket-target same M⊢)
⊢unbracket-target same (⊢$ κ) = ⊢$ κ
⊢unbracket-target same (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢unbracket-target same L⊢)
    (⊢unbracket-target same M⊢)
⊢unbracket-target same (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢unbracket-target same M⊢) c
⊢unbracket-target same (⊢ν M⊢) =
  ⊢ν (⊢unbracket-target (unbracket-ν same) M⊢)
⊢unbracket-target same
    (⊢reveal {α = α} {fresh = fresh} α-eq c⊢ M⊢) =
  ⊢reveal (trans (sym (rep?-unbracket same α)) α-eq) c⊢
    (⊢unbracket-target
      (unbracket-begin {fresh′ = unbracket-fresh same fresh} same) M⊢)
⊢unbracket-target same
    (⊢conceal {Y = Y} {α = α} slot-eq α-eq c⊢ M⊢) =
  ⊢conceal (unbracket-slot same slot-eq)
    (trans (sym (rep?-unbracket (unbracket-end {Y = Y} same) α)) α-eq)
    c⊢ (⊢unbracket-target (unbracket-end {Y = Y} same) M⊢)
⊢unbracket-target same ⊢blame = ⊢blame

⊢unbracket : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {Γ : TermCtx Δ} {M : Term Θ Δ} {A : Ty Δ}
    {Y : TyVar (suc Δ)} {a : TyVar Θ} {fresh : a ∉ᵛ σ}
  → Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩ ,end[ Y ] ∣ Γ ⊢ M ⦂ A
  → Ψ ∣ Γ ⊢ M ⦂ A
⊢unbracket = ⊢unbracket-target unbracket-base

reenter-extension : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {Y : TyVar (suc Δ)} {a : TyVar Θ}
    (slot-eq : Vec.lookup σ Y ≡ just a)
  → Ψ ≼[ zero ,
      insert↪ᵗ (delete↪ᵗ id↪ᵗ Y ⨟↪ᵗ id↪ᵗ) Y ]
      (Ψ ,end[ Y ] ,begin[
        toRenameᵗ
          (insert↪ᵗ (delete↪ᵗ id↪ᵗ Y ⨟↪ᵗ id↪ᵗ) Y) Y ≔ a
      ]⟨ fresh-after-end {Ψ = Ψ} {Y = Y} slot-eq ⟩)
reenter-extension {Ψ = Ψ} {Y = Y} slot-eq =
  ≼-end-begin slot-eq ≼-refl region shifted-zero
  where
  mapped = toRenameᵗ id↪ᵗ Y
  region : (Ψ ,end[ mapped ]) ≼[ zero , id↪ᵗ ] (Ψ ,end[ Y ])
  region = subst≡
    (λ Z → (Ψ ,end[ mapped ]) ≼[ zero , id↪ᵗ ] (Ψ ,end[ Z ]))
    (toRename-id-eq Y) ≼-refl

reenter-anchor-id : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {Y : TyVar (suc Δ)} {a : TyVar Θ}
    (slot-eq : Vec.lookup σ Y ≡ just a) (q : TyVar Θ)
  → shiftAlong (reenter-extension {Ψ = Ψ} {Y = Y} slot-eq) q ≡ q
reenter-anchor-id {Ψ = Ψ} {Y = Y} slot-eq q =
  sym (shifted-zero-eq
    (shiftAlong-shifted (reenter-extension {Ψ = Ψ} {Y = Y} slot-eq) q))

⊢reenter : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
    {M : Term Θ (suc Δ)} {A : Ty (suc Δ)}
    {Y : TyVar (suc Δ)} {a : TyVar Θ}
    (slot-eq : Vec.lookup σ Y ≡ just a)
  → Ψ ∣ [] ⊢ M ⦂ A
  → Ψ ,end[ Y ] ,begin[ Y ≔ a
      ]⟨ fresh-after-end {Ψ = Ψ} {Y = Y} slot-eq ⟩
      ∣ [] ⊢ M ⦂ A
⊢reenter {Ψ = Ψ} {M = M} {A = A} {Y = Y} {a = a} slot-eq M⊢ =
  subst≡ (λ N → Ψ ,end[ Y ] ,begin[ Y ≔ a
      ]⟨ fresh-after-end {Ψ = Ψ} {Y = Y} slot-eq ⟩
      ∣ [] ⊢ N ⦂ A)
    (renameᶿ-pointwise-id
      (reenter-anchor-id {Ψ = Ψ} {Y = Y} slot-eq) M)
    (subst≡
      (λ Z → Ψ ,end[ Y ] ,begin[ Z ≔ a
          ]⟨ fresh-after-end {Ψ = Ψ} {Y = Y} slot-eq ⟩
        ∣ [] ⊢ renameᶿ
          (shiftAlong (reenter-extension {Ψ = Ψ} {Y = Y} slot-eq)) M ⦂ A)
      (reenter-injection-id Y Y)
      (⊢≼-id
        (reenter-extension {Ψ = Ψ} {Y = Y} slot-eq)
        (reenter-injection-id Y) M⊢))

------------------------------------------------------------------------
-- Replacing one lexical slot by a freshly allocated crossing
------------------------------------------------------------------------

-- `allocSlots` is the slot-level invariant of lexical allocation.  Every
-- ordinary crossing keeps its anchor through `φ`; the distinguished lexical
-- position becomes the one fresh target anchor `b`.
allocSlots : ∀ {Θ Θ′ Δ}
  → (TyVar Θ → TyVar Θ′)
  → TyVar Δ → TyVar Θ′
  → Vec.Vec (Maybe (TyVar Θ)) Δ
  → Vec.Vec (Maybe (TyVar Θ′)) Δ
allocSlots φ zero b (entry Vec.∷ slots) =
  just b Vec.∷ mapᵛ (mapMaybe φ) slots
allocSlots φ (suc P) b (entry Vec.∷ slots) =
  mapMaybe φ entry Vec.∷ allocSlots φ P b slots

allocSlots-here : ∀ {Θ Θ′ Δ} (φ : TyVar Θ → TyVar Θ′)
    (P : TyVar Δ) b (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → Vec.lookup (allocSlots φ P b slots) P ≡ just b
allocSlots-here φ zero b (entry Vec.∷ slots) = refl
allocSlots-here φ (suc P) b (entry Vec.∷ slots) =
  allocSlots-here φ P b slots

allocSlots-other : ∀ {Θ Θ′ Δ} (φ : TyVar Θ → TyVar Θ′)
    (P X : TyVar Δ) b (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → P ≢ X
  → Vec.lookup (allocSlots φ P b slots) X
    ≡ mapMaybe φ (Vec.lookup slots X)
allocSlots-other φ zero zero b slots neq = ⊥-elim (neq refl)
allocSlots-other φ zero (suc X) b (entry Vec.∷ slots) neq =
  lookup-mapᵛ (mapMaybe φ) slots X
allocSlots-other φ (suc P) zero b (entry Vec.∷ slots) neq = refl
allocSlots-other φ (suc P) (suc X) b (entry Vec.∷ slots) neq =
  allocSlots-other φ P X b slots (λ eq → neq (cong suc eq))

mapᵛ-insert : ∀ {n} {A B : Set} (f : A → B)
    (Y : TyVar (suc n)) (entry : A) (values : Vec.Vec A n)
  → mapᵛ f (insertᵛ Y entry values)
    ≡ insertᵛ Y (f entry) (mapᵛ f values)
mapᵛ-insert f zero entry values = refl
mapᵛ-insert f (suc Y) entry (head Vec.∷ values) =
  cong (f head Vec.∷_) (mapᵛ-insert f Y entry values)

allocSlots-insert : ∀ {Θ Θ′ Δ} (φ : TyVar Θ → TyVar Θ′)
    (Y : TyVar (suc Δ)) (P : TyVar Δ) b entry
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → allocSlots φ (punchIn Y P) b (insertᵛ Y entry slots)
    ≡ insertᵛ Y (mapMaybe φ entry) (allocSlots φ P b slots)
allocSlots-insert φ zero P b entry slots = refl
allocSlots-insert φ (suc Y) zero b entry (head Vec.∷ slots) =
  cong (just b Vec.∷_) (mapᵛ-insert (mapMaybe φ) Y entry slots)
allocSlots-insert φ (suc Y) (suc P) b entry (head Vec.∷ slots) =
  cong (mapMaybe φ head Vec.∷_)
    (allocSlots-insert φ Y P b entry slots)

map-anchor-ext : ∀ {Θ Θ′ Δ} (φ : TyVar Θ → TyVar Θ′)
    (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → mapᵛ (mapMaybe (extᵗ φ)) (mapᵛ (mapMaybe suc) slots)
    ≡ mapᵛ (mapMaybe suc) (mapᵛ (mapMaybe φ) slots)
map-anchor-ext φ Vec.[] = refl
map-anchor-ext φ (nothing Vec.∷ slots) =
  cong (nothing Vec.∷_) (map-anchor-ext φ slots)
map-anchor-ext φ (just a Vec.∷ slots) =
  cong (just (suc (φ a)) Vec.∷_) (map-anchor-ext φ slots)

allocSlots-ν : ∀ {Θ Θ′ Δ} (φ : TyVar Θ → TyVar Θ′)
    (P : TyVar Δ) b (slots : Vec.Vec (Maybe (TyVar Θ)) Δ)
  → allocSlots (extᵗ φ) P (suc b)
      (mapᵛ (mapMaybe suc) slots)
    ≡ mapᵛ (mapMaybe suc) (allocSlots φ P b slots)
allocSlots-ν φ zero b (nothing Vec.∷ slots) =
  cong (just (suc b) Vec.∷_) (map-anchor-ext φ slots)
allocSlots-ν φ zero b (just a Vec.∷ slots) =
  cong (just (suc b) Vec.∷_) (map-anchor-ext φ slots)
allocSlots-ν φ (suc P) b (nothing Vec.∷ slots) =
  cong (nothing Vec.∷_) (allocSlots-ν φ P b slots)
allocSlots-ν φ (suc P) b (just a Vec.∷ slots) =
  cong (just (suc (φ a)) Vec.∷_) (allocSlots-ν φ P b slots)

mapᵛ-remove : ∀ {n} {A B : Set} (f : A → B)
    (Y : TyVar (suc n)) (values : Vec.Vec A (suc n))
  → mapᵛ f (removeᵛ Y values) ≡ removeᵛ Y (mapᵛ f values)
mapᵛ-remove f zero (head Vec.∷ values) = refl
mapᵛ-remove {n = suc n} f (suc Y) (head Vec.∷ values) =
  cong (f head Vec.∷_) (mapᵛ-remove f Y values)

allocSlots-remove : ∀ {Θ Θ′ Δ} (φ : TyVar Θ → TyVar Θ′)
    (Y P : TyVar (suc Δ)) b
    (slots : Vec.Vec (Maybe (TyVar Θ)) (suc Δ))
    (neq : Y ≢ P)
  → allocSlots φ (punchOut Y P neq) b (removeᵛ Y slots)
    ≡ removeᵛ Y (allocSlots φ P b slots)
allocSlots-remove φ zero zero b slots neq = ⊥-elim (neq refl)
allocSlots-remove φ zero (suc P) b (head Vec.∷ slots) neq = refl
allocSlots-remove {Δ = suc Δ} φ (suc Y) zero b
    (head Vec.∷ slots) neq =
  cong (just b Vec.∷_) (mapᵛ-remove (mapMaybe φ) Y slots)
allocSlots-remove {Δ = suc Δ} φ (suc Y) (suc P) b
    (head Vec.∷ slots) neq =
  cong (mapMaybe φ head Vec.∷_)
    (allocSlots-remove φ Y P b slots
      (λ eq → neq (cong suc eq)))

data AllocationTarget : ∀ {Θ Θ′ Δ σ τ}
    (φ : TyVar Θ → TyVar Θ′) (P : TyVar Δ) (b : TyVar Θ′)
    → TyEnv Θ Δ σ → TyEnv Θ′ Δ τ → Set where
  allocation-base : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {C : Ty Δ}
    → AllocationTarget suc zero zero (Ψ ,typ)
        ((Ψ ,:= C)
          ,begin[ zero ≔ zero ]⟨ fresh-zero-map-suc {slots = σ} ⟩)

  allocation-begin : ∀ {Θ Θ′ Δ σ τ}
      {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
      {Y : TyVar (suc Δ)} {a : TyVar Θ}
      {fresh : a ∉ᵛ σ} {fresh′ : φ a ∉ᵛ τ}
    → AllocationTarget φ P b Ψ Φ
    → AllocationTarget φ (punchIn Y P) b
        (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩)
        (Φ ,begin[ Y ≔ φ a ]⟨ fresh′ ⟩)

  allocation-typ : ∀ {Θ Θ′ Δ σ τ}
      {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
    → AllocationTarget φ P b Ψ Φ
    → AllocationTarget φ (suc P) b (Ψ ,typ) (Φ ,typ)

  allocation-ν : ∀ {Θ Θ′ Δ σ τ}
      {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ} {A : Ty Δ}
    → AllocationTarget φ P b Ψ Φ
    → AllocationTarget (extᵗ φ) P (suc b)
        (Ψ ,:= A) (Φ ,:= A)

  allocation-end : ∀ {Θ Θ′ Δ σ τ}
      {φ : TyVar Θ → TyVar Θ′}
      {P Y : TyVar (suc Δ)} {b : TyVar Θ′}
      {Ψ : TyEnv Θ (suc Δ) σ} {Φ : TyEnv Θ′ (suc Δ) τ}
    → (neq : Y ≢ P)
    → AllocationTarget φ P b Ψ Φ
    → AllocationTarget φ (punchOut Y P neq) b
        (Ψ ,end[ Y ]) (Φ ,end[ Y ])

allocation-slots : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
  → AllocationTarget φ P b Ψ Φ
  → τ ≡ allocSlots φ P b σ
allocation-slots allocation-base = refl
allocation-slots
    (allocation-begin {φ = φ} {P = P} {Y = Y} target)
    rewrite allocation-slots target =
  sym (allocSlots-insert φ Y P _ _ _)
allocation-slots (allocation-typ target)
    rewrite allocation-slots target = refl
allocation-slots (allocation-ν {φ = φ} {P = P} target)
    rewrite allocation-slots target = sym (allocSlots-ν φ P _ _)
allocation-slots
    (allocation-end {φ = φ} {P = P} {Y = Y} neq target)
    rewrite allocation-slots target =
  sym (allocSlots-remove φ Y P _ _ neq)

allocation-source-lexical : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
  → AllocationTarget φ P b Ψ Φ
  → Vec.lookup σ P ≡ nothing
allocation-source-lexical allocation-base = refl
allocation-source-lexical
    (allocation-begin {σ = σ} {P = P} {Y = Y} {a = a} target) =
  trans (lookup-insert-punch Y (just a) σ P)
    (allocation-source-lexical target)
allocation-source-lexical (allocation-typ target) =
  allocation-source-lexical target
allocation-source-lexical
    (allocation-ν {σ = σ} {P = P} target) =
  trans (lookup-mapᵛ (mapMaybe suc) σ P)
    (cong (mapMaybe suc) (allocation-source-lexical target))
allocation-source-lexical
    (allocation-end {σ = σ} {P = P} {Y = Y} neq target) =
  trans (lookup-remove-punch Y σ (punchOut Y P neq))
    (trans (cong (Vec.lookup σ)
        (punchIn-punchOut Y P neq))
      (allocation-source-lexical target))

AllocationTarget-anchor-injective : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
  → AllocationTarget φ P b Ψ Φ
  → ∀ {a q} → φ a ≡ φ q → a ≡ q
AllocationTarget-anchor-injective allocation-base = fin-suc-injective
AllocationTarget-anchor-injective (allocation-begin target) =
  AllocationTarget-anchor-injective target
AllocationTarget-anchor-injective (allocation-typ target) =
  AllocationTarget-anchor-injective target
AllocationTarget-anchor-injective (allocation-ν target) =
  extᵗ-injective′ (AllocationTarget-anchor-injective target)
AllocationTarget-anchor-injective (allocation-end neq target) =
  AllocationTarget-anchor-injective target

zero≢fin-suc : ∀ {n} {a : TyVar n} → zero ≢ suc a
zero≢fin-suc ()

nothing≢just : ∀ {A : Set} {x : A} → nothing ≢ just x
nothing≢just ()

allocation-extra-distinct : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
  → AllocationTarget φ P b Ψ Φ
  → ∀ a → b ≢ φ a
allocation-extra-distinct allocation-base a = zero≢fin-suc
allocation-extra-distinct (allocation-begin target) =
  allocation-extra-distinct target
allocation-extra-distinct (allocation-typ target) =
  allocation-extra-distinct target
allocation-extra-distinct (allocation-ν target) zero ()
allocation-extra-distinct (allocation-ν target) (suc a) eq =
  allocation-extra-distinct target a (fin-suc-injective eq)
allocation-extra-distinct (allocation-end neq target) =
  allocation-extra-distinct target

allocation-target-extra : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
  → (target : AllocationTarget φ P b Ψ Φ)
  → Vec.lookup τ P ≡ just b
allocation-target-extra {φ = φ} {P = P} {b = b} {Ψ = Ψ} target =
  trans (cong (λ slots → Vec.lookup slots P) (allocation-slots target))
    (allocSlots-here φ P b (slotsOf Ψ))

allocation-target-other : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P X : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
  → (target : AllocationTarget φ P b Ψ Φ)
  → P ≢ X
  → Vec.lookup τ X ≡ mapMaybe φ (Vec.lookup σ X)
allocation-target-other {φ = φ} {P = P} {X = X} {b = b}
    {Ψ = Ψ} target neq =
  trans (cong (λ slots → Vec.lookup slots X) (allocation-slots target))
    (allocSlots-other φ P X b (slotsOf Ψ) neq)

allocation-target-forward : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P X : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ} {a : TyVar Θ}
  → (target : AllocationTarget φ P b Ψ Φ)
  → Vec.lookup σ X ≡ just a
  → Vec.lookup τ X ≡ just (φ a)
allocation-target-forward {P = P} {X = X} target source-eq =
  trans (allocation-target-other target P≢X)
    (cong (mapMaybe _) source-eq)
  where
  P≢X : P ≢ X
  P≢X refl with trans (sym (allocation-source-lexical target)) source-eq
  P≢X refl | ()

allocation-target-backward : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P X : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ} {a : TyVar Θ}
  → (target : AllocationTarget φ P b Ψ Φ)
  → Vec.lookup τ X ≡ just (φ a)
  → Vec.lookup σ X ≡ just a
allocation-target-backward {φ = φ} {P = P} {X = X}
    {Ψ = Ψ} target target-eq with P ≟ X
allocation-target-backward {φ = φ} {P = P} {X = .P}
    target target-eq | yes refl =
  ⊥-elim (allocation-extra-distinct target _
    (just-injective
      (trans (sym (allocation-target-extra target)) target-eq)))
allocation-target-backward {φ = φ} {P = P} {X = X}
    {Ψ = Ψ} target target-eq | no P≢X
    with Vec.lookup (slotsOf Ψ) X in source-eq
allocation-target-backward target target-eq | no P≢X | nothing
    = ⊥-elim (nothing≢just
      (trans (sym (cong (mapMaybe _) source-eq))
        (trans (sym (allocation-target-other target P≢X)) target-eq)))
allocation-target-backward {φ = φ} target target-eq
    | no P≢X | just q =
  cong just (AllocationTarget-anchor-injective target
    (just-injective
      (trans (sym (cong (mapMaybe φ) source-eq))
        (trans (sym (allocation-target-other target P≢X)) target-eq))))

liveSlot?-AllocationTarget : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
  → (target : AllocationTarget φ P b Ψ Φ) (a : TyVar Θ)
  → liveSlot? τ (φ a) ≡ liveSlot? σ a
liveSlot?-AllocationTarget {Ψ = Ψ} {Φ = Φ} target a
    with liveSlot? (slotsOf Ψ) a in source-live
       | liveSlot? (slotsOf Φ) _ in target-live
liveSlot?-AllocationTarget {Ψ = Ψ} {Φ = Φ} target a
    | nothing | nothing = target-live
liveSlot?-AllocationTarget {Ψ = Ψ} {Φ = Φ} target a
    | nothing | just Y =
  ⊥-elim (nothing≢just
    (trans (sym source-live)
      (liveSlot?-complete (slotsOf Ψ) (aliases-unique Ψ) source-eq)))
  where
  source-eq = allocation-target-backward target
    (liveSlot?-sound (slotsOf Φ) _ Y target-live)
liveSlot?-AllocationTarget {Ψ = Ψ} {Φ = Φ} target a
    | just X | nothing =
  ⊥-elim (nothing≢just
    (trans (sym target-live)
      (liveSlot?-complete (slotsOf Φ) (aliases-unique Φ) target-eq)))
  where
  target-eq = allocation-target-forward target
    (liveSlot?-sound (slotsOf Ψ) _ X source-live)
liveSlot?-AllocationTarget {Ψ = Ψ} {Φ = Φ} target a
    | just X | just Y =
  trans target-live
    (cong just (sym (aliases-unique Φ target-X target-Y)))
  where
  target-X = allocation-target-forward target
    (liveSlot?-sound (slotsOf Ψ) _ X source-live)
  target-Y = liveSlot?-sound (slotsOf Φ) _ Y target-live

liveSlot?-AllocationTarget-extra : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
  → (target : AllocationTarget φ P b Ψ Φ)
  → liveSlot? τ b ≡ just P
liveSlot?-AllocationTarget-extra {Φ = Φ} target =
  liveSlot?-complete (slotsOf Φ) (aliases-unique Φ)
    (allocation-target-extra target)

aliasResult?-AllocationTarget : ∀ {Θ Θ′ Δ σ τ Δout}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
    (target : AllocationTarget φ P b Ψ Φ)
    (old : TyVar Θ → Maybe (Ty Δ))
    (new : TyVar Θ′ → Maybe (Ty Δ))
    (live-ren : TyVar Δ → TyVar Δout) (a : TyVar Θ)
  → (∀ q → new (φ q) ≡ old q)
  → aliasResult? new τ live-ren (φ a)
    ≡ aliasResult? old σ live-ren a
aliasResult?-AllocationTarget {Ψ = Ψ} {Φ = Φ} target old new
    live-ren a resolve-eq
    rewrite liveSlot?-AllocationTarget target a
    with liveSlot? (slotsOf Ψ) a
aliasResult?-AllocationTarget target old new live-ren a resolve-eq
    | just X = refl
aliasResult?-AllocationTarget target old new live-ren a resolve-eq
    | nothing rewrite resolve-eq a = refl

repoint?-AllocationTarget : ∀
    {Θ Θ′ Θ₀ Θ₀′ Δ Δ₀ Δout σ τ σ₀ τ₀}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
    {ψ : TyVar Θ₀ → TyVar Θ₀′} {Q : TyVar Δ₀} {c : TyVar Θ₀′}
    {Ξ : TyEnv Θ₀ Δ₀ σ₀} {Ω : TyEnv Θ₀′ Δ₀ τ₀}
    (query : AllocationTarget φ P b Ψ Φ)
    (birth : AllocationTarget ψ Q c Ξ Ω)
    (old : TyVar Θ → Maybe (Ty Δ))
    (new : TyVar Θ′ → Maybe (Ty Δ))
    (source-anchor : TyVar (suc Θ₀) → TyVar Θ)
    (target-anchor : TyVar (suc Θ₀′) → TyVar Θ′)
    (route : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A : Ty Δ₀)
  → (∀ q → new (φ q) ≡ old q)
  → (∀ q → target-anchor (extᵗ ψ q) ≡ φ (source-anchor q))
  → target-anchor (suc c) ≡ b
  → route Q ≡ just (live-ren P)
  → repoint? new τ τ₀ target-anchor route live-ren A
    ≡ repoint? old σ σ₀ source-anchor route live-ren A
repoint?-AllocationTarget {Q = Q} query birth old new source-anchor target-anchor
    route live-ren (＇ X) resolve-eq anchor-eq extra-eq route-eq
    with Q ≟ X
repoint?-AllocationTarget {Ψ = Ψ} {Φ = Φ} {Ξ = Ξ} {Ω = Ω}
    query birth old new source-anchor target-anchor route live-ren (＇ X)
    resolve-eq anchor-eq extra-eq route-eq | yes refl
    rewrite allocation-source-lexical birth
          | allocation-target-extra birth
          | extra-eq
          | liveSlot?-AllocationTarget-extra query
          | route-eq = refl
repoint?-AllocationTarget {Ψ = Ψ} {Φ = Φ} {Ξ = Ξ} {Ω = Ω}
    query birth old new source-anchor target-anchor route live-ren (＇ X)
    resolve-eq anchor-eq extra-eq route-eq | no Q≢X
    rewrite allocation-target-other birth Q≢X
    with Vec.lookup (slotsOf Ξ) X
repoint?-AllocationTarget {Ψ = Ψ} {Φ = Φ}
    query birth old new source-anchor target-anchor
    route live-ren (＇ X) resolve-eq anchor-eq extra-eq route-eq
    | no Q≢X | nothing = refl
repoint?-AllocationTarget {Ψ = Ψ} {Φ = Φ}
    query birth old new source-anchor target-anchor
    route live-ren (＇ X) resolve-eq anchor-eq extra-eq route-eq
    | no Q≢X | just q =
  subst≡
    (λ anchor → aliasResult? new (slotsOf Φ) live-ren anchor
      ≡ aliasResult? old (slotsOf Ψ) live-ren (source-anchor (suc q)))
    (sym (anchor-eq (suc q)))
    (aliasResult?-AllocationTarget query old new live-ren
      (source-anchor (suc q)) resolve-eq)
repoint?-AllocationTarget query birth old new source-anchor target-anchor
    route live-ren (‵ ι) resolve-eq anchor-eq extra-eq route-eq = refl
repoint?-AllocationTarget query birth old new source-anchor target-anchor
    route live-ren ★ resolve-eq anchor-eq extra-eq route-eq = refl
repoint?-AllocationTarget query birth old new source-anchor target-anchor
    route live-ren (A ⇒ B) resolve-eq anchor-eq extra-eq route-eq =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-AllocationTarget query birth old new source-anchor
          target-anchor route live-ren A resolve-eq anchor-eq extra-eq
          route-eq)
        (repoint?-AllocationTarget query birth old new source-anchor
          target-anchor route live-ren B resolve-eq anchor-eq extra-eq
          route-eq))
      (sym (repoint?-arrow _ _ _ _ _ _ A B)))
repoint?-AllocationTarget query birth old new source-anchor target-anchor
    route live-ren (`∀ A) resolve-eq anchor-eq extra-eq route-eq =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (repoint?-AllocationTarget query (allocation-typ birth) old new
          source-anchor target-anchor (ext-route route)
          (λ X → suc (live-ren X)) A resolve-eq anchor-eq extra-eq
          (trans (cong (mapMaybe suc) route-eq) refl)))
      (sym (repoint?-all _ _ _ _ _ _ A)))

repoint?-query-AllocationTarget : ∀
    {Θ Θ′ Θ₀ Δ Δ₀ Δout : TyCtx}
    {σ : Vec.Vec (Maybe (TyVar Θ)) Δ}
    {τ : Vec.Vec (Maybe (TyVar Θ′)) Δ}
    {σ₀ : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
    (query : AllocationTarget φ P b Ψ Φ)
    (old : TyVar Θ → Maybe (Ty Δ))
    (new : TyVar Θ′ → Maybe (Ty Δ))
    (birth : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀)
    (source-anchor : TyVar (suc Θ₀) → TyVar Θ)
    (target-anchor : TyVar (suc Θ₀) → TyVar Θ′)
    (route : TyVar Δ₀ → Maybe (TyVar Δout))
    (live-ren : TyVar Δ → TyVar Δout) (A : Ty Δ₀)
  → (∀ q → new (φ q) ≡ old q)
  → (∀ q → target-anchor q ≡ φ (source-anchor q))
  → repoint? new τ birth target-anchor route live-ren A
    ≡ repoint? old σ birth source-anchor route live-ren A
repoint?-query-AllocationTarget query old new birth source-anchor
    target-anchor route live-ren (＇ X) resolve-eq anchor-eq
    with Vec.lookup birth X
repoint?-query-AllocationTarget query old new birth source-anchor
    target-anchor route live-ren (＇ X) resolve-eq anchor-eq | nothing = refl
repoint?-query-AllocationTarget {Ψ = Ψ} {Φ = Φ} query old new birth
    source-anchor target-anchor route live-ren (＇ X) resolve-eq anchor-eq
    | just q =
  subst≡
    (λ anchor → aliasResult? new (slotsOf Φ) live-ren anchor
      ≡ aliasResult? old (slotsOf Ψ) live-ren (source-anchor (suc q)))
    (sym (anchor-eq (suc q)))
    (aliasResult?-AllocationTarget query old new live-ren
      (source-anchor (suc q)) resolve-eq)
repoint?-query-AllocationTarget query old new birth source-anchor
    target-anchor route live-ren (‵ ι) resolve-eq anchor-eq = refl
repoint?-query-AllocationTarget query old new birth source-anchor
    target-anchor route live-ren ★ resolve-eq anchor-eq = refl
repoint?-query-AllocationTarget query old new birth source-anchor
    target-anchor route live-ren (A ⇒ B) resolve-eq anchor-eq =
  trans (repoint?-arrow _ _ _ _ _ _ A B)
    (trans (cong₂ _⇒?_
        (repoint?-query-AllocationTarget {σ₀ = birth} query old new birth
          source-anchor target-anchor route live-ren A resolve-eq anchor-eq)
        (repoint?-query-AllocationTarget {σ₀ = birth} query old new birth
          source-anchor target-anchor route live-ren B resolve-eq anchor-eq))
      (sym (repoint?-arrow _ _ _ _ _ _ A B)))
repoint?-query-AllocationTarget query old new birth source-anchor
    target-anchor route live-ren (`∀ A) resolve-eq anchor-eq =
  trans (repoint?-all _ _ _ _ _ _ A)
    (trans (cong all?
        (repoint?-query-AllocationTarget {σ₀ = nothing Vec.∷ birth}
          query old new (nothing Vec.∷ birth) source-anchor target-anchor
          (ext-route route) (λ X → suc (live-ren X)) A
          resolve-eq anchor-eq))
      (sym (repoint?-all _ _ _ _ _ _ A)))

scanRep?-outer-AllocationTarget : ∀
    {Θ Θ′ Θ₀ Δ Δ₀ : TyCtx}
    {σ : Vec.Vec (Maybe (TyVar Θ)) Δ}
    {τ : Vec.Vec (Maybe (TyVar Θ′)) Δ}
    {σ₀ : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
    (query : AllocationTarget φ P b Ψ Φ)
    (old : TyVar Θ → Maybe (Ty Δ))
    (new : TyVar Θ′ → Maybe (Ty Δ))
    (current : TyEnv Θ₀ Δ₀ σ₀)
    (source-anchor : TyVar Θ₀ → TyVar Θ)
    (target-anchor : TyVar Θ₀ → TyVar Θ′)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → (∀ q → new (φ q) ≡ old q)
  → (∀ q → target-anchor q ≡ φ (source-anchor q))
  → scanRep? new Φ current target-anchor route a
    ≡ scanRep? old Ψ current source-anchor route a
scanRep?-outer-AllocationTarget query old new ∅ source-anchor
    target-anchor route () resolve-eq anchor-eq
scanRep?-outer-AllocationTarget query old new
    (current ,begin[ Y ≔ q ]⟨ fresh ⟩) source-anchor target-anchor
    route a resolve-eq anchor-eq =
  scanRep?-outer-AllocationTarget query old new current source-anchor
    target-anchor (λ X → route (punchIn Y X)) a resolve-eq anchor-eq
scanRep?-outer-AllocationTarget query old new (current ,typ)
    source-anchor target-anchor route a resolve-eq anchor-eq =
  scanRep?-outer-AllocationTarget query old new current source-anchor
    target-anchor (λ X → route (suc X)) a resolve-eq anchor-eq
scanRep?-outer-AllocationTarget {Ψ = Ψ} {Φ = Φ} query old new
    (current ,:= A) source-anchor target-anchor route zero
    resolve-eq anchor-eq =
  repoint?-query-AllocationTarget {σ₀ = slotsOf current} query old new
    (slotsOf current) source-anchor target-anchor route (λ X → X) A
    resolve-eq anchor-eq
scanRep?-outer-AllocationTarget query old new (current ,:= A)
    source-anchor target-anchor route (suc a) resolve-eq anchor-eq =
  scanRep?-outer-AllocationTarget query old new current
    (λ q → source-anchor (suc q)) (λ q → target-anchor (suc q))
    route a resolve-eq (λ q → anchor-eq (suc q))
scanRep?-outer-AllocationTarget query old new (current ,end[ Y ])
    source-anchor target-anchor route a resolve-eq anchor-eq =
  scanRep?-outer-AllocationTarget query old new current source-anchor
    target-anchor (route-end Y route) a resolve-eq anchor-eq

route-end-other : ∀ {Δ Δ′} (Y : TyVar (suc Δ))
    (route : TyVar Δ → Maybe (TyVar Δ′)) (X : TyVar (suc Δ))
    (neq : Y ≢ X)
  → route-end Y route X ≡ route (punchOut Y X neq)
route-end-other Y route X neq with Y ≟ X
route-end-other Y route .Y neq | yes refl = ⊥-elim (neq refl)
route-end-other Y route X neq | no _ = refl

scanRep?-AllocationTarget : ∀
    {Θ Θ′ Θ₀ Θ₀′ Δ Δ₀ : TyCtx}
    {σ : Vec.Vec (Maybe (TyVar Θ)) Δ}
    {τ : Vec.Vec (Maybe (TyVar Θ′)) Δ}
    {σ₀ : Vec.Vec (Maybe (TyVar Θ₀)) Δ₀}
    {τ₀ : Vec.Vec (Maybe (TyVar Θ₀′)) Δ₀}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
    {ψ : TyVar Θ₀ → TyVar Θ₀′} {Q : TyVar Δ₀} {c : TyVar Θ₀′}
    {Ξ : TyEnv Θ₀ Δ₀ σ₀} {Ω : TyEnv Θ₀′ Δ₀ τ₀}
    (query : AllocationTarget φ P b Ψ Φ)
    (current : AllocationTarget ψ Q c Ξ Ω)
    (old : TyVar Θ → Maybe (Ty Δ))
    (new : TyVar Θ′ → Maybe (Ty Δ))
    (source-anchor : TyVar Θ₀ → TyVar Θ)
    (target-anchor : TyVar Θ₀′ → TyVar Θ′)
    (route : TyVar Δ₀ → Maybe (TyVar Δ)) (a : TyVar Θ₀)
  → (∀ q → new (φ q) ≡ old q)
  → (∀ q → target-anchor (ψ q) ≡ φ (source-anchor q))
  → target-anchor c ≡ b
  → route Q ≡ just P
  → scanRep? new Φ Ω target-anchor route (ψ a)
    ≡ scanRep? old Ψ Ξ source-anchor route a
scanRep?-AllocationTarget query (allocation-base {Ψ = base}) old new source-anchor
    target-anchor route a resolve-eq anchor-eq extra-eq route-eq =
  scanRep?-outer-AllocationTarget query old new base source-anchor′
    target-anchor′ (λ X → route (suc X)) a resolve-eq anchor-eq′
  where
  source-anchor′ = source-anchor
  target-anchor′ = λ q → target-anchor (suc q)
  anchor-eq′ = λ q → anchor-eq q
scanRep?-AllocationTarget query (allocation-begin current) old new
    source-anchor target-anchor route a resolve-eq anchor-eq extra-eq
    route-eq =
  scanRep?-AllocationTarget query current old new source-anchor
    target-anchor (λ X → route (punchIn _ X)) a resolve-eq anchor-eq
    extra-eq route-eq
scanRep?-AllocationTarget query (allocation-typ current) old new
    source-anchor target-anchor route a resolve-eq anchor-eq extra-eq
    route-eq =
  scanRep?-AllocationTarget query current old new source-anchor
    target-anchor (λ X → route (suc X)) a resolve-eq anchor-eq
    extra-eq route-eq
scanRep?-AllocationTarget query
    (allocation-ν {P = Q} {b = c} {A = A} current) old new source-anchor
    target-anchor route zero resolve-eq anchor-eq extra-eq route-eq =
  repoint?-AllocationTarget query current old new source-anchor target-anchor
    route (λ X → X) A resolve-eq anchor-eq extra-eq route-eq
scanRep?-AllocationTarget query
    (allocation-ν {P = Q} {b = c} current) old new source-anchor
    target-anchor route (suc a) resolve-eq anchor-eq extra-eq route-eq =
  scanRep?-AllocationTarget query current old new
    (λ q → source-anchor (suc q)) (λ q → target-anchor (suc q))
    route a resolve-eq (λ q → anchor-eq (suc q)) extra-eq route-eq

scanRep?-AllocationTarget query
    (allocation-end {P = Q} {Y = Y} neq current) old new
    source-anchor target-anchor route a resolve-eq anchor-eq extra-eq
    route-eq =
  scanRep?-AllocationTarget query current old new source-anchor
    target-anchor (route-end Y route) a resolve-eq anchor-eq extra-eq
    (trans (route-end-other Y route Q neq) route-eq)

AllocationTarget-count : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
  → AllocationTarget φ P b Ψ Φ
  → Θ′ ≡ suc Θ
AllocationTarget-count allocation-base = refl
AllocationTarget-count (allocation-begin target) =
  AllocationTarget-count target
AllocationTarget-count (allocation-typ target) =
  AllocationTarget-count target
AllocationTarget-count (allocation-ν target) =
  cong suc (AllocationTarget-count target)
AllocationTarget-count (allocation-end neq target) =
  AllocationTarget-count target

AllocationTarget-fuel-offset : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
  → (target : AllocationTarget φ P b Ψ Φ) (a : TyVar Θ)
  → ∃[ extra ] (Θ′ ∸ toℕ (φ a) ≡ extra + (Θ ∸ toℕ a))
AllocationTarget-fuel-offset allocation-base a = zero , refl
AllocationTarget-fuel-offset (allocation-begin target) a =
  AllocationTarget-fuel-offset target a
AllocationTarget-fuel-offset (allocation-typ target) a =
  AllocationTarget-fuel-offset target a
AllocationTarget-fuel-offset (allocation-ν target) zero
    with AllocationTarget-count target
AllocationTarget-fuel-offset (allocation-ν target) zero | refl =
  suc zero , refl
AllocationTarget-fuel-offset (allocation-ν target) (suc a) =
  AllocationTarget-fuel-offset target a
AllocationTarget-fuel-offset (allocation-end neq target) a =
  AllocationTarget-fuel-offset target a

repFuel?-AllocationTarget : ∀ fuel {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
    (target : AllocationTarget φ P b Ψ Φ) (a : TyVar Θ)
  → repFuel? fuel Φ (φ a) ≡ repFuel? fuel Ψ a
repFuel?-AllocationTarget zero target a = refl
repFuel?-AllocationTarget (suc fuel) {Ψ = Ψ} {Φ = Φ}
    target a =
  scanRep?-AllocationTarget target target (repFuel? fuel Ψ)
    (repFuel? fuel Φ) (λ q → q) (λ q → q) (λ X → just X) a
    (repFuel?-AllocationTarget fuel target) (λ q → refl) refl refl

rep?-AllocationTarget : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ}
    (target : AllocationTarget φ P b Ψ Φ) {a : TyVar Θ} {A : Ty Δ}
  → rep? Ψ a ≡ just A
  → rep? Φ (φ a) ≡ just A
rep?-AllocationTarget {Θ = Θ} {Θ′ = Θ′} {Ψ = Ψ} {Φ = Φ}
    target {a = a} eq with AllocationTarget-fuel-offset target a
rep?-AllocationTarget {Θ = Θ} {Θ′ = Θ′} {Ψ = Ψ} {Φ = Φ}
    target {a = a} eq | extra , fuel-eq rewrite fuel-eq =
  repFuel?-success-add extra (Θ ∸ toℕ a)
    (trans (repFuel?-AllocationTarget (Θ ∸ toℕ a) target a) eq)

fresh-AllocationTarget : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ} {a : TyVar Θ}
  → AllocationTarget φ P b Ψ Φ
  → a ∉ᵛ σ
  → φ a ∉ᵛ τ
fresh-AllocationTarget target fresh X target-eq =
  fresh X (allocation-target-backward target target-eq)

allocation-source-slot≢ : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P Y : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ} {a : TyVar Θ}
  → (target : AllocationTarget φ P b Ψ Φ)
  → Vec.lookup σ Y ≡ just a
  → Y ≢ P
allocation-source-slot≢ target slot-eq refl =
  nothing≢just
    (trans (sym (allocation-source-lexical target)) slot-eq)

-- A lexical allocation replaces one distinguished lexical slot by the
-- freshly minted anchor's crossing.  All other slots remain at the same
-- positions, so typing only renames anchors.  The begin/end cases commute
-- the distinguished position through the balanced delimiters explicitly.

⊢allocate-target : ∀ {Θ Θ′ Δ σ τ}
    {φ : TyVar Θ → TyVar Θ′} {P : TyVar Δ} {b : TyVar Θ′}
    {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ τ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → AllocationTarget φ P b Ψ Φ
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Φ ∣ Γ ⊢ renameᶿ φ M ⦂ A
⊢allocate-target target (⊢` x∈) = ⊢` x∈
⊢allocate-target target (⊢ƛ M⊢) =
  ⊢ƛ (⊢allocate-target target M⊢)
⊢allocate-target target (⊢· L⊢ M⊢) =
  ⊢· (⊢allocate-target target L⊢) (⊢allocate-target target M⊢)
⊢allocate-target target (⊢Λ M⊢) =
  ⊢Λ (⊢allocate-target (allocation-typ target) M⊢)
⊢allocate-target target (⊢⦂∀ M⊢) =
  ⊢⦂∀ (⊢allocate-target target M⊢)
⊢allocate-target target (⊢$ κ) = ⊢$ κ
⊢allocate-target target (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢allocate-target target L⊢)
    (⊢allocate-target target M⊢)
⊢allocate-target target (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢allocate-target target M⊢) c
⊢allocate-target target (⊢ν M⊢) =
  ⊢ν (⊢allocate-target (allocation-ν target) M⊢)
⊢allocate-target {φ = φ} target
    (⊢reveal {α = a} {fresh = fresh} rep-eq c⊢ M⊢) =
  ⊢reveal (rep?-AllocationTarget target rep-eq) c⊢
    (⊢allocate-target
      (allocation-begin
        {fresh′ = fresh-AllocationTarget target fresh} target)
      M⊢)
⊢allocate-target target
    (⊢conceal {Y = Y} slot-eq rep-eq c⊢ M⊢) =
  ⊢conceal (allocation-target-forward target slot-eq)
    (rep?-AllocationTarget ended-target rep-eq) c⊢
    (⊢allocate-target ended-target M⊢)
  where
  ended-target = allocation-end
    (allocation-source-slot≢ target slot-eq) target
⊢allocate-target target ⊢blame = ⊢blame

⊢allocate-lexical : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {Γ : TermCtx (suc Δ)} {M : Term Θ (suc Δ)}
    {A : Ty (suc Δ)} {C : Ty Δ}
  → Ψ ,typ ∣ Γ ⊢ M ⦂ A
  → ((Ψ ,:= C)
      ,begin[ zero ≔ zero ]⟨ fresh-zero-map-suc {slots = σ} ⟩)
      ∣ Γ ⊢ shiftᶿ M ⦂ A
⊢allocate-lexical M⊢ = ⊢allocate-target allocation-base M⊢
