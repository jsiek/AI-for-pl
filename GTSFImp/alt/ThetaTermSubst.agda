module alt.ThetaTermSubst where

-- File Charter:
--   * Proves typing preservation for parallel term renaming and
--     regular-context injection renaming in the Θ-indexed calculus.
--   * Defines the action of regular-context injections on binder telescopes
--     and proves typing preservation for the general term action
--     `renameᵗᵐ` from alt.ThetaReduction.
--   * Reveal scopes are retained verbatim between `,begin[_≔_]` and their
--     popping `,end[_]` markers.  This file transports the lazy slot and
--     representation lookups across regular and anchor renamings; it performs
--     no telescope entry surgery.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (¬_; yes; no)

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
    Ψ Ψ′ : TyEnv Θ Δ
    Γ Γ′ : TermCtx Δ
    A B C D : Ty Δ
    L M N : Term Θ Δ
    slot inner outer : TyVar Δ
    entry anchor α a : TyVar Θ

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

------------------------------------------------------------------------
-- Ty⁺ renaming algebra
------------------------------------------------------------------------

renameᵗ⁺-cong : ∀ {Θ Δ Δ′} {A⁺ : Ty⁺ Θ Δ}
    {ρ σ : TyVar Δ → TyVar Δ′}
  → (∀ X → ρ X ≡ σ X)
  → renameᵗ⁺ ρ A⁺ ≡ renameᵗ⁺ σ A⁺
renameᵗ⁺-cong {A⁺ = ＇⁺ X} eq = cong ＇⁺_ (eq X)
renameᵗ⁺-cong {A⁺ = ‵⁺ ι} eq = refl
renameᵗ⁺-cong {A⁺ = ★⁺} eq = refl
renameᵗ⁺-cong {A⁺ = A⁺ ⇒⁺ B⁺} eq =
  cong₂ _⇒⁺_ (renameᵗ⁺-cong {A⁺ = A⁺} eq)
    (renameᵗ⁺-cong {A⁺ = B⁺} eq)
renameᵗ⁺-cong {A⁺ = `∀⁺ A⁺} eq =
  cong `∀⁺ (renameᵗ⁺-cong {A⁺ = A⁺} ext-eq)
  where
  ext-eq : ∀ X → extᵗ _ X ≡ extᵗ _ X
  ext-eq zero = refl
  ext-eq (suc X) = cong suc (eq X)
renameᵗ⁺-cong {A⁺ = ref α} eq = refl

renameᶠ⁺-cong : ∀ {Θ Θ′ Δ} {A⁺ : Ty⁺ Θ Δ}
    {ρ σ : TyVar Θ → TyVar Θ′}
  → (∀ α → ρ α ≡ σ α)
  → renameᶠ⁺ ρ A⁺ ≡ renameᶠ⁺ σ A⁺
renameᶠ⁺-cong {A⁺ = ＇⁺ X} eq = refl
renameᶠ⁺-cong {A⁺ = ‵⁺ ι} eq = refl
renameᶠ⁺-cong {A⁺ = ★⁺} eq = refl
renameᶠ⁺-cong {A⁺ = A⁺ ⇒⁺ B⁺} eq =
  cong₂ _⇒⁺_ (renameᶠ⁺-cong {A⁺ = A⁺} eq)
    (renameᶠ⁺-cong {A⁺ = B⁺} eq)
renameᶠ⁺-cong {A⁺ = `∀⁺ A⁺} eq =
  cong `∀⁺ (renameᶠ⁺-cong {A⁺ = A⁺} eq)
renameᶠ⁺-cong {A⁺ = ref α} eq = cong ref (eq α)

renameᵗ⁺-comp : ∀ {Θ Δ₁ Δ₂ Δ₃}
    (ρ : TyVar Δ₁ → TyVar Δ₂)
    (σ : TyVar Δ₂ → TyVar Δ₃) (A⁺ : Ty⁺ Θ Δ₁)
  → renameᵗ⁺ σ (renameᵗ⁺ ρ A⁺)
    ≡ renameᵗ⁺ (λ X → σ (ρ X)) A⁺
renameᵗ⁺-comp ρ σ (＇⁺ X) = refl
renameᵗ⁺-comp ρ σ (‵⁺ ι) = refl
renameᵗ⁺-comp ρ σ ★⁺ = refl
renameᵗ⁺-comp ρ σ (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (renameᵗ⁺-comp ρ σ A⁺)
    (renameᵗ⁺-comp ρ σ B⁺)
renameᵗ⁺-comp ρ σ (`∀⁺ A⁺) =
  cong `∀⁺
    (trans (renameᵗ⁺-comp (extᵗ ρ) (extᵗ σ) A⁺)
      (renameᵗ⁺-cong {A⁺ = A⁺} ext-compose))
  where
  ext-compose : ∀ X
    → extᵗ σ (extᵗ ρ X) ≡ extᵗ (λ Y → σ (ρ Y)) X
  ext-compose zero = refl
  ext-compose (suc X) = refl
renameᵗ⁺-comp ρ σ (ref α) = refl

renameᶠ⁺-comp : ∀ {Θ₁ Θ₂ Θ₃ Δ}
    (ρ : TyVar Θ₁ → TyVar Θ₂)
    (σ : TyVar Θ₂ → TyVar Θ₃) (A⁺ : Ty⁺ Θ₁ Δ)
  → renameᶠ⁺ σ (renameᶠ⁺ ρ A⁺)
    ≡ renameᶠ⁺ (λ α → σ (ρ α)) A⁺
renameᶠ⁺-comp ρ σ (＇⁺ X) = refl
renameᶠ⁺-comp ρ σ (‵⁺ ι) = refl
renameᶠ⁺-comp ρ σ ★⁺ = refl
renameᶠ⁺-comp ρ σ (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (renameᶠ⁺-comp ρ σ A⁺)
    (renameᶠ⁺-comp ρ σ B⁺)
renameᶠ⁺-comp ρ σ (`∀⁺ A⁺) =
  cong `∀⁺ (renameᶠ⁺-comp ρ σ A⁺)
renameᶠ⁺-comp ρ σ (ref α) = refl

renameᵗ⁺-renameᶠ⁺ : ∀ {Θ Θ′ Δ Δ′}
    (ρ : TyVar Δ → TyVar Δ′) (σ : TyVar Θ → TyVar Θ′)
    (A⁺ : Ty⁺ Θ Δ)
  → renameᵗ⁺ ρ (renameᶠ⁺ σ A⁺) ≡ renameᶠ⁺ σ (renameᵗ⁺ ρ A⁺)
renameᵗ⁺-renameᶠ⁺ ρ σ (＇⁺ X) = refl
renameᵗ⁺-renameᶠ⁺ ρ σ (‵⁺ ι) = refl
renameᵗ⁺-renameᶠ⁺ ρ σ ★⁺ = refl
renameᵗ⁺-renameᶠ⁺ ρ σ (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (renameᵗ⁺-renameᶠ⁺ ρ σ A⁺)
    (renameᵗ⁺-renameᶠ⁺ ρ σ B⁺)
renameᵗ⁺-renameᶠ⁺ ρ σ (`∀⁺ A⁺) =
  cong `∀⁺ (renameᵗ⁺-renameᶠ⁺ (extᵗ ρ) σ A⁺)
renameᵗ⁺-renameᶠ⁺ ρ σ (ref α) = refl

renameᵗ⁺-⌜⌝ : ∀ {Θ Δ Δ′} (ρ : TyVar Δ → TyVar Δ′)
    (A : Ty Δ)
  → renameᵗ⁺ {Θ = Θ} ρ ⌜ A ⌝ ≡ ⌜ renameᵗ ρ A ⌝
renameᵗ⁺-⌜⌝ ρ (＇ X) = refl
renameᵗ⁺-⌜⌝ ρ (‵ ι) = refl
renameᵗ⁺-⌜⌝ ρ ★ = refl
renameᵗ⁺-⌜⌝ ρ (A ⇒ B) =
  cong₂ _⇒⁺_ (renameᵗ⁺-⌜⌝ ρ A) (renameᵗ⁺-⌜⌝ ρ B)
renameᵗ⁺-⌜⌝ ρ (`∀ A) = cong `∀⁺ (renameᵗ⁺-⌜⌝ (extᵗ ρ) A)

renameᶠ⁺-⌜⌝ : ∀ {Θ Θ′ Δ} (ρ : TyVar Θ → TyVar Θ′)
    (A : Ty Δ)
  → renameᶠ⁺ ρ ⌜ A ⌝ ≡ ⌜ A ⌝
renameᶠ⁺-⌜⌝ ρ (＇ X) = refl
renameᶠ⁺-⌜⌝ ρ (‵ ι) = refl
renameᶠ⁺-⌜⌝ ρ ★ = refl
renameᶠ⁺-⌜⌝ ρ (A ⇒ B) =
  cong₂ _⇒⁺_ (renameᶠ⁺-⌜⌝ ρ A) (renameᶠ⁺-⌜⌝ ρ B)
renameᶠ⁺-⌜⌝ ρ (`∀ A) = cong `∀⁺ (renameᶠ⁺-⌜⌝ ρ A)

begin⁺-⌜⌝ : ∀ {Θ Δ} (Y : TyVar (suc Δ)) (α : TyVar Θ)
    (A : Ty Δ)
  → begin⁺ Y α ⌜ A ⌝ ≡ ⌜ wkᵗ Y A ⌝
begin⁺-⌜⌝ Y α (＇ X) = refl
begin⁺-⌜⌝ Y α (‵ ι) = refl
begin⁺-⌜⌝ Y α ★ = refl
begin⁺-⌜⌝ Y α (A ⇒ B) =
  cong₂ _⇒⁺_ (begin⁺-⌜⌝ Y α A) (begin⁺-⌜⌝ Y α B)
begin⁺-⌜⌝ Y α (`∀ A) =
  cong `∀⁺
    (trans (begin⁺-⌜⌝ (suc Y) α A)
      (cong (λ B → ⌜ B ⌝) (renameᵗ-cong A punch-eq)))
  where
  punch-eq : ∀ X → punchIn (suc Y) X ≡ extᵗ (punchIn Y) X
  punch-eq zero = refl
  punch-eq (suc X) = refl

------------------------------------------------------------------------
-- Executable strengthening algebra
------------------------------------------------------------------------

fin-suc-injective : ∀ {n} {X Y : TyVar n}
  → suc X ≡ suc Y
  → X ≡ Y
fin-suc-injective refl = refl

punchIn≢ : ∀ {Δ} (Y : TyVar (suc Δ)) (X : TyVar Δ)
  → Y ≢ punchIn Y X
punchIn≢ zero X ()
punchIn≢ (suc Y) zero ()
punchIn≢ (suc Y) (suc X) eq =
  punchIn≢ Y X (fin-suc-injective eq)

punchOut-punchIn : ∀ {Δ} (Y : TyVar (suc Δ)) (X : TyVar Δ)
    (Y≢X : Y ≢ punchIn Y X)
  → punchOut Y (punchIn Y X) Y≢X ≡ X
punchOut-punchIn zero X Y≢X = refl
punchOut-punchIn (suc Y) zero Y≢X = refl
punchOut-punchIn (suc Y) (suc X) Y≢X =
  cong suc (punchOut-punchIn Y X _)

punchIn-punchOut : ∀ {Δ} (Y X : TyVar (suc Δ))
    (Y≢X : Y ≢ X)
  → punchIn Y (punchOut Y X Y≢X) ≡ X
punchIn-punchOut zero zero Y≢X = ⊥-elim (Y≢X refl)
punchIn-punchOut zero (suc X) Y≢X = refl
punchIn-punchOut { Δ = suc Δ } (suc Y) zero Y≢X = refl
punchIn-punchOut { Δ = suc Δ } (suc Y) (suc X) Y≢X =
  cong suc (punchIn-punchOut Y X _)

toRenameᵗ-injective : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
  → ∀ {X Y} → toRenameᵗ ρ X ≡ toRenameᵗ ρ Y → X ≡ Y
toRenameᵗ-injective empty {()}
toRenameᵗ-injective (keep ρ) {zero} {zero} eq = refl
toRenameᵗ-injective (keep ρ) {zero} {suc Y} ()
toRenameᵗ-injective (keep ρ) {suc X} {zero} ()
toRenameᵗ-injective (keep ρ) {suc X} {suc Y} eq =
  cong suc (toRenameᵗ-injective ρ (fin-suc-injective eq))
toRenameᵗ-injective (skip ρ) eq =
  toRenameᵗ-injective ρ (fin-suc-injective eq)

rename-punchOut : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y X : TyVar (suc Δ)) (Y≢X : Y ≢ X)
    (ρY≢ρX : toRenameᵗ ρ Y ≢ toRenameᵗ ρ X)
  → toRenameᵗ (delete↪ᵗ ρ Y) (punchOut Y X Y≢X)
    ≡ punchOut (toRenameᵗ ρ Y) (toRenameᵗ ρ X) ρY≢ρX
rename-punchOut (keep ρ) zero zero Y≢X ρY≢ρX =
  ⊥-elim (Y≢X refl)
rename-punchOut (keep ρ) zero (suc X) Y≢X ρY≢ρX = refl
rename-punchOut {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (keep ρ)) (suc Y) zero Y≢X ρY≢ρX
    rewrite delete-keep-suc (keep ρ) Y =
  refl
rename-punchOut {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (keep ρ)) (suc Y) (suc X) Y≢X ρY≢ρX
    rewrite delete-keep-suc (keep ρ) Y =
  cong suc (rename-punchOut (keep ρ) Y X
    (λ eq → Y≢X (cong suc eq))
    (λ eq → ρY≢ρX (cong suc eq)))
rename-punchOut {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (skip ρ)) (suc Y) zero Y≢X ρY≢ρX
    rewrite delete-keep-suc (skip ρ) Y =
  refl
rename-punchOut {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (skip ρ)) (suc Y) (suc X) Y≢X ρY≢ρX
    rewrite delete-keep-suc (skip ρ) Y =
  cong suc (rename-punchOut (skip ρ) Y X
    (λ eq → Y≢X (cong suc eq))
    (λ eq → ρY≢ρX (cong suc eq)))
rename-punchOut (skip (keep ρ)) Y X Y≢X ρY≢ρX
    rewrite delete-skip (keep ρ) Y =
  cong suc (rename-punchOut (keep ρ) Y X Y≢X
    (λ eq → ρY≢ρX (cong suc eq)))
rename-punchOut (skip (skip ρ)) Y X Y≢X ρY≢ρX
    rewrite delete-skip (skip ρ) Y =
  cong suc (rename-punchOut (skip ρ) Y X Y≢X
    (λ eq → ρY≢ρX (cong suc eq)))

rename-begin⁺ : ∀ {Θ Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (anchor : TyVar Θ) (A⁺ : Ty⁺ Θ Δ)
  → renameᵗ⁺ (toRenameᵗ ρ) (begin⁺ Y anchor A⁺)
    ≡ begin⁺ (toRenameᵗ ρ Y) anchor
        (renameᵗ⁺ (toRenameᵗ (delete↪ᵗ ρ Y)) A⁺)
rename-begin⁺ ρ Y anchor (＇⁺ X) = cong ＇⁺_ (delete-punchIn ρ Y X)
rename-begin⁺ ρ Y anchor (‵⁺ ι) = refl
rename-begin⁺ ρ Y anchor ★⁺ = refl
rename-begin⁺ ρ Y anchor (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (rename-begin⁺ ρ Y anchor A⁺)
    (rename-begin⁺ ρ Y anchor B⁺)
rename-begin⁺ ρ Y anchor (`∀⁺ A⁺) =
  cong `∀⁺
    (trans (renameᵗ⁺-cong {A⁺ = begin⁺ (suc Y) anchor A⁺}
        (λ X → sym (toRename-keep-eq ρ X)))
      (trans (rename-begin⁺ (keep ρ) (suc Y) anchor A⁺)
        (cong (begin⁺ (suc (toRenameᵗ ρ Y)) anchor)
          (renameᵗ⁺-cong {A⁺ = A⁺}
            (toRename-keep-eq (delete↪ᵗ ρ Y))))))
rename-begin⁺ ρ Y anchor (ref α) with anchor ≟ α
rename-begin⁺ ρ Y anchor (ref .anchor) | yes refl = refl
rename-begin⁺ ρ Y anchor (ref α) | no anchor≢α = refl

rename-end⁺ : ∀ {Θ Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (anchor : TyVar Θ)
    (A⁺ : Ty⁺ Θ (suc Δ))
  → renameᵗ⁺ (toRenameᵗ (delete↪ᵗ ρ Y)) (end⁺ Y anchor A⁺)
    ≡ end⁺ (toRenameᵗ ρ Y) anchor
        (renameᵗ⁺ (toRenameᵗ ρ) A⁺)
rename-end⁺ ρ Y anchor (＇⁺ X)
    with Y ≟ X | toRenameᵗ ρ Y ≟ toRenameᵗ ρ X
rename-end⁺ ρ Y anchor (＇⁺ .Y) | yes refl | yes refl = refl
rename-end⁺ ρ Y anchor (＇⁺ .Y) | yes refl | no Y≢Y =
  ⊥-elim (Y≢Y refl)
rename-end⁺ ρ Y anchor (＇⁺ X) | no Y≢X | yes eq =
  ⊥-elim (Y≢X (toRenameᵗ-injective ρ eq))
rename-end⁺ ρ Y anchor (＇⁺ X) | no Y≢X | no ρY≢ρX =
  cong ＇⁺_ (rename-punchOut ρ Y X Y≢X ρY≢ρX)
rename-end⁺ ρ Y anchor (‵⁺ ι) = refl
rename-end⁺ ρ Y anchor ★⁺ = refl
rename-end⁺ ρ Y anchor (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (rename-end⁺ ρ Y anchor A⁺)
    (rename-end⁺ ρ Y anchor B⁺)
rename-end⁺ ρ Y anchor (`∀⁺ A⁺) =
  cong `∀⁺
    (trans (renameᵗ⁺-cong {A⁺ = end⁺ (suc Y) anchor A⁺}
        (λ X → sym (toRename-keep-eq (delete↪ᵗ ρ Y) X)))
      (trans (rename-end⁺ (keep ρ) (suc Y) anchor A⁺)
        (cong (end⁺ (suc (toRenameᵗ ρ Y)) anchor)
          (renameᵗ⁺-cong {A⁺ = A⁺} (toRename-keep-eq ρ)))))
rename-end⁺ ρ Y anchor (ref α) = refl

end-begin⁺ : ∀ {Θ Δ} (Y : TyVar (suc Δ)) (anchor : TyVar Θ)
    (A⁺ : Ty⁺ Θ Δ)
  → end⁺ Y anchor (begin⁺ Y anchor A⁺) ≡ A⁺
end-begin⁺ Y anchor (＇⁺ X) with Y ≟ punchIn Y X
end-begin⁺ Y anchor (＇⁺ X) | yes eq = ⊥-elim (punchIn≢ Y X eq)
end-begin⁺ Y anchor (＇⁺ X) | no Y≢X
    rewrite punchOut-punchIn Y X Y≢X =
  refl
end-begin⁺ Y anchor (‵⁺ ι) = refl
end-begin⁺ Y anchor ★⁺ = refl
end-begin⁺ Y anchor (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (end-begin⁺ Y anchor A⁺) (end-begin⁺ Y anchor B⁺)
end-begin⁺ Y anchor (`∀⁺ A⁺) =
  cong `∀⁺ (end-begin⁺ (suc Y) anchor A⁺)
end-begin⁺ Y anchor (ref α) with anchor ≟ α
end-begin⁺ Y anchor (ref .anchor) | yes refl with Y ≟ Y
end-begin⁺ Y anchor (ref .anchor) | yes refl | yes refl = refl
end-begin⁺ Y anchor (ref .anchor) | yes refl | no Y≢Y =
  ⊥-elim (Y≢Y refl)
end-begin⁺ Y anchor (ref α) | no anchor≢α = refl

data FreshPositions : ∀ {Δ}
    → TyVar (suc Δ) → TyVar (suc (suc Δ))
    → TyVar (suc Δ) → TyVar (suc (suc Δ)) → Set where
  fresh-zero : ∀ {Δ} {Y : TyVar (suc Δ)}
    → FreshPositions zero zero Y (suc Y)
  fresh-suc : ∀ {Δ} {F Y : TyVar (suc Δ)}
      {E Y′ : TyVar (suc (suc Δ))}
    → FreshPositions F E Y Y′
    → FreshPositions (suc F) (suc E) (suc Y) (suc Y′)

fresh-skips-first : ∀ {Δ} {F Y : TyVar (suc Δ)}
    {E Y′ : TyVar (suc (suc Δ))}
  → FreshPositions F E Y Y′
  → punchIn Y′ F ≡ E
fresh-skips-first fresh-zero = refl
fresh-skips-first (fresh-suc positions) =
  cong suc (fresh-skips-first positions)

fresh-first≢second : ∀ {Δ} {F Y : TyVar (suc Δ)}
    {E Y′ : TyVar (suc (suc Δ))}
  → FreshPositions F E Y Y′
  → E ≢ Y′
fresh-first≢second fresh-zero ()
fresh-first≢second (fresh-suc positions) eq =
  fresh-first≢second positions (fin-suc-injective eq)

fresh-remove-second : ∀ {Δ} {F Y : TyVar (suc Δ)}
    {E Y′ : TyVar (suc (suc Δ))}
    (positions : FreshPositions F E Y Y′) (E≢Y′ : E ≢ Y′)
  → punchOut E Y′ E≢Y′ ≡ Y
fresh-remove-second fresh-zero E≢Y′ = refl
fresh-remove-second (fresh-suc positions) E≢Y′ =
  cong suc (fresh-remove-second positions _)

fresh-punch-square : ∀ {Δ} {F Y : TyVar (suc Δ)}
    {E Y′ : TyVar (suc (suc Δ))} (positions : FreshPositions F E Y Y′)
    (X : TyVar Δ)
  → punchIn Y′ (punchIn F X) ≡ punchIn E (punchIn Y X)
fresh-punch-square fresh-zero X = refl
fresh-punch-square (fresh-suc positions) zero = refl
fresh-punch-square (fresh-suc positions) (suc X) =
  cong suc (fresh-punch-square positions X)

fresh-variable⁺ : ∀ {Θ Δ} {F : TyVar (suc Δ)}
    {Y′ : TyVar (suc (suc Δ))} (E : TyVar (suc (suc Δ)))
    (Y : TyVar (suc Δ)) (positions : FreshPositions F E Y Y′)
    (X : TyVar Δ)
  → end⁺ {Θ = suc Θ} E zero (＇⁺ (punchIn Y′ (punchIn F X)))
    ≡ ＇⁺ (punchIn Y X)
fresh-variable⁺ E Y positions X
    rewrite fresh-punch-square positions X with E ≟ punchIn E (punchIn Y X)
fresh-variable⁺ E Y positions X | yes eq =
  ⊥-elim (punchIn≢ E (punchIn Y X) eq)
fresh-variable⁺ E Y positions X | no E≢X
    rewrite punchOut-punchIn E (punchIn Y X) E≢X =
  refl

fresh-begin-end-at⁺ : ∀ {Θ Δ}
    {F : TyVar (suc Δ)}
  → (E : TyVar (suc (suc Δ))) (Y : TyVar (suc Δ))
  → (Y′ : TyVar (suc (suc Δ)))
  → FreshPositions F E Y Y′
  → (anchor : TyVar Θ) (A⁺ : Ty⁺ (suc Θ) Δ)
  → end⁺ E zero (begin⁺ Y′ (suc anchor) (begin⁺ F zero A⁺))
    ≡ begin⁺ Y (suc anchor) A⁺
fresh-begin-end-at⁺ E Y Y′ positions anchor (＇⁺ X) =
  fresh-variable⁺ E Y positions X
fresh-begin-end-at⁺ E Y Y′ positions anchor (‵⁺ ι) = refl
fresh-begin-end-at⁺ E Y Y′ positions anchor ★⁺ = refl
fresh-begin-end-at⁺ E Y Y′ positions anchor (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (fresh-begin-end-at⁺ E Y Y′ positions anchor A⁺)
    (fresh-begin-end-at⁺ E Y Y′ positions anchor B⁺)
fresh-begin-end-at⁺ E Y Y′ positions anchor (`∀⁺ A⁺) =
  cong `∀⁺
    (fresh-begin-end-at⁺ (suc E) (suc Y) (suc Y′)
      (fresh-suc positions) anchor A⁺)
fresh-begin-end-at⁺ E Y Y′ positions anchor (ref zero)
    rewrite fresh-skips-first positions with E ≟ E
fresh-begin-end-at⁺ E Y Y′ positions anchor (ref zero) | yes refl = refl
fresh-begin-end-at⁺ E Y Y′ positions anchor (ref zero) | no E≢E =
  ⊥-elim (E≢E refl)
fresh-begin-end-at⁺ E Y Y′ positions anchor (ref (suc α))
    with anchor ≟ α
fresh-begin-end-at⁺ E Y Y′ positions anchor (ref (suc .anchor))
    | yes refl with E ≟ Y′
fresh-begin-end-at⁺ E Y Y′ positions anchor (ref (suc .anchor))
    | yes refl | yes eq =
  ⊥-elim (fresh-first≢second positions eq)
fresh-begin-end-at⁺ E Y Y′ positions anchor (ref (suc .anchor))
    | yes refl | no E≢Y′ =
  cong ＇⁺_ (fresh-remove-second positions E≢Y′)
fresh-begin-end-at⁺ E Y Y′ positions anchor (ref (suc α))
    | no anchor≢α =
  refl

fresh-begin-end⁺ : ∀ {Θ Δ} (Y : TyVar (suc Δ))
    (anchor : TyVar Θ) (A⁺ : Ty⁺ (suc Θ) Δ)
  → end⁺ zero zero
      (begin⁺ (suc Y) (suc anchor) (begin⁺ zero zero A⁺))
    ≡ begin⁺ Y (suc anchor) A⁺
fresh-begin-end⁺ Y anchor A⁺ =
  fresh-begin-end-at⁺ zero Y (suc Y) fresh-zero anchor A⁺

------------------------------------------------------------------------
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

⊢rename : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ Γ′ : TermCtx Δ}
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

⊢rename-suc : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Ψ ∣ B ∷ Γ ⊢ rename suc M ⦂ A
⊢rename-suc M⊢ = ⊢rename (λ x∈ → S x∈) M⊢

------------------------------------------------------------------------
-- Regular-context injections act on binder telescopes
------------------------------------------------------------------------

emptyTyEnv : ∀ {Θ} (Δ : TyCtx) → TyEnv Θ zero → TyEnv Θ Δ
emptyTyEnv zero Ψ = Ψ
emptyTyEnv (suc Δ) Ψ = emptyTyEnv Δ Ψ ,typ

renameTyEnv : ∀ {Θ Δ Δ′}
  → Δ ↪ᵗ Δ′
  → TyEnv Θ Δ
  → TyEnv Θ Δ′
renameTyEnv {Δ′ = Δ′} ρ ∅ = emptyTyEnv Δ′ ∅
renameTyEnv ρ (Ψ ,:= A) =
  renameTyEnv ρ Ψ ,:= renameᵗ (toRenameᵗ ρ) A
renameTyEnv (keep ρ) (Ψ ,begin[ Y ≔ α ]) =
  renameTyEnv (delete↪ᵗ (keep ρ) Y) Ψ
    ,begin[ toRenameᵗ (keep ρ) Y ≔ α ]
renameTyEnv (skip ρ) (Ψ ,begin[ Y ≔ α ]) =
  renameTyEnv (delete↪ᵗ (skip ρ) Y) Ψ
    ,begin[ toRenameᵗ (skip ρ) Y ≔ α ]
renameTyEnv (keep ρ) (Ψ ,typ) = renameTyEnv ρ Ψ ,typ
renameTyEnv (skip ρ) (Ψ ,typ) = renameTyEnv ρ (Ψ ,typ) ,typ
renameTyEnv ρ (Ψ ,end[ Y ]) =
  renameTyEnv (insert↪ᵗ ρ Y) Ψ
    ,end[ toRenameᵗ (insert↪ᵗ ρ Y) Y ]

renameTyEnv-insert : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Ψ : TyEnv Θ Δ) (Y : TyVar (suc Δ)) (α : TyVar Θ)
  → renameTyEnv (insert↪ᵗ ρ Y) (Ψ ,begin[ Y ≔ α ])
    ≡ renameTyEnv ρ Ψ
        ,begin[ toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ α ]
renameTyEnv-insert ρ Ψ zero α = refl
renameTyEnv-insert (keep ρ) Ψ (suc Y) α
    rewrite delete-insert↪ᵗ ρ Y =
  refl
renameTyEnv-insert (skip ρ) Ψ (suc Y) α
    rewrite delete-insert↪ᵗ ρ (suc Y) =
  refl

rename-∋typ : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {Ψ : TyEnv Θ Δ} {Y : TyVar Δ} {α : TyVar Θ}
  → Ψ ∋typ Y ≔ α
  → renameTyEnv ρ Ψ ∋typ toRenameᵗ ρ Y ≔ α
rename-∋typ (keep ρ) found-begin = found-begin
rename-∋typ (skip ρ) found-begin = found-begin
rename-∋typ ρ@(keep η)
    (skip-begin {Ψ = Ψ} {Y = Y} {α = α} {X = slot}
      {β = anchor}
      Y∈) =
  subst≡
    (λ W → renameTyEnv (delete↪ᵗ ρ slot) Ψ
        ,begin[ toRenameᵗ ρ slot ≔ anchor ] ∋typ W ≔ α)
    (sym (delete-punchIn ρ slot Y))
    (skip-begin (rename-∋typ (delete↪ᵗ ρ slot) Y∈))
rename-∋typ ρ@(skip η)
    (skip-begin {Ψ = Ψ} {Y = Y} {α = α} {X = slot}
      {β = anchor}
      Y∈) =
  subst≡
    (λ W → renameTyEnv (delete↪ᵗ ρ slot) Ψ
        ,begin[ toRenameᵗ ρ slot ≔ anchor ] ∋typ W ≔ α)
    (sym (delete-punchIn ρ slot Y))
    (skip-begin (rename-∋typ (delete↪ᵗ ρ slot) Y∈))
rename-∋typ (keep ρ) (skip-typ Y∈) =
  skip-typ (rename-∋typ ρ Y∈)
rename-∋typ (skip ρ) (skip-typ Y∈) =
  skip-typ (rename-∋typ ρ (skip-typ Y∈))
rename-∋typ ρ (skip-nu-binding Y∈) =
  skip-nu-binding (rename-∋typ ρ Y∈)
rename-∋typ ρ
    (skip-end {Ψ = Ψ} {Y = Y} {X = X} Y∈) =
  skip-end
    (subst≡
      (λ Z → renameTyEnv (insert↪ᵗ ρ Y) Ψ
        ∋typ Z ≔ _)
      (insert-punchIn ρ Y X)
      (rename-∋typ (insert↪ᵗ ρ Y) Y∈))

rename-typ-keep⁺ : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (A⁺ : Ty⁺ Θ Δ)
  → renameᵗ⁺ (toRenameᵗ (keep ρ)) (typ⁺ A⁺)
    ≡ typ⁺ (renameᵗ⁺ (toRenameᵗ ρ) A⁺)
rename-typ-keep⁺ ρ A⁺ =
  trans (renameᵗ⁺-comp suc (toRenameᵗ (keep ρ)) A⁺)
    (sym (renameᵗ⁺-comp (toRenameᵗ ρ) suc A⁺))

rename-typ-skip⁺ : ∀ {Θ Δ Δ′} (ρ : suc Δ ↪ᵗ Δ′)
    (A⁺ : Ty⁺ Θ Δ)
  → renameᵗ⁺ (toRenameᵗ (skip ρ)) (typ⁺ A⁺)
    ≡ typ⁺ (renameᵗ⁺ (toRenameᵗ ρ) (typ⁺ A⁺))
rename-typ-skip⁺ ρ A⁺ =
  trans (renameᵗ⁺-comp suc (toRenameᵗ (skip ρ)) A⁺)
    (trans (renameᵗ⁺-cong {A⁺ = A⁺} env-eq)
      (sym (trans
        (cong (renameᵗ⁺ suc) (renameᵗ⁺-comp suc (toRenameᵗ ρ) A⁺))
        (renameᵗ⁺-comp (λ X → toRenameᵗ ρ (suc X)) suc A⁺))))
  where
  env-eq : ∀ X
    → toRenameᵗ (skip ρ) (suc X) ≡ suc (toRenameᵗ ρ (suc X))
  env-eq X = refl

rename-∋rep⁺ : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {Ψ : TyEnv Θ Δ} {α : TyVar Θ} {A⁺ : Ty⁺ Θ Δ}
  → Ψ ∋rep⁺ α ≔ A⁺
  → renameTyEnv ρ Ψ ∋rep⁺ α ≔
      renameᵗ⁺ (toRenameᵗ ρ) A⁺
rename-∋rep⁺ ρ (Z {Ψ = Ψ} {A = A}) =
  subst≡
    (λ D⁺ → renameTyEnv ρ Ψ ,:= renameᵗ (toRenameᵗ ρ) A
      ∋rep⁺ zero ≔ D⁺)
    payload-eq Z
  where
  target-embed = renameᶠ⁺-⌜⌝ suc (renameᵗ (toRenameᵗ ρ) A)
  source-embed = trans
    (cong (renameᵗ⁺ (toRenameᵗ ρ)) (renameᶠ⁺-⌜⌝ suc A))
    (renameᵗ⁺-⌜⌝ (toRenameᵗ ρ) A)
  payload-eq = trans target-embed (sym source-embed)
rename-∋rep⁺ ρ (S {A⁺ = A⁺} α∈) =
  subst≡ (λ D⁺ → _ ∋rep⁺ _ ≔ D⁺)
    (sym (renameᵗ⁺-renameᶠ⁺ (toRenameᵗ ρ) suc A⁺))
    (S (rename-∋rep⁺ ρ α∈))
rename-∋rep⁺ ρ@(keep η)
    (skip-begin {a = a} {β = anchor} {A⁺ = A⁺} {Y = Y} α∈) =
  subst≡ (λ D⁺ → _ ∋rep⁺ _ ≔ D⁺)
    (sym (rename-begin⁺ ρ Y anchor A⁺))
    (skip-begin (rename-∋rep⁺ (delete↪ᵗ ρ Y) α∈))
rename-∋rep⁺ ρ@(skip η)
    (skip-begin {a = a} {β = anchor} {A⁺ = A⁺} {Y = Y} α∈) =
  subst≡ (λ D⁺ → _ ∋rep⁺ _ ≔ D⁺)
    (sym (rename-begin⁺ ρ Y anchor A⁺))
    (skip-begin (rename-∋rep⁺ (delete↪ᵗ ρ Y) α∈))
rename-∋rep⁺ (keep ρ) (skip-typ {a = a} {A⁺ = A⁺} α∈) =
  subst≡ (λ D⁺ → _ ∋rep⁺ _ ≔ D⁺)
    (sym (rename-typ-keep⁺ ρ A⁺))
    (skip-typ (rename-∋rep⁺ ρ α∈))
rename-∋rep⁺ (skip ρ) (skip-typ {a = a} {A⁺ = A⁺} α∈) =
  subst≡ (λ D⁺ → _ ∋rep⁺ _ ≔ D⁺)
    (sym (rename-typ-skip⁺ ρ A⁺))
    (skip-typ (rename-∋rep⁺ ρ (skip-typ α∈)))
rename-∋rep⁺ ρ
    (skip-end {Ψ = Ψ} {Y = Y} {β = anchor} {a = a}
      {A⁺ = A⁺} slot∈ α∈) =
  subst≡ (λ D⁺ → _ ∋rep⁺ _ ≔ D⁺) payload-eq
    (skip-end (rename-∋typ ρ⁺ slot∈) (rename-∋rep⁺ ρ⁺ α∈))
  where
  ρ⁺ = insert↪ᵗ ρ Y
  deleted-eq = delete-insert↪ᵗ ρ Y
  commute = subst≡
    (λ η → renameᵗ⁺ (toRenameᵗ η) (end⁺ Y anchor A⁺)
      ≡ end⁺ (toRenameᵗ ρ⁺ Y) anchor
          (renameᵗ⁺ (toRenameᵗ ρ⁺) A⁺))
    deleted-eq (rename-end⁺ ρ⁺ Y anchor A⁺)
  payload-eq = sym commute

mutual
  rename-⇓ : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
      {Ψ : TyEnv Θ Δ} {A⁺ : Ty⁺ Θ Δ} {A : Ty Δ}
    → Ψ ⊢ A⁺ ⇓ A
    → renameTyEnv ρ Ψ ⊢ renameᵗ⁺ (toRenameᵗ ρ) A⁺
        ⇓ renameᵗ (toRenameᵗ ρ) A
  rename-⇓ ρ ⇓-var = ⇓-var
  rename-⇓ ρ ⇓-base = ⇓-base
  rename-⇓ ρ ⇓-star = ⇓-star
  rename-⇓ ρ (⇓-fun A⇓ B⇓) = ⇓-fun (rename-⇓ ρ A⇓) (rename-⇓ ρ B⇓)
  rename-⇓ ρ (⇓-all {A⁺ = A⁺} {A = A} A⇓) =
    ⇓-all
      (subst≡ (λ B → _ ⊢ renameᵗ⁺ (extᵗ (toRenameᵗ ρ)) A⁺ ⇓ B)
        (renameᵗ-cong A (toRename-keep-eq ρ))
        (subst≡ (λ B⁺ → _ ⊢ B⁺ ⇓ renameᵗ (toRenameᵗ (keep ρ)) A)
          (renameᵗ⁺-cong {A⁺ = A⁺} (toRename-keep-eq ρ))
          (rename-⇓ (keep ρ) A⇓)))
  rename-⇓ ρ (⇓-ref α∈) = ⇓-ref (rename-∋rep ρ α∈)

  rename-∋rep : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
      {Ψ : TyEnv Θ Δ} {α : TyVar Θ} {A : Ty Δ}
    → Ψ ∋rep α ≔ A
    → renameTyEnv ρ Ψ ∋rep α ≔ renameᵗ (toRenameᵗ ρ) A
  rename-∋rep ρ (∋rep-of α∈ A⇓) =
    ∋rep-of (rename-∋rep⁺ ρ α∈) (rename-⇓ ρ A⇓)


------------------------------------------------------------------------
-- Alternative targets for regular-context renaming
------------------------------------------------------------------------

-- The canonical target `renameTyEnv ρ Ψ` is convenient for arbitrary
-- injections.  Λ descent needs the literal target `Ψ ,typ` for
-- weakening at zero.  This relation records both choices and is stable under
-- every telescope extension, including a verbatim popping marker.

data RenameTarget : ∀ {Θ Δ Δ′}
    (ρ : Δ ↪ᵗ Δ′) → TyEnv Θ Δ → TyEnv Θ Δ′ → Set where
  canonical-target : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ}
      --------------------------------------------------
    → RenameTarget ρ Ψ (renameTyEnv ρ Ψ)

  literal-wk-target : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      -------------------------------------------
    → RenameTarget wk↪ᵗ Ψ (Ψ ,typ)

  target-typ : ∀ {Θ Δ Δ′}
      {ρ : suc Δ ↪ᵗ suc Δ′} {Ψ : TyEnv Θ Δ}
      {Φ : TyEnv Θ Δ′} (X : TyVar (suc Δ)) (α : TyVar Θ)
    → RenameTarget (delete↪ᵗ ρ X) Ψ Φ
      --------------------------------------------------------------
    → RenameTarget ρ (Ψ ,begin[ X ≔ α ])
        (Φ ,begin[ toRenameᵗ ρ X ≔ α ])

  target-lexical : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′}
    → RenameTarget ρ Ψ Φ
      -----------------------------------------------
    → RenameTarget (keep ρ) (Ψ ,typ) (Φ ,typ)

  target-:= : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′} {A : Ty Δ}
    → RenameTarget ρ Ψ Φ
      --------------------------------------------------
    → RenameTarget ρ (Ψ ,:= A)
        (Φ ,:= renameᵗ (toRenameᵗ ρ) A)

  target-end : ∀ {Θ Δ Δ′}
      {ρ : suc Δ ↪ᵗ suc Δ′}
      {Ψ : TyEnv Θ (suc Δ)} {Φ : TyEnv Θ (suc Δ′)}
      (Y : TyVar (suc Δ))
    → RenameTarget ρ Ψ Φ
      ------------------------------------------------------------
    → RenameTarget (delete↪ᵗ ρ Y) (Ψ ,end[ Y ])
        (Φ ,end[ toRenameᵗ ρ Y ])

renameTarget-∋typ : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′}
    {Y : TyVar Δ} {α : TyVar Θ}
  → RenameTarget ρ Ψ Φ
  → Ψ ∋typ Y ≔ α
  → Φ ∋typ toRenameᵗ ρ Y ≔ α
renameTarget-∋typ {ρ = ρ} canonical-target Y∈ = rename-∋typ ρ Y∈
renameTarget-∋typ {Ψ = Ψ} {Y = Y} {α = α}
    literal-wk-target Y∈ =
  subst≡ (λ Z → (Ψ ,typ) ∋typ Z ≔ α)
    (cong suc (sym (toRename-id-eq Y))) (skip-typ Y∈)
renameTarget-∋typ (target-typ X anchor target) found-begin = found-begin
renameTarget-∋typ {ρ = ρ}
    (target-typ X anchor target)
    (skip-begin {Y = Y} Y∈) =
  subst≡ (λ W → _ ∋typ W ≔ _)
    (sym (delete-punchIn ρ X Y))
    (skip-begin (renameTarget-∋typ target Y∈))
renameTarget-∋typ (target-lexical target) (skip-typ Y∈) =
  skip-typ (renameTarget-∋typ target Y∈)
renameTarget-∋typ (target-:= target) (skip-nu-binding Y∈) =
  skip-nu-binding (renameTarget-∋typ target Y∈)
renameTarget-∋typ (target-end Y target) (skip-end Y∈) =
  skip-end
    (subst≡ (λ Z → _ ∋typ Z ≔ _)
      (delete-punchIn _ Y _) (renameTarget-∋typ target Y∈))

renameTarget-∋rep⁺ : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′}
    {α : TyVar Θ} {A⁺ : Ty⁺ Θ Δ}
  → RenameTarget ρ Ψ Φ
  → Ψ ∋rep⁺ α ≔ A⁺
  → Φ ∋rep⁺ α ≔ renameᵗ⁺ (toRenameᵗ ρ) A⁺
renameTarget-∋rep⁺ {ρ = ρ} canonical-target α∈ = rename-∋rep⁺ ρ α∈
renameTarget-∋rep⁺ {A⁺ = A⁺} literal-wk-target α∈ =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (renameᵗ⁺-cong {A⁺ = A⁺} toRename-wk-eq))
    (skip-typ α∈)
renameTarget-∋rep⁺ {ρ = ρ} (target-typ X anchor target)
    (skip-begin {a = a} {A⁺ = A⁺} α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (rename-begin⁺ ρ X anchor A⁺))
    (skip-begin (renameTarget-∋rep⁺ target α∈))
renameTarget-∋rep⁺ {ρ = keep ρ} (target-lexical target)
    (skip-typ {a = a} {A⁺ = A⁺} α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (rename-typ-keep⁺ ρ A⁺))
    (skip-typ (renameTarget-∋rep⁺ target α∈))
renameTarget-∋rep⁺ {ρ = ρ} (target-:= {Φ = Φ} target)
    (Z {A = A}) =
  subst≡
    (λ B⁺ → Φ ,:= renameᵗ (toRenameᵗ ρ) A ∋rep⁺ zero ≔ B⁺)
    payload-eq Z
  where
  target-embed = renameᶠ⁺-⌜⌝ suc (renameᵗ (toRenameᵗ ρ) A)
  source-embed = trans
    (cong (renameᵗ⁺ (toRenameᵗ ρ)) (renameᶠ⁺-⌜⌝ suc A))
    (renameᵗ⁺-⌜⌝ (toRenameᵗ ρ) A)
  payload-eq = trans target-embed (sym source-embed)
renameTarget-∋rep⁺ {ρ = ρ} (target-:= target)
    (S {A⁺ = A⁺} α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (renameᵗ⁺-renameᶠ⁺ (toRenameᵗ ρ) suc A⁺))
    (S (renameTarget-∋rep⁺ target α∈))
renameTarget-∋rep⁺ (target-end {ρ = ρ} Y target)
    (skip-end {Y = .Y} {β = anchor} {a = a} {A⁺ = A⁺}
      slot∈ α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (rename-end⁺ ρ Y anchor A⁺))
    (skip-end (renameTarget-∋typ target slot∈)
      (renameTarget-∋rep⁺ target α∈))

mutual
  renameTarget-⇓ : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′}
      {A⁺ : Ty⁺ Θ Δ} {A : Ty Δ}
    → RenameTarget ρ Ψ Φ
    → Ψ ⊢ A⁺ ⇓ A
    → Φ ⊢ renameᵗ⁺ (toRenameᵗ ρ) A⁺ ⇓ renameᵗ (toRenameᵗ ρ) A
  renameTarget-⇓ target ⇓-var = ⇓-var
  renameTarget-⇓ target ⇓-base = ⇓-base
  renameTarget-⇓ target ⇓-star = ⇓-star
  renameTarget-⇓ target (⇓-fun A⇓ B⇓) =
    ⇓-fun (renameTarget-⇓ target A⇓) (renameTarget-⇓ target B⇓)
  renameTarget-⇓ {ρ = ρ} target (⇓-all {A⁺ = A⁺} {A = A} A⇓) =
    ⇓-all
      (subst≡ (λ B → _ ⊢ renameᵗ⁺ (extᵗ (toRenameᵗ ρ)) A⁺ ⇓ B)
        (renameᵗ-cong A (toRename-keep-eq ρ))
        (subst≡ (λ B⁺ → _ ⊢ B⁺ ⇓ renameᵗ (toRenameᵗ (keep ρ)) A)
          (renameᵗ⁺-cong {A⁺ = A⁺} (toRename-keep-eq ρ))
          (renameTarget-⇓ (target-lexical target) A⇓)))
  renameTarget-⇓ target (⇓-ref α∈) =
    ⇓-ref (renameTarget-∋rep target α∈)

  renameTarget-∋rep : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′}
      {α : TyVar Θ} {A : Ty Δ}
    → RenameTarget ρ Ψ Φ
    → Ψ ∋rep α ≔ A
    → Φ ∋rep α ≔ renameᵗ (toRenameᵗ ρ) A
  renameTarget-∋rep target (∋rep-of α∈ A⇓) =
    ∋rep-of (renameTarget-∋rep⁺ target α∈) (renameTarget-⇓ target A⇓)


renameTarget-insert : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′}
  → RenameTarget ρ Ψ Φ
  → (Y : TyVar (suc Δ)) (α : TyVar Θ)
  → RenameTarget (insert↪ᵗ ρ Y) (Ψ ,begin[ Y ≔ α ])
      (Φ ,begin[ toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ α ])
renameTarget-insert {ρ = ρ} {Ψ = Ψ} {Φ = Φ} target Y α =
  target-typ Y α
    (subst≡ (λ η → RenameTarget η Ψ Φ)
      (sym (delete-insert↪ᵗ ρ Y)) target)

------------------------------------------------------------------------
-- Type-variable renaming preserves typing
------------------------------------------------------------------------

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


⊢renameᵗᵐ-target : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′} {Γ : TermCtx Δ}
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
  renamed-body⊢ = ⊢renameᵗᵐ-target (target-lexical target) M⊢

  body-context⊢ =
    subst≡
      (λ Γ′ → Φ ,typ ∣ Γ′
        ⊢ renameᵗᵐ (keep ρ) _ ⦂ _)
      (renameCtx-keep-shift ρ Γ) renamed-body⊢

  body⊢ =
    subst≡
      (λ B → Φ ,typ ∣
        renameCtx suc (renameCtx (toRenameᵗ ρ) Γ)
          ⊢ renameᵗᵐ (keep ρ) _ ⦂ B)
      (renameᵗ-cong A (toRename-keep-eq ρ)) body-context⊢
⊢renameᵗᵐ-target {ρ = ρ} {Φ = Φ} {Γ = Γ}
    {M = L ⦂∀ C [ A ]} target (⊢⦂∀ L⊢) =
  subst≡
    (λ B → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ L ⦂∀ renameᵗ (toRenameᵗ (keep ρ)) C
        [ renameᵗ (toRenameᵗ ρ) A ] ⦂ B)
    result-eq (⊢⦂∀ body⊢)
  where
  body-eq = renameᵗ-cong C (toRename-keep-eq ρ)

  body⊢ =
    subst≡
      (λ B → Φ ∣ renameCtx (toRenameᵗ ρ) Γ
        ⊢ renameᵗᵐ ρ L ⦂ `∀ B)
      (sym body-eq) (⊢renameᵗᵐ-target target L⊢)

  result-eq = sym (rename-open↪ᵗ ρ C A)
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
  ⊢ν (⊢renameᵗᵐ-target (target-:= target) M⊢)
⊢renameᵗᵐ-target {ρ = ρ} {Φ = Φ}
    target
    (⊢reveal {A = A} {B = B} {C = C} {Y = Y} {α = α}
      α∈ c⊢ M⊢) =
  ⊢reveal (renameTarget-∋rep target α∈) conversion⊢ body⊢
  where
  ρ⁺ = insert↪ᵗ ρ Y
  Y′ = toRenameᵗ ρ⁺ Y

  body⊢ =
    ⊢renameᵗᵐ-target (renameTarget-insert target Y α) M⊢

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↑[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) A
        ↝ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y B))
      (rename-insert-wk ρ Y C)
      (rename-⊢↑ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ =
    subst≡
      (λ B′ →
        ⊢↑[ Y′ ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ ρ) C) ] _
          ⦂ renameᵗ (toRenameᵗ ρ⁺) A ↝ B′)
      (rename-insert-wk ρ Y B) conversion-representation⊢
⊢renameᵗᵐ-target {ρ = ρ⁺@(keep ρ)} target
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y}
      slot∈ α∈ c⊢ M⊢) =
  ⊢conceal slot⊢ lookup⊢ conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  ended-target = target-end Y target

  slot⊢ = renameTarget-∋typ target slot∈
  lookup⊢ = renameTarget-∋rep ended-target α∈
  body⊢ = ⊢renameᵗᵐ-target ended-target M⊢

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↓[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y A)
        ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y C)
      (rename-⊢↓ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ =
    subst≡
      (λ A′ → ⊢↓[ Y′
          ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ deleted) C) ] _
        ⦂ A′ ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y A) conversion-representation⊢
⊢renameᵗᵐ-target {ρ = ρ⁺@(skip ρ)} target
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y}
      slot∈ α∈ c⊢ M⊢) =
  ⊢conceal slot⊢ lookup⊢ conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  ended-target = target-end Y target

  slot⊢ = renameTarget-∋typ target slot∈
  lookup⊢ = renameTarget-∋rep ended-target α∈
  body⊢ = ⊢renameᵗᵐ-target ended-target M⊢

  conversion-representation⊢ =
    subst≡
      (λ R → ⊢↓[ Y′ ⦂ R ] _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) (wkᵗ Y A)
        ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y C)
      (rename-⊢↓ (toRenameᵗ ρ⁺) c⊢)

  conversion⊢ =
    subst≡
      (λ A′ → ⊢↓[ Y′
          ⦂ wkᵗ Y′ (renameᵗ (toRenameᵗ deleted) C) ] _
        ⦂ A′ ↝ renameᵗ (toRenameᵗ ρ⁺) B)
      (rename-delete-wk ρ⁺ Y A) conversion-representation⊢
⊢renameᵗᵐ-target target ⊢blame = ⊢blame

⊢renameᵗᵐ : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ M ⦂ renameᵗ (toRenameᵗ ρ) A
⊢renameᵗᵐ = ⊢renameᵗᵐ-target canonical-target

------------------------------------------------------------------------
-- Observational transport across an adjacent begin/end bracket
------------------------------------------------------------------------

punchIn-injectiveᵗ : ∀ {Δ} (X : TyVar (suc Δ)) {Y q : TyVar Δ}
  → punchIn X Y ≡ punchIn X q
  → Y ≡ q
punchIn-injectiveᵗ zero eq = fin-suc-injective eq
punchIn-injectiveᵗ (suc X) {zero} {zero} eq = refl
punchIn-injectiveᵗ (suc X) {zero} {suc q} ()
punchIn-injectiveᵗ (suc X) {suc Y} {zero} ()
punchIn-injectiveᵗ (suc X) {suc Y} {suc q} eq =
  cong suc (punchIn-injectiveᵗ X (fin-suc-injective eq))

ty-var-injectiveᵗ : ∀ {Δ} {X Y : TyVar Δ}
  → _≡_ {A = Ty Δ} (＇ X) (＇ Y)
  → X ≡ Y
ty-var-injectiveᵗ {X = X} {.X} refl = refl

ty-fun-left-injectiveᵗ : ∀ {Δ} {A B C D : Ty Δ}
  → A ⇒ B ≡ C ⇒ D
  → A ≡ C
ty-fun-left-injectiveᵗ refl = refl

ty-fun-right-injectiveᵗ : ∀ {Δ} {A B C D : Ty Δ}
  → A ⇒ B ≡ C ⇒ D
  → B ≡ D
ty-fun-right-injectiveᵗ refl = refl

ty-all-injectiveᵗ : ∀ {Δ} {A B : Ty (suc Δ)}
  → `∀ A ≡ `∀ B
  → A ≡ B
ty-all-injectiveᵗ refl = refl

renameTy-injectiveᵗ : ∀ {Δ Δ′} {ρ : TyVar Δ → TyVar Δ′}
    (injective : ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y)
    {A B : Ty Δ}
  → renameᵗ ρ A ≡ renameᵗ ρ B
  → A ≡ B
renameTy-injectiveᵗ injective {A = ＇ X} {B = ＇ Y} eq =
  cong ＇_ (injective (ty-var-injectiveᵗ eq))
renameTy-injectiveᵗ injective {A = ＇ X} {B = ‵ ι} ()
renameTy-injectiveᵗ injective {A = ＇ X} {B = ★} ()
renameTy-injectiveᵗ injective {A = ＇ X} {B = B ⇒ C} ()
renameTy-injectiveᵗ injective {A = ＇ X} {B = `∀ B} ()
renameTy-injectiveᵗ injective {A = ‵ ι} {B = ＇ X} ()
renameTy-injectiveᵗ injective {A = ‵ ι} {B = ‵ ι′} refl = refl
renameTy-injectiveᵗ injective {A = ‵ ι} {B = ★} ()
renameTy-injectiveᵗ injective {A = ‵ ι} {B = B ⇒ C} ()
renameTy-injectiveᵗ injective {A = ‵ ι} {B = `∀ B} ()
renameTy-injectiveᵗ injective {A = ★} {B = ＇ X} ()
renameTy-injectiveᵗ injective {A = ★} {B = ‵ ι} ()
renameTy-injectiveᵗ injective {A = ★} {B = ★} eq = refl
renameTy-injectiveᵗ injective {A = ★} {B = B ⇒ C} ()
renameTy-injectiveᵗ injective {A = ★} {B = `∀ B} ()
renameTy-injectiveᵗ injective {A = A ⇒ B} {B = ＇ X} ()
renameTy-injectiveᵗ injective {A = A ⇒ B} {B = ‵ ι} ()
renameTy-injectiveᵗ injective {A = A ⇒ B} {B = ★} ()
renameTy-injectiveᵗ injective {A = A ⇒ B} {B = C ⇒ D} eq =
  cong₂ _⇒_
    (renameTy-injectiveᵗ injective (ty-fun-left-injectiveᵗ eq))
    (renameTy-injectiveᵗ injective (ty-fun-right-injectiveᵗ eq))
renameTy-injectiveᵗ injective {A = A ⇒ B} {B = `∀ C} ()
renameTy-injectiveᵗ injective {A = `∀ A} {B = ＇ X} ()
renameTy-injectiveᵗ injective {A = `∀ A} {B = ‵ ι} ()
renameTy-injectiveᵗ injective {A = `∀ A} {B = ★} ()
renameTy-injectiveᵗ injective {A = `∀ A} {B = B ⇒ C} ()
renameTy-injectiveᵗ {ρ = ρ} injective {A = `∀ A} {B = `∀ B} eq =
  cong `∀
    (renameTy-injectiveᵗ ext-injective (ty-all-injectiveᵗ eq))
  where
  ext-injective : ∀ {X Y}
    → extᵗ ρ X ≡ extᵗ ρ Y
    → X ≡ Y
  ext-injective {zero} {zero} eq = refl
  ext-injective {zero} {suc Y} ()
  ext-injective {suc X} {zero} ()
  ext-injective {suc X} {suc Y} eq =
    cong suc (injective (fin-suc-injective eq))

wkᵗ-injective : ∀ {Δ} (X : TyVar (suc Δ)) {A B : Ty Δ}
  → wkᵗ X A ≡ wkᵗ X B
  → A ≡ B
wkᵗ-injective X = renameTy-injectiveᵗ (punchIn-injectiveᵗ X)

begin-∋typ-view : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {X Z : TyVar (suc Δ)} {α β : TyVar Θ}
  → Ψ ,begin[ X ≔ β ] ∋typ Z ≔ α
  → (Z ≡ X × α ≡ β)
    ⊎ ∃[ Y ] (Z ≡ punchIn X Y × Ψ ∋typ Y ≔ α)
begin-∋typ-view found-begin = inj₁ (refl , refl)
begin-∋typ-view (skip-begin {Y = Y} Y∈) =
  inj₂ (Y , refl , Y∈)

unbegin-∋typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {X : TyVar (suc Δ)} {Y : TyVar Δ} {α β : TyVar Θ}
  → Ψ ,begin[ X ≔ β ] ∋typ punchIn X Y ≔ α
  → Ψ ∋typ Y ≔ α
unbegin-∋typ {X = X} {Y = Y} X∈ with begin-∋typ-view X∈
unbegin-∋typ {X = X} {Y = Y} X∈ | inj₁ (eq , anchor-eq) =
  ⊥-elim (punchIn≢ X Y (sym eq))
unbegin-∋typ {X = X} {Y = Y} X∈
    | inj₂ (q , eq , q∈) =
  subst≡ (λ W → _ ∋typ W ≔ _)
    (sym (punchIn-injectiveᵗ X eq)) q∈

∋typ-unique : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {X : TyVar Δ} {α β : TyVar Θ}
  → Ψ ∋typ X ≔ α
  → Ψ ∋typ X ≔ β
  → α ≡ β
∋typ-unique {X = X} found-begin Y∈ with begin-∋typ-view Y∈
∋typ-unique {X = X} found-begin Y∈ | inj₁ (refl , anchor-eq) =
  sym anchor-eq
∋typ-unique {X = X} found-begin Y∈ | inj₂ (Y , eq , Y∈′) =
  ⊥-elim (punchIn≢ X Y eq)
∋typ-unique (skip-begin {Y = Y} X∈) Z∈
    with begin-∋typ-view Z∈
∋typ-unique (skip-begin {Y = Y} X∈) Z∈
    | inj₁ (eq , anchor-eq) =
  ⊥-elim (punchIn≢ _ Y (sym eq))
∋typ-unique (skip-begin {Y = Y} X∈) Z∈
    | inj₂ (z , eq , Z∈′) =
  ∋typ-unique X∈
    (subst≡ (λ W → _ ∋typ W ≔ _)
      (sym (punchIn-injectiveᵗ _ eq)) Z∈′)
∋typ-unique (skip-typ X∈) (skip-typ Y∈) =
  ∋typ-unique X∈ Y∈
∋typ-unique (skip-nu-binding X∈) (skip-nu-binding Y∈) =
  cong suc (∋typ-unique X∈ Y∈)
∋typ-unique (skip-end X∈) (skip-end Y∈) =
  ∋typ-unique X∈ Y∈

∋rep⁺-unique : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {α : TyVar Θ} {A⁺ B⁺ : Ty⁺ Θ Δ}
  → Ψ ∋rep⁺ α ≔ A⁺
  → Ψ ∋rep⁺ α ≔ B⁺
  → A⁺ ≡ B⁺
∋rep⁺-unique Z Z = refl
∋rep⁺-unique (S A∈) (S B∈) = cong wkᶠ⁺ (∋rep⁺-unique A∈ B∈)
∋rep⁺-unique (skip-begin {a = a} {Y = Y} A∈)
    (skip-begin B∈) =
  cong (begin⁺ Y _) (∋rep⁺-unique A∈ B∈)
∋rep⁺-unique (skip-typ A∈) (skip-typ B∈) =
  cong typ⁺ (∋rep⁺-unique A∈ B∈)
∋rep⁺-unique (skip-end {a = a} slot₁ A∈)
    (skip-end slot₂ B∈) with ∋typ-unique slot₁ slot₂
∋rep⁺-unique (skip-end {a = a} slot₁ A∈)
    (skip-end slot₂ B∈) | refl =
  cong (end⁺ _ _) (∋rep⁺-unique A∈ B∈)

mutual
  ⇓-unique : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {A⁺ : Ty⁺ Θ Δ} {A B : Ty Δ}
    → Ψ ⊢ A⁺ ⇓ A
    → Ψ ⊢ A⁺ ⇓ B
    → A ≡ B
  ⇓-unique ⇓-var ⇓-var = refl
  ⇓-unique ⇓-base ⇓-base = refl
  ⇓-unique ⇓-star ⇓-star = refl
  ⇓-unique (⇓-fun A⇓ B⇓) (⇓-fun A⇓′ B⇓′) =
    cong₂ _⇒_ (⇓-unique A⇓ A⇓′) (⇓-unique B⇓ B⇓′)
  ⇓-unique (⇓-all A⇓) (⇓-all B⇓) = cong `∀ (⇓-unique A⇓ B⇓)
  ⇓-unique (⇓-ref A∈) (⇓-ref B∈) = ∋rep-unique A∈ B∈

  ∋rep-unique : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {α : TyVar Θ} {A B : Ty Δ}
    → Ψ ∋rep α ≔ A
    → Ψ ∋rep α ≔ B
    → A ≡ B
  ∋rep-unique (∋rep-of A∈ A⇓) (∋rep-of B∈ B⇓)
      with ∋rep⁺-unique A∈ B∈
  ∋rep-unique (∋rep-of A∈ A⇓) (∋rep-of B∈ B⇓) | refl =
    ⇓-unique A⇓ B⇓

⇓-⌜⌝ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {A : Ty Δ}
  → Ψ ⊢ ⌜ A ⌝ ⇓ A
⇓-⌜⌝ {A = ＇ X} = ⇓-var
⇓-⌜⌝ {A = ‵ ι} = ⇓-base
⇓-⌜⌝ {A = ★} = ⇓-star
⇓-⌜⌝ {A = A ⇒ B} = ⇓-fun ⇓-⌜⌝ ⇓-⌜⌝
⇓-⌜⌝ {A = `∀ A} = ⇓-all ⇓-⌜⌝

∋rep-here : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {A : Ty Δ}
  → Ψ ,:= A ∋rep zero ≔ A
∋rep-here {Θ = Θ} {Ψ = Ψ} {A = A} =
  ∋rep-of Z
    (subst≡ (λ A⁺ → Ψ ,:= A ⊢ A⁺ ⇓ A)
      (sym (renameᶠ⁺-⌜⌝ (suc {n = Θ}) A)) ⇓-⌜⌝)

∋rep-here-begin : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {A : Ty Δ}
    {Y : TyVar (suc Δ)} {α : TyVar (suc Θ)}
  → (Ψ ,:= A) ,begin[ Y ≔ α ] ∋rep zero ≔ wkᵗ Y A
∋rep-here-begin {Θ = Θ} {Ψ = Ψ} {A = A} {Y = Y} {α = α} =
  ∋rep-of (skip-begin Z)
    (subst≡ (λ A⁺ → (Ψ ,:= A) ,begin[ Y ≔ α ]
        ⊢ A⁺ ⇓ wkᵗ Y A)
      (sym payload-eq) ⇓-⌜⌝)
  where
  payload-eq :
      begin⁺ Y α (wkᶠ⁺ {Θ = Θ} ⌜ A ⌝)
    ≡ ⌜ wkᵗ Y A ⌝
  payload-eq =
    trans (cong (begin⁺ Y α)
      (renameᶠ⁺-⌜⌝ (suc {n = Θ}) A))
      (begin⁺-⌜⌝ Y α A)

------------------------------------------------------------------------
-- Resolved re-entry lookup obstruction
------------------------------------------------------------------------

-- Commit 0190acb9 recorded this telescope as the counterexample to eager
-- end resolution: ending X changed the inner anchor's `＇0` payload to ℕ.
-- A raw `ref` now survives the end and the later begin re-aliases it to the
-- new abstract slot, so the former negative instance is positive.

reenter-counterexample-Ψ : TyEnv (suc (suc zero)) (suc zero)
reenter-counterexample-Ψ =
  (∅ ,:= ‵ `ℕ ,begin[ zero ≔ zero ]) ,:= ＇ zero

reenter-counterexample-slot :
    reenter-counterexample-Ψ ∋typ zero ≔ suc zero
reenter-counterexample-slot = skip-nu-binding found-begin

reenter-counterexample-inner :
    reenter-counterexample-Ψ ∋rep zero ≔ ＇ zero
reenter-counterexample-inner = ∋rep-of Z ⇓-var

reenter-counterexample-slot-rep :
    reenter-counterexample-Ψ ∋rep suc zero ≔ wkᵗ zero (‵ `ℕ)
reenter-counterexample-slot-rep = ∋rep-of (S (skip-begin Z)) ⇓-base

reenter-counterexample-reentered :
    (reenter-counterexample-Ψ ,end[ zero ]
      ,begin[ zero ≔ suc zero ]) ∋rep zero ≔ ＇ zero
reenter-counterexample-reentered =
  ∋rep-of
    (skip-begin (skip-end reenter-counterexample-slot Z)) ⇓-var

-- The unconditional re-entry transport is still false when a second live
-- slot uses the same anchor and ends after the first slot's begin.  Its end
-- introduces `ref (suc zero)` too late for the older begin to re-alias it.
-- The source query therefore resolves to ℕ, whereas re-entering the older
-- slot changes the same query to its abstract variable.

reenter-shadow-Ψ : TyEnv (suc (suc zero)) (suc zero)
reenter-shadow-Ψ =
  ((((∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ])
    ,begin[ zero ≔ zero ]) ,:= ＇ zero) ,end[ zero ]

reenter-shadow-ended-slot :
    (((∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ])
      ,begin[ zero ≔ zero ]) ,:= ＇ zero
      ∋typ zero ≔ suc zero
reenter-shadow-ended-slot = skip-nu-binding found-begin

reenter-shadow-live-slot :
    reenter-shadow-Ψ ∋typ zero ≔ suc zero
reenter-shadow-live-slot =
  skip-end (skip-nu-binding (skip-begin found-begin))

reenter-shadow-new-raw :
    reenter-shadow-Ψ ∋rep⁺ zero ≔ ref (suc zero)
reenter-shadow-new-raw = skip-end reenter-shadow-ended-slot Z

reenter-shadow-old-raw :
    reenter-shadow-Ψ ∋rep⁺ suc zero ≔ ‵⁺ `ℕ
reenter-shadow-old-raw =
  skip-end reenter-shadow-ended-slot
    (S (skip-begin (skip-begin Z)))

reenter-shadow-old-rep :
    reenter-shadow-Ψ ∋rep suc zero ≔ ‵ `ℕ
reenter-shadow-old-rep = ∋rep-of reenter-shadow-old-raw ⇓-base

reenter-shadow-source :
    reenter-shadow-Ψ ∋rep zero ≔ ‵ `ℕ
reenter-shadow-source =
  ∋rep-of reenter-shadow-new-raw (⇓-ref reenter-shadow-old-rep)

reenter-shadow-target :
    (reenter-shadow-Ψ ,end[ zero ]
      ,begin[ zero ≔ suc zero ]) ∋rep zero ≔ ＇ zero
reenter-shadow-target =
  ∋rep-of
    (skip-begin
      (skip-end reenter-shadow-live-slot reenter-shadow-new-raw))
    ⇓-var

reenter-shadow-no-transport :
  ¬ ((reenter-shadow-Ψ ,end[ zero ]
      ,begin[ zero ≔ suc zero ]) ∋rep zero ≔ ‵ `ℕ)
reenter-shadow-no-transport lookup
    with ∋rep-unique lookup reenter-shadow-target
reenter-shadow-no-transport lookup | ()

data SameTarget : ∀ {Θ Δ}
    → TyEnv Θ Δ → TyEnv Θ Δ → Set where
  same-bracket : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {C : Ty Δ}
    → Ψ ∋rep α ≔ C
    → SameTarget Ψ ((Ψ ,begin[ X ≔ α ]) ,end[ X ])

  same-unbracket : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → SameTarget ((Ψ ,begin[ X ≔ α ]) ,end[ X ]) Ψ

  same-fresh-before-begin : ∀ {Θ Δ} {Ψ : TyEnv (suc Θ) Δ}
      {X : TyVar (suc Δ)} {anchor : TyVar Θ} {C : Ty Δ}
    → Ψ ∋rep zero ≔ C
    → SameTarget (Ψ ,begin[ X ≔ suc anchor ])
        (((Ψ ,begin[ zero ≔ zero ])
          ,begin[ suc X ≔ suc anchor ]) ,end[ zero ])

  same-begin : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → SameTarget Ψ Φ
    → SameTarget (Ψ ,begin[ X ≔ α ]) (Φ ,begin[ X ≔ α ])

  same-typ : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
    → SameTarget Ψ Φ
    → SameTarget (Ψ ,typ) (Φ ,typ)

  same-nu : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ} {A : Ty Δ}
    → SameTarget Ψ Φ
    → SameTarget (Ψ ,:= A) (Φ ,:= A)

  same-end : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ (suc Δ)}
      {X : TyVar (suc Δ)}
    → SameTarget Ψ Φ
    → SameTarget (Ψ ,end[ X ]) (Φ ,end[ X ])

sameTarget-∋typ : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
    {X : TyVar Δ} {α : TyVar Θ}
  → SameTarget Ψ Φ
  → Ψ ∋typ X ≔ α
  → Φ ∋typ X ≔ α
sameTarget-∋typ (same-bracket α∈) X∈ =
  skip-end (skip-begin X∈)
sameTarget-∋typ same-unbracket (skip-end X∈) =
  unbegin-∋typ X∈
sameTarget-∋typ (same-fresh-before-begin fresh∈) found-begin =
  skip-end found-begin
sameTarget-∋typ (same-fresh-before-begin fresh∈)
    (skip-begin X∈) =
  skip-end (skip-begin (skip-begin X∈))
sameTarget-∋typ (same-begin target) found-begin = found-begin
sameTarget-∋typ (same-begin target) (skip-begin X∈) =
  skip-begin (sameTarget-∋typ target X∈)
sameTarget-∋typ (same-typ target) (skip-typ X∈) =
  skip-typ (sameTarget-∋typ target X∈)
sameTarget-∋typ (same-nu target) (skip-nu-binding X∈) =
  skip-nu-binding (sameTarget-∋typ target X∈)
sameTarget-∋typ (same-end target) (skip-end X∈) =
  skip-end (sameTarget-∋typ target X∈)

sameTarget-∋rep⁺ : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
    {α : TyVar Θ} {A⁺ : Ty⁺ Θ Δ}
  → SameTarget Ψ Φ
  → Ψ ∋rep⁺ α ≔ A⁺
  → Φ ∋rep⁺ α ≔ A⁺
sameTarget-∋rep⁺ {A⁺ = A⁺}
    (same-bracket {X = X} {α = anchor} α∈) a∈ =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺) (end-begin⁺ X anchor A⁺)
    (skip-end found-begin (skip-begin a∈))
sameTarget-∋rep⁺ same-unbracket
    (skip-end {Y = X} {β = anchor} slot∈
      (skip-begin {a = a} {A⁺ = A⁺} a∈))
    with ∋typ-unique slot∈ found-begin
sameTarget-∋rep⁺ same-unbracket
    (skip-end {Y = X} {β = anchor} slot∈
      (skip-begin {a = a} {A⁺ = A⁺} a∈))
    | refl =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (end-begin⁺ X anchor A⁺)) a∈
sameTarget-∋rep⁺
    (same-fresh-before-begin {X = X} {anchor = anchor} fresh∈)
    (skip-begin {a = a} {A⁺ = A⁺} a∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (fresh-begin-end⁺ X anchor A⁺)
    (skip-end (skip-begin found-begin)
      (skip-begin (skip-begin a∈)))
sameTarget-∋rep⁺ (same-begin target) (skip-begin {a = a} α∈) =
  skip-begin (sameTarget-∋rep⁺ target α∈)
sameTarget-∋rep⁺ (same-typ target) (skip-typ {a = a} α∈) =
  skip-typ (sameTarget-∋rep⁺ target α∈)
sameTarget-∋rep⁺ (same-nu target) Z = Z
sameTarget-∋rep⁺ (same-nu target) (S α∈) =
  S (sameTarget-∋rep⁺ target α∈)
sameTarget-∋rep⁺ (same-end target) (skip-end slot∈ α∈) =
  skip-end (sameTarget-∋typ target slot∈)
    (sameTarget-∋rep⁺ target α∈)

mutual
  sameTarget-⇓ : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
      {A⁺ : Ty⁺ Θ Δ} {A : Ty Δ}
    → SameTarget Ψ Φ
    → Ψ ⊢ A⁺ ⇓ A
    → Φ ⊢ A⁺ ⇓ A
  sameTarget-⇓ target ⇓-var = ⇓-var
  sameTarget-⇓ target ⇓-base = ⇓-base
  sameTarget-⇓ target ⇓-star = ⇓-star
  sameTarget-⇓ target (⇓-fun A⇓ B⇓) =
    ⇓-fun (sameTarget-⇓ target A⇓) (sameTarget-⇓ target B⇓)
  sameTarget-⇓ target (⇓-all A⇓) =
    ⇓-all (sameTarget-⇓ (same-typ target) A⇓)
  sameTarget-⇓ target (⇓-ref α∈) =
    ⇓-ref (sameTarget-∋rep target α∈)

  sameTarget-∋rep : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
      {α : TyVar Θ} {A : Ty Δ}
    → SameTarget Ψ Φ
    → Ψ ∋rep α ≔ A
    → Φ ∋rep α ≔ A
  sameTarget-∋rep target (∋rep-of α∈ A⇓) =
    ∋rep-of (sameTarget-∋rep⁺ target α∈) (sameTarget-⇓ target A⇓)

⊢sameTarget : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → SameTarget Ψ Φ
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Φ ∣ Γ ⊢ M ⦂ A
⊢sameTarget target (⊢` x∈) = ⊢` x∈
⊢sameTarget target (⊢ƛ M⊢) = ⊢ƛ (⊢sameTarget target M⊢)
⊢sameTarget target (⊢· L⊢ M⊢) =
  ⊢· (⊢sameTarget target L⊢) (⊢sameTarget target M⊢)
⊢sameTarget target (⊢Λ M⊢) =
  ⊢Λ (⊢sameTarget (same-typ target) M⊢)
⊢sameTarget target (⊢⦂∀ M⊢) = ⊢⦂∀ (⊢sameTarget target M⊢)
⊢sameTarget target (⊢$ κ) = ⊢$ κ
⊢sameTarget target (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢sameTarget target L⊢) (⊢sameTarget target M⊢)
⊢sameTarget target (⊢⟨⟩ M⊢ c) = ⊢⟨⟩ (⊢sameTarget target M⊢) c
⊢sameTarget target (⊢ν M⊢) = ⊢ν (⊢sameTarget (same-nu target) M⊢)
⊢sameTarget target (⊢reveal α∈ c⊢ M⊢) =
  ⊢reveal (sameTarget-∋rep target α∈) c⊢
    (⊢sameTarget (same-begin target) M⊢)
⊢sameTarget target (⊢conceal slot∈ α∈ c⊢ M⊢) =
  ⊢conceal (sameTarget-∋typ target slot∈)
    (sameTarget-∋rep (same-end target) α∈) c⊢
    (⊢sameTarget (same-end target) M⊢)
⊢sameTarget target ⊢blame = ⊢blame

⊢bracket : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A C : Ty Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ}
  → Ψ ∋rep α ≔ C
  → Ψ ∣ Γ ⊢ M ⦂ A
  → (Ψ ,begin[ X ≔ α ]) ,end[ X ] ∣ Γ ⊢ M ⦂ A
⊢bracket α∈ = ⊢sameTarget (same-bracket α∈)

⊢unbracket : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
    {X : TyVar (suc Δ)} {α : TyVar Θ}
  → (Ψ ,begin[ X ≔ α ]) ,end[ X ] ∣ Γ ⊢ M ⦂ A
  → Ψ ∣ Γ ⊢ M ⦂ A
⊢unbracket = ⊢sameTarget same-unbracket

------------------------------------------------------------------------
-- Literal regular-context weakening at zero
------------------------------------------------------------------------

renameCtx-wk-eq : ∀ {Δ} (Γ : TermCtx Δ)
  → renameCtx (toRenameᵗ wk↪ᵗ) Γ ≡ renameCtx suc Γ
renameCtx-wk-eq [] = refl
renameCtx-wk-eq (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-wk-eq A) (renameCtx-wk-eq Γ)

⊢weakenᵗᵐ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
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

exts-∋ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ Γ′ : TermCtx Δ}
    {σ : Subst Θ Δ} {A : Ty Δ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Ψ ∣ Γ′ ⊢ σ x ⦂ B)
  → ∀ {x B}
  → A ∷ Γ ∋ x ⦂ B
  → Ψ ∣ A ∷ Γ′ ⊢ exts σ x ⦂ B
exts-∋ σ⊢ Z = ⊢` Z
exts-∋ σ⊢ (S x∈) = ⊢rename-suc (σ⊢ x∈)

liftˢ-∋ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ Γ′ : TermCtx Δ}
    {σ : Subst Θ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Ψ ∣ Γ′ ⊢ σ x ⦂ A)
  → ∀ {x A}
  → renameCtx suc Γ ∋ x ⦂ A
  → Ψ ,typ ∣ renameCtx suc Γ′ ⊢ liftˢ σ x ⦂ A
liftˢ-∋ σ⊢ x∈ with lookup-renameCtx-inv x∈
liftˢ-∋ σ⊢ x∈ | B , B∈ , refl = ⊢weakenᵗᵐ (σ⊢ B∈)

⊢subst : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ Γ′ : TermCtx Δ}
    {σ : Subst Θ Δ} {M : Term Θ Δ} {A : Ty Δ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Ψ ∣ Γ′ ⊢ σ x ⦂ B)
  → Ψ ∣ Γ ⊢ M ⦂ A
    --------------------------
  → Ψ ∣ Γ′ ⊢ subst σ M ⦂ A
⊢subst σ⊢ (⊢` x∈) = σ⊢ x∈
⊢subst σ⊢ (⊢ƛ M⊢) = ⊢ƛ (⊢subst (exts-∋ σ⊢) M⊢)
⊢subst σ⊢ (⊢· L⊢ M⊢) =
  ⊢· (⊢subst σ⊢ L⊢) (⊢subst σ⊢ M⊢)
⊢subst σ⊢ (⊢Λ M⊢) = ⊢Λ (⊢subst (liftˢ-∋ σ⊢) M⊢)
⊢subst σ⊢ (⊢⦂∀ L⊢) = ⊢⦂∀ (⊢subst σ⊢ L⊢)
⊢subst σ⊢ (⊢$ κ) = ⊢$ κ
⊢subst σ⊢ (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢subst σ⊢ L⊢) (⊢subst σ⊢ M⊢)
⊢subst σ⊢ (⊢⟨⟩ M⊢ c) = ⊢⟨⟩ (⊢subst σ⊢ M⊢) c
⊢subst σ⊢ (⊢ν M⊢) = ⊢ν M⊢
⊢subst σ⊢ (⊢reveal α∈ c⊢ M⊢) = ⊢reveal α∈ c⊢ M⊢
⊢subst σ⊢ (⊢conceal slot∈ α∈ c⊢ M⊢) =
  ⊢conceal slot∈ α∈ c⊢ M⊢
⊢subst σ⊢ ⊢blame = ⊢blame

⊢[] : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M N : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ A ∷ Γ ⊢ M ⦂ B
  → Ψ ∣ Γ ⊢ N ⦂ A
    ---------------------
  → Ψ ∣ Γ ⊢ M [ N ] ⦂ B
⊢[] {Θ = Θ} {Ψ = Ψ} {Γ = Γ} {N = N} {A = A} M⊢ N⊢ =
  ⊢subst single⊢ M⊢
  where
  single⊢ : ∀ {x C}
    → A ∷ Γ ∋ x ⦂ C
    → Ψ ∣ Γ ⊢ singleSub N x ⦂ C
  single⊢ Z = N⊢
  single⊢ (S x∈) = ⊢` x∈

------------------------------------------------------------------------
-- Anchor renaming and visible weakening
------------------------------------------------------------------------

renameᶠ⁺-begin : ∀ {Θ Θ′ Δ} (ρ : TyVar Θ → TyVar Θ′)
    → (∀ {β γ} → ρ β ≡ ρ γ → β ≡ γ)
    → (Y : TyVar (suc Δ)) (anchor : TyVar Θ) (A⁺ : Ty⁺ Θ Δ)
    → renameᶠ⁺ ρ (begin⁺ Y anchor A⁺)
      ≡ begin⁺ Y (ρ anchor) (renameᶠ⁺ ρ A⁺)
renameᶠ⁺-begin ρ ρ-inj Y anchor (＇⁺ X) = refl
renameᶠ⁺-begin ρ ρ-inj Y anchor (‵⁺ ι) = refl
renameᶠ⁺-begin ρ ρ-inj Y anchor ★⁺ = refl
renameᶠ⁺-begin ρ ρ-inj Y anchor (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (renameᶠ⁺-begin ρ ρ-inj Y anchor A⁺)
    (renameᶠ⁺-begin ρ ρ-inj Y anchor B⁺)
renameᶠ⁺-begin ρ ρ-inj Y anchor (`∀⁺ A⁺) =
  cong `∀⁺ (renameᶠ⁺-begin ρ ρ-inj (suc Y) anchor A⁺)
renameᶠ⁺-begin ρ ρ-inj Y anchor (ref α)
    with anchor ≟ α | ρ anchor ≟ ρ α
renameᶠ⁺-begin ρ ρ-inj Y anchor (ref .anchor)
    | yes refl | yes refl = refl
renameᶠ⁺-begin ρ ρ-inj Y anchor (ref .anchor)
    | yes refl | no eq = ⊥-elim (eq refl)
renameᶠ⁺-begin ρ ρ-inj Y anchor (ref α)
    | no anchor≢α | yes eq = ⊥-elim (anchor≢α (ρ-inj eq))
renameᶠ⁺-begin ρ ρ-inj Y anchor (ref α)
    | no anchor≢α | no eq = refl

renameᶠ⁺-end : ∀ {Θ Θ′ Δ} (ρ : TyVar Θ → TyVar Θ′)
    (Y : TyVar (suc Δ)) (anchor : TyVar Θ)
    (A⁺ : Ty⁺ Θ (suc Δ))
  → renameᶠ⁺ ρ (end⁺ Y anchor A⁺)
    ≡ end⁺ Y (ρ anchor) (renameᶠ⁺ ρ A⁺)
renameᶠ⁺-end ρ Y anchor (＇⁺ X) with Y ≟ X
renameᶠ⁺-end ρ Y anchor (＇⁺ .Y) | yes refl = refl
renameᶠ⁺-end ρ Y anchor (＇⁺ X) | no Y≢X = refl
renameᶠ⁺-end ρ Y anchor (‵⁺ ι) = refl
renameᶠ⁺-end ρ Y anchor ★⁺ = refl
renameᶠ⁺-end ρ Y anchor (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (renameᶠ⁺-end ρ Y anchor A⁺)
    (renameᶠ⁺-end ρ Y anchor B⁺)
renameᶠ⁺-end ρ Y anchor (`∀⁺ A⁺) =
  cong `∀⁺ (renameᶠ⁺-end ρ (suc Y) anchor A⁺)
renameᶠ⁺-end ρ Y anchor (ref α) = refl

renameᶠ⁺-wkᶠ⁺ : ∀ {Θ Θ′ Δ} (ρ : TyVar Θ → TyVar Θ′)
    (A⁺ : Ty⁺ Θ Δ)
  → renameᶠ⁺ (extᵗ ρ) (wkᶠ⁺ A⁺) ≡ wkᶠ⁺ (renameᶠ⁺ ρ A⁺)
renameᶠ⁺-wkᶠ⁺ ρ A⁺ =
  trans (renameᶠ⁺-comp suc (extᵗ ρ) A⁺)
    (sym (renameᶠ⁺-comp ρ suc A⁺))

begin-fresh-shift⁺ : ∀ {Θ Δ} (Y : TyVar (suc Δ))
    (A⁺ : Ty⁺ Θ Δ)
  → begin⁺ Y zero (wkᶠ⁺ A⁺) ≡ renameᵗ⁺ (punchIn Y) (wkᶠ⁺ A⁺)
begin-fresh-shift⁺ Y (＇⁺ X) = refl
begin-fresh-shift⁺ Y (‵⁺ ι) = refl
begin-fresh-shift⁺ Y ★⁺ = refl
begin-fresh-shift⁺ Y (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (begin-fresh-shift⁺ Y A⁺) (begin-fresh-shift⁺ Y B⁺)
begin-fresh-shift⁺ Y (`∀⁺ A⁺) =
  cong `∀⁺
    (trans (begin-fresh-shift⁺ (suc Y) A⁺)
      (renameᵗ⁺-cong {A⁺ = wkᶠ⁺ A⁺} punch-eq))
  where
  punch-eq : ∀ X → punchIn (suc Y) X ≡ extᵗ (punchIn Y) X
  punch-eq zero = refl
  punch-eq (suc X) = refl
begin-fresh-shift⁺ Y (ref α) = refl

renameᶠ⁺-wkᶠ⁺-⌜⌝ : ∀ {Θ Θ′ Δ} (ρ : TyVar Θ → TyVar Θ′)
    (A : Ty Δ)
  → renameᶠ⁺ (extᵗ ρ) (wkᶠ⁺ {Θ = Θ} ⌜ A ⌝)
    ≡ wkᶠ⁺ {Θ = Θ′} ⌜ A ⌝
renameᶠ⁺-wkᶠ⁺-⌜⌝ {Θ = Θ} {Θ′ = Θ′} ρ A =
  trans (cong (renameᶠ⁺ (extᵗ ρ))
    (renameᶠ⁺-⌜⌝ (suc {n = Θ}) A))
    (trans (renameᶠ⁺-⌜⌝ (extᵗ ρ) A)
      (sym (renameᶠ⁺-⌜⌝ (suc {n = Θ′}) A)))

data AnchorTarget : ∀ {Θ Θ′ Δ} (ρ : TyVar Θ → TyVar Θ′)
    → TyEnv Θ Δ → TyEnv Θ′ Δ → Set where
  visible-shift-target : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {B : Ty Δ}
      -----------------------------------------
    → AnchorTarget suc Ψ (Ψ ,:= B)

  anchor-target-typ : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ}
      (Y : TyVar (suc Δ)) (α : TyVar Θ)
    → AnchorTarget ρ Ψ Φ
      --------------------------------------------------
    → AnchorTarget ρ (Ψ ,begin[ Y ≔ α ]) (Φ ,begin[ Y ≔ ρ α ])

  anchor-target-lexical : ∀ {Θ Θ′ Δ}
      {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ}
    → AnchorTarget ρ Ψ Φ
      --------------------------------------------
    → AnchorTarget ρ (Ψ ,typ) (Φ ,typ)

  anchor-target-:= : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ} {A : Ty Δ}
    → AnchorTarget ρ Ψ Φ
      -----------------------------------------------
    → AnchorTarget (extᵗ ρ) (Ψ ,:= A) (Φ ,:= A)

  anchor-target-end : ∀ {Θ Θ′ Δ}
      {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ (suc Δ)} {Φ : TyEnv Θ′ (suc Δ)}
      (Y : TyVar (suc Δ))
    → AnchorTarget ρ Ψ Φ
      --------------------------------------------------
    → AnchorTarget ρ (Ψ ,end[ Y ]) (Φ ,end[ Y ])

  -- A lexical slot has no own crossing.  When anchor weakening allocates
  -- its representation, that newest slot can therefore become the fresh
  -- recorded crossing without transporting a position argument.
  anchor-target-allocate : ∀ {Θ Δ}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv (suc Θ) Δ}
    → AnchorTarget suc Ψ Φ
      ------------------------------------------------------
    → AnchorTarget suc (Ψ ,typ) (Φ ,begin[ zero ≔ zero ])

anchorTarget-∋typ : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ}
    {Y : TyVar Δ} {α : TyVar Θ}
  → (∀ {β γ} → ρ β ≡ ρ γ → β ≡ γ)
  → AnchorTarget ρ Ψ Φ
  → Ψ ∋typ Y ≔ α
  → Φ ∋typ Y ≔ ρ α
anchorTarget-∋typ ρ-inj visible-shift-target Y∈ =
  skip-nu-binding Y∈
anchorTarget-∋typ ρ-inj
    (anchor-target-typ Y anchor target) found-begin = found-begin
anchorTarget-∋typ ρ-inj (anchor-target-typ slot anchor target)
    (skip-begin Y∈) =
  skip-begin (anchorTarget-∋typ ρ-inj target Y∈)
anchorTarget-∋typ ρ-inj (anchor-target-lexical target)
    (skip-typ Y∈) =
  skip-typ (anchorTarget-∋typ ρ-inj target Y∈)
anchorTarget-∋typ ρ-inj (anchor-target-allocate target)
    (skip-typ Y∈) =
  skip-begin (anchorTarget-∋typ ρ-inj target Y∈)
anchorTarget-∋typ ρ-inj (anchor-target-:= target)
    (skip-nu-binding Y∈) =
  skip-nu-binding
    (anchorTarget-∋typ
      (λ eq → fin-suc-injective (ρ-inj (cong suc eq)))
      target Y∈)
anchorTarget-∋typ ρ-inj (anchor-target-end Y target)
    (skip-end Y∈) =
  skip-end (anchorTarget-∋typ ρ-inj target Y∈)

anchorTarget-∋rep⁺ : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ}
    {α : TyVar Θ} {A⁺ : Ty⁺ Θ Δ}
  → (∀ {β γ} → ρ β ≡ ρ γ → β ≡ γ)
  → AnchorTarget ρ Ψ Φ
  → Ψ ∋rep⁺ α ≔ A⁺
  → Φ ∋rep⁺ (ρ α) ≔ renameᶠ⁺ ρ A⁺
anchorTarget-∋rep⁺ ρ-inj visible-shift-target α∈ = S α∈
anchorTarget-∋rep⁺ {ρ = ρ} ρ-inj
    (anchor-target-typ Y anchor target)
    (skip-begin {a = a} {A⁺ = A⁺} α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (renameᶠ⁺-begin ρ ρ-inj Y anchor A⁺))
    (skip-begin (anchorTarget-∋rep⁺ ρ-inj target α∈))
anchorTarget-∋rep⁺ {ρ = ρ} ρ-inj (anchor-target-lexical target)
    (skip-typ {a = a} α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (renameᵗ⁺-renameᶠ⁺ suc ρ _)
    (skip-typ (anchorTarget-∋rep⁺ ρ-inj target α∈))
anchorTarget-∋rep⁺ ρ-inj (anchor-target-allocate target)
    (skip-typ {a = a} α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺) payload-eq
    (skip-begin (anchorTarget-∋rep⁺ ρ-inj target α∈))
  where
  payload-eq = trans (begin-fresh-shift⁺ zero _)
    (renameᵗ⁺-renameᶠ⁺ suc suc _)
anchorTarget-∋rep⁺ ρ-inj
    (anchor-target-:= {ρ = ρ} target)
    (Z {A = A}) rewrite renameᶠ⁺-wkᶠ⁺-⌜⌝ ρ A = Z
anchorTarget-∋rep⁺ ρ-inj (anchor-target-:= {ρ = ρ} target)
    (S {A⁺ = A⁺} α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (renameᶠ⁺-wkᶠ⁺ ρ A⁺))
    (S (anchorTarget-∋rep⁺
      (λ eq → fin-suc-injective (ρ-inj (cong suc eq)))
      target α∈))
anchorTarget-∋rep⁺ {ρ = ρ} ρ-inj (anchor-target-end Y target)
    (skip-end {β = anchor} {a = a} {A⁺ = A⁺} slot∈ α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (renameᶠ⁺-end ρ Y anchor A⁺))
    (skip-end (anchorTarget-∋typ ρ-inj target slot∈)
      (anchorTarget-∋rep⁺ ρ-inj target α∈))

mutual
  anchorTarget-⇓ : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ}
      {A⁺ : Ty⁺ Θ Δ} {A : Ty Δ}
    → (∀ {β γ} → ρ β ≡ ρ γ → β ≡ γ)
    → AnchorTarget ρ Ψ Φ
    → Ψ ⊢ A⁺ ⇓ A
    → Φ ⊢ renameᶠ⁺ ρ A⁺ ⇓ A
  anchorTarget-⇓ ρ-inj target ⇓-var = ⇓-var
  anchorTarget-⇓ ρ-inj target ⇓-base = ⇓-base
  anchorTarget-⇓ ρ-inj target ⇓-star = ⇓-star
  anchorTarget-⇓ ρ-inj target (⇓-fun A⇓ B⇓) =
    ⇓-fun (anchorTarget-⇓ ρ-inj target A⇓)
      (anchorTarget-⇓ ρ-inj target B⇓)
  anchorTarget-⇓ ρ-inj target (⇓-all A⇓) =
    ⇓-all (anchorTarget-⇓ ρ-inj (anchor-target-lexical target) A⇓)
  anchorTarget-⇓ ρ-inj target (⇓-ref α∈) =
    ⇓-ref (anchorTarget-∋rep ρ-inj target α∈)

  anchorTarget-∋rep : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ}
      {α : TyVar Θ} {A : Ty Δ}
    → (∀ {β γ} → ρ β ≡ ρ γ → β ≡ γ)
    → AnchorTarget ρ Ψ Φ
    → Ψ ∋rep α ≔ A
    → Φ ∋rep (ρ α) ≔ A
  anchorTarget-∋rep ρ-inj target (∋rep-of α∈ A⇓) =
    ∋rep-of (anchorTarget-∋rep⁺ ρ-inj target α∈)
      (anchorTarget-⇓ ρ-inj target A⇓)


extᵗ-injective-at : ∀ {Θ Θ′} {ρ : TyVar Θ → TyVar Θ′}
  → (∀ {α β} → ρ α ≡ ρ β → α ≡ β)
  → (α β : TyVar (suc Θ))
  → extᵗ ρ α ≡ extᵗ ρ β → α ≡ β
extᵗ-injective-at ρ-inj zero zero eq = refl
extᵗ-injective-at ρ-inj zero (suc X) ()
extᵗ-injective-at ρ-inj (suc X) zero ()
extᵗ-injective-at ρ-inj (suc X) (suc Y) eq =
  cong suc (ρ-inj (fin-suc-injective eq))

extᵗ-injective : ∀ {Θ Θ′} {ρ : TyVar Θ → TyVar Θ′}
  → (∀ {α β} → ρ α ≡ ρ β → α ≡ β)
  → ∀ {α β : TyVar (suc Θ)}
  → extᵗ ρ α ≡ extᵗ ρ β → α ≡ β
extᵗ-injective ρ-inj {α = X} {β = Y} =
  extᵗ-injective-at ρ-inj X Y

⊢renameᶿ-target : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → (∀ {α β} → ρ α ≡ ρ β → α ≡ β)
  → AnchorTarget ρ Ψ Φ
  → Ψ ∣ Γ ⊢ M ⦂ A
    ----------------------------
  → Φ ∣ Γ ⊢ renameᶿ ρ M ⦂ A
⊢renameᶿ-target ρ-inj target (⊢` x∈) = ⊢` x∈
⊢renameᶿ-target ρ-inj target (⊢ƛ M⊢) =
  ⊢ƛ (⊢renameᶿ-target ρ-inj target M⊢)
⊢renameᶿ-target ρ-inj target (⊢· L⊢ M⊢) =
  ⊢· (⊢renameᶿ-target ρ-inj target L⊢)
    (⊢renameᶿ-target ρ-inj target M⊢)
⊢renameᶿ-target ρ-inj target (⊢Λ M⊢) =
  ⊢Λ (⊢renameᶿ-target ρ-inj (anchor-target-lexical target) M⊢)
⊢renameᶿ-target ρ-inj target (⊢⦂∀ L⊢) =
  ⊢⦂∀ (⊢renameᶿ-target ρ-inj target L⊢)
⊢renameᶿ-target ρ-inj target (⊢$ κ) = ⊢$ κ
⊢renameᶿ-target ρ-inj target (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (⊢renameᶿ-target ρ-inj target L⊢)
    (⊢renameᶿ-target ρ-inj target M⊢)
⊢renameᶿ-target ρ-inj target (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢renameᶿ-target ρ-inj target M⊢) c
⊢renameᶿ-target ρ-inj target (⊢ν M⊢) =
  ⊢ν (⊢renameᶿ-target (extᵗ-injective ρ-inj)
    (anchor-target-:= target) M⊢)
⊢renameᶿ-target ρ-inj target (⊢reveal {α = α} α∈ c⊢ M⊢) =
  ⊢reveal (anchorTarget-∋rep ρ-inj target α∈) c⊢
    (⊢renameᶿ-target ρ-inj (anchor-target-typ _ α target) M⊢)
⊢renameᶿ-target ρ-inj target
    (⊢conceal {Y = Y} slot∈ α∈ c⊢ M⊢) =
  ⊢conceal (anchorTarget-∋typ ρ-inj target slot∈)
    (anchorTarget-∋rep ρ-inj ended-target α∈) c⊢
    (⊢renameᶿ-target ρ-inj ended-target M⊢)
  where
  ended-target = anchor-target-end Y target
⊢renameᶿ-target ρ-inj target ⊢blame = ⊢blame

⊢shiftᶿ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
    ---------------------------
  → Ψ ,:= B ∣ Γ ⊢ shiftᶿ M ⦂ A
⊢shiftᶿ M⊢ = ⊢renameᶿ-target fin-suc-injective
  visible-shift-target M⊢

⊢allocate-lexical : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx (suc Δ)}
    {M : Term Θ (suc Δ)} {A : Ty (suc Δ)} {C : Ty Δ}
  → Ψ ,typ ∣ Γ ⊢ M ⦂ A
    ---------------------------------------------------
  → (Ψ ,:= C) ,begin[ zero ≔ zero ] ∣ Γ ⊢ shiftᶿ M ⦂ A
⊢allocate-lexical M⊢ = ⊢renameᶿ-target fin-suc-injective
  (anchor-target-allocate visible-shift-target) M⊢

------------------------------------------------------------------------
∋:=-shift : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {α : TyVar Θ} {A B : Ty Δ}
  → Ψ ∋rep α ≔ A
  → (Ψ ,:= B) ∋rep (suc α) ≔ A
∋:=-shift =
  anchorTarget-∋rep fin-suc-injective visible-shift-target

∋rep-allocate-lexical : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {α : TyVar Θ} {A B : Ty Δ}
  → Ψ ∋rep α ≔ A
  → (Ψ ,:= B) ,begin[ zero ≔ zero ]
      ∋rep suc α ≔ ⇑ᵗ A
∋rep-allocate-lexical {Ψ = Ψ} {α = α} {A = A} α∈ =
  anchorTarget-∋rep fin-suc-injective
    (anchor-target-allocate visible-shift-target)
    weakened
  where
  weaken-eq : ∀ X → toRenameᵗ wk↪ᵗ X ≡ suc X
  weaken-eq = toRename-wk-eq

  weakened : Ψ ,typ ∋rep α ≔ ⇑ᵗ A
  weakened =
    subst≡ (λ C → Ψ ,typ ∋rep α ≔ C)
      (renameᵗ-cong A weaken-eq)
      (renameTarget-∋rep literal-wk-target α∈)

∋rep-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {α : TyVar Θ} {A : Ty Δ}
  → Ψ ∋rep α ≔ A
  → Ψ ,typ ∋rep α ≔ ⇑ᵗ A
∋rep-typ {Ψ = Ψ} {α = α} {A = A} α∈ =
  subst≡ (λ C → Ψ ,typ ∋rep α ≔ C)
    (renameᵗ-cong A toRename-wk-eq)
    (renameTarget-∋rep literal-wk-target α∈)
