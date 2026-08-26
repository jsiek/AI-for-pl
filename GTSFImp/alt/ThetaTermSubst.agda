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
open import Data.Bool using (Bool; false; true)
open import Data.List using ([]; _∷_; map)
import Data.List.Membership.Propositional as ListMembership
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
  renaming (map to mapMaybe)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
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
    ℒ : Vec.Vec Bool Θ
    ℒ′ : Vec.Vec Bool Θ′
    Ψ Ψ′ : TyEnv Θ Δ ℒ
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

begin⁺-⌜⌝ : ∀ {Θ Δ} (Y : TyVar (suc Δ)) (A : Ty Δ)
  → begin⁺ {Θ = Θ} Y ⌜ A ⌝ ≡ ⌜ wkᵗ Y A ⌝
begin⁺-⌜⌝ Y (＇ X) = refl
begin⁺-⌜⌝ Y (‵ ι) = refl
begin⁺-⌜⌝ Y ★ = refl
begin⁺-⌜⌝ Y (A ⇒ B) =
  cong₂ _⇒⁺_ (begin⁺-⌜⌝ Y A) (begin⁺-⌜⌝ Y B)
begin⁺-⌜⌝ Y (`∀ A) =
  cong `∀⁺
    (trans (begin⁺-⌜⌝ (suc Y) A)
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
    (Y : TyVar (suc Δ)) (A⁺ : Ty⁺ Θ Δ)
  → renameᵗ⁺ (toRenameᵗ ρ) (begin⁺ Y A⁺)
    ≡ begin⁺ (toRenameᵗ ρ Y)
        (renameᵗ⁺ (toRenameᵗ (delete↪ᵗ ρ Y)) A⁺)
rename-begin⁺ ρ Y (＇⁺ X) = cong ＇⁺_ (delete-punchIn ρ Y X)
rename-begin⁺ ρ Y (‵⁺ ι) = refl
rename-begin⁺ ρ Y ★⁺ = refl
rename-begin⁺ ρ Y (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (rename-begin⁺ ρ Y A⁺)
    (rename-begin⁺ ρ Y B⁺)
rename-begin⁺ ρ Y (`∀⁺ A⁺) =
  cong `∀⁺
    (trans (renameᵗ⁺-cong {A⁺ = begin⁺ (suc Y) A⁺}
        (λ X → sym (toRename-keep-eq ρ X)))
      (trans (rename-begin⁺ (keep ρ) (suc Y) A⁺)
        (cong (begin⁺ (suc (toRenameᵗ ρ Y)))
          (renameᵗ⁺-cong {A⁺ = A⁺}
            (toRename-keep-eq (delete↪ᵗ ρ Y))))))
rename-begin⁺ ρ Y (ref α) = refl

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
  → end⁺ Y anchor (begin⁺ Y A⁺) ≡ A⁺
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
end-begin⁺ Y anchor (ref α) = refl

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
  → (A⁺ : Ty⁺ (suc Θ) Δ)
  → end⁺ E zero (begin⁺ Y′ (begin⁺ F A⁺)) ≡ begin⁺ Y A⁺
fresh-begin-end-at⁺ E Y Y′ positions (＇⁺ X) =
  fresh-variable⁺ E Y positions X
fresh-begin-end-at⁺ E Y Y′ positions (‵⁺ ι) = refl
fresh-begin-end-at⁺ E Y Y′ positions ★⁺ = refl
fresh-begin-end-at⁺ E Y Y′ positions (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (fresh-begin-end-at⁺ E Y Y′ positions A⁺)
    (fresh-begin-end-at⁺ E Y Y′ positions B⁺)
fresh-begin-end-at⁺ E Y Y′ positions (`∀⁺ A⁺) =
  cong `∀⁺
    (fresh-begin-end-at⁺ (suc E) (suc Y) (suc Y′)
      (fresh-suc positions) A⁺)
fresh-begin-end-at⁺ E Y Y′ positions (ref α) = refl

fresh-begin-end⁺ : ∀ {Θ Δ} (Y : TyVar (suc Δ))
    (A⁺ : Ty⁺ (suc Θ) Δ)
  → end⁺ zero zero (begin⁺ (suc Y) (begin⁺ zero A⁺))
    ≡ begin⁺ Y A⁺
fresh-begin-end⁺ Y A⁺ =
  fresh-begin-end-at⁺ zero Y (suc Y) fresh-zero A⁺

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

⊢rename : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ} {Γ Γ′ : TermCtx Δ}
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

⊢rename-suc : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → Ψ ∣ B ∷ Γ ⊢ rename suc M ⦂ A
⊢rename-suc M⊢ = ⊢rename (λ x∈ → S x∈) M⊢

------------------------------------------------------------------------
-- Regular-context injections act on binder telescopes
------------------------------------------------------------------------

emptyTyEnv : ∀ {Θ} {ℒ : Vec.Vec Bool Θ} (Δ : TyCtx)
  → TyEnv Θ zero ℒ
  → TyEnv Θ Δ ℒ
emptyTyEnv zero Ψ = Ψ
emptyTyEnv (suc Δ) Ψ = emptyTyEnv Δ Ψ ,typ

renameTyEnv : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ}
  → Δ ↪ᵗ Δ′
  → TyEnv Θ Δ ℒ
  → TyEnv Θ Δ′ ℒ
renameTyEnv {Δ′ = Δ′} ρ ∅ = emptyTyEnv Δ′ ∅
renameTyEnv ρ (Ψ ,:= A) =
  renameTyEnv ρ Ψ ,:= renameᵗ (toRenameᵗ ρ) A
renameTyEnv (keep ρ) (Ψ ,begin[ Y ≔ α ]⟨ inactive ⟩) =
  renameTyEnv (delete↪ᵗ (keep ρ) Y) Ψ
    ,begin[ toRenameᵗ (keep ρ) Y ≔ α ]⟨ inactive ⟩
renameTyEnv (skip ρ) (Ψ ,begin[ Y ≔ α ]⟨ inactive ⟩) =
  renameTyEnv (delete↪ᵗ (skip ρ) Y) Ψ
    ,begin[ toRenameᵗ (skip ρ) Y ≔ α ]⟨ inactive ⟩
renameTyEnv (keep ρ) (Ψ ,typ) = renameTyEnv ρ Ψ ,typ
renameTyEnv (skip ρ) (Ψ ,typ) = renameTyEnv ρ (Ψ ,typ) ,typ
renameTyEnv ρ (Ψ ,end[ Y ≔ α ]) =
  renameTyEnv (insert↪ᵗ ρ Y) Ψ
    ,end[ toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ α ]

liveSlot?-end-none : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    {Ψ : TyEnv Θ (suc Δ) L} {W : TyVar (suc Δ)}
    {bound query : TyVar Θ}
  → query ≢ bound
  → liveSlot? Ψ query ≡ nothing
  → liveSlot? (Ψ ,end[ W ≔ bound ]) query ≡ nothing
liveSlot?-end-none {bound = bound} {query = query} query≢bound eq with query ≟ bound
liveSlot?-end-none query≢bound eq | yes query≡bound =
  ⊥-elim (query≢bound query≡bound)
liveSlot?-end-none query≢bound eq | no query≢bound′ rewrite eq = refl

liveSlot?-end-hit : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    {Ψ : TyEnv Θ (suc Δ) L} {W : TyVar (suc Δ)}
    {bound query : TyVar Θ}
  → query ≢ bound
  → liveSlot? Ψ query ≡ just W
  → liveSlot? (Ψ ,end[ W ≔ bound ]) query ≡ nothing
liveSlot?-end-hit {bound = bound} {query = query} query≢bound eq with query ≟ bound
liveSlot?-end-hit query≢bound eq | yes query≡bound =
  ⊥-elim (query≢bound query≡bound)
liveSlot?-end-hit {W = W} query≢bound eq | no query≢bound′
    rewrite eq with W ≟ W
liveSlot?-end-hit query≢bound eq | no query≢bound′ | yes refl = refl
liveSlot?-end-hit query≢bound eq | no query≢bound′ | no W≢W =
  ⊥-elim (W≢W refl)

liveSlot?-end-keep : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    {Ψ : TyEnv Θ (suc Δ) L} {W Y : TyVar (suc Δ)}
    {bound query : TyVar Θ}
  → query ≢ bound
  → liveSlot? Ψ query ≡ just Y
  → (W≢Y : W ≢ Y)
  → liveSlot? (Ψ ,end[ W ≔ bound ]) query
    ≡ just (punchOut W Y W≢Y)
liveSlot?-end-keep {bound = bound} {query = query} query≢bound eq W≢Y
    with query ≟ bound
liveSlot?-end-keep query≢bound eq W≢Y | yes query≡bound =
  ⊥-elim (query≢bound query≡bound)
liveSlot?-end-keep {W = W} {Y = Y} query≢bound eq W≢Y
    | no query≢bound′ rewrite eq with W ≟ Y
liveSlot?-end-keep query≢bound eq W≢Y | no query≢bound′
    | yes W≡Y = ⊥-elim (W≢Y W≡Y)
liveSlot?-end-keep query≢bound eq W≢Y | no query≢bound′
    | no W≢Y′ = refl

mapMaybe-pointwise : ∀ {a b} {A : Set a} {B : Set b}
    {f g : A → B} (value : Maybe A)
  → (∀ x → f x ≡ g x)
  → mapMaybe f value ≡ mapMaybe g value
mapMaybe-pointwise nothing eq = refl
mapMaybe-pointwise (just x) eq = cong just (eq x)

mapMaybe-compose : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    (f : A → B) (g : B → C) (value : Maybe A)
  → mapMaybe g (mapMaybe f value) ≡ mapMaybe (λ x → g (f x)) value
mapMaybe-compose f g nothing = refl
mapMaybe-compose f g (just x) = refl

map-liveSlot?-end : ∀ {Θ Δ Δ′} {L : Vec.Vec Bool Θ}
    (ρ : suc Δ ↪ᵗ suc Δ′)
    (Ψ : TyEnv Θ (suc Δ) L) (Φ : TyEnv Θ (suc Δ′) L)
    (Y : TyVar (suc Δ)) (bound query : TyVar Θ)
  → liveSlot? Φ query ≡ mapMaybe (toRenameᵗ ρ) (liveSlot? Ψ query)
  → liveSlot?
      (Φ ,end[ toRenameᵗ ρ Y ≔ bound ]) query
    ≡ mapMaybe (toRenameᵗ (delete↪ᵗ ρ Y))
        (liveSlot? (Ψ ,end[ Y ≔ bound ]) query)
map-liveSlot?-end ρ Ψ Φ Y bound query ih with query ≟ bound
map-liveSlot?-end ρ Ψ Φ Y .query query ih | yes refl = refl
map-liveSlot?-end ρ Ψ Φ Y bound query ih | no query≢bound
    with liveSlot? Ψ query | liveSlot? Φ query | ih
map-liveSlot?-end ρ Ψ Φ Y bound query ih | no query≢bound
    | nothing | nothing | refl = refl
map-liveSlot?-end ρ Ψ Φ Y bound query ih | no query≢bound
    | nothing | just target | ()
map-liveSlot?-end ρ Ψ Φ Y bound query ih | no query≢bound
    | just source | nothing | ()
map-liveSlot?-end ρ Ψ Φ Y bound query ih | no query≢bound
    | just source | just .(toRenameᵗ ρ source) | refl
    with Y ≟ source
       | toRenameᵗ ρ Y ≟ toRenameᵗ ρ source
map-liveSlot?-end ρ Ψ Φ Y bound query ih | no query≢bound
    | just .Y | just .(toRenameᵗ ρ Y) | refl
    | yes refl | yes refl = refl
map-liveSlot?-end ρ Ψ Φ Y bound query ih | no query≢bound
    | just .Y | just .(toRenameᵗ ρ Y) | refl
    | yes refl | no image≢image = ⊥-elim (image≢image refl)
map-liveSlot?-end ρ Ψ Φ Y bound query ih | no query≢bound
    | just source | just .(toRenameᵗ ρ source) | refl
    | no Y≢source | yes image-eq =
  ⊥-elim (Y≢source (toRenameᵗ-injective ρ image-eq))
map-liveSlot?-end ρ Ψ Φ Y bound query ih | no query≢bound
    | just source | just .(toRenameᵗ ρ source) | refl
    | no Y≢source | no image≢image =
  cong just (sym (rename-punchOut ρ Y source Y≢source image≢image))

rename-liveSlot? : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ}
    (ρ : Δ ↪ᵗ Δ′) (Ψ : TyEnv Θ Δ ℒ) (query : TyVar Θ)
  → liveSlot? (renameTyEnv ρ Ψ) query
    ≡ mapMaybe (toRenameᵗ ρ) (liveSlot? Ψ query)
rename-liveSlot? ρ ∅ ()
rename-liveSlot? ρ (Ψ ,:= A) zero = refl
rename-liveSlot? ρ (Ψ ,:= A) (suc query) =
  rename-liveSlot? ρ Ψ query
rename-liveSlot? ρ@(keep η)
    (Ψ ,begin[ Y ≔ bound ]⟨ inactive ⟩) query with query ≟ bound
rename-liveSlot? ρ@(keep η)
    (Ψ ,begin[ Y ≔ bound ]⟨ inactive ⟩) .bound
    | yes refl = refl
rename-liveSlot? ρ@(keep η)
    (Ψ ,begin[ Y ≔ bound ]⟨ inactive ⟩) query
    | no query≢bound with liveSlot? Ψ query in slot-eq
rename-liveSlot? ρ@(keep η)
    (Ψ ,begin[ Y ≔ bound ]⟨ inactive ⟩) query
    | no query≢bound | nothing
    rewrite rename-liveSlot? (delete↪ᵗ ρ Y) Ψ query | slot-eq = refl
rename-liveSlot? ρ@(keep η)
    (Ψ ,begin[ Y ≔ bound ]⟨ inactive ⟩) query
    | no query≢bound | just X
    rewrite rename-liveSlot? (delete↪ᵗ ρ Y) Ψ query | slot-eq =
  cong just (sym (delete-punchIn ρ Y X))
rename-liveSlot? ρ@(skip η)
    (Ψ ,begin[ Y ≔ bound ]⟨ inactive ⟩) query with query ≟ bound
rename-liveSlot? ρ@(skip η)
    (Ψ ,begin[ Y ≔ bound ]⟨ inactive ⟩) .bound
    | yes refl = refl
rename-liveSlot? ρ@(skip η)
    (Ψ ,begin[ Y ≔ bound ]⟨ inactive ⟩) query
    | no query≢bound with liveSlot? Ψ query in slot-eq
rename-liveSlot? ρ@(skip η)
    (Ψ ,begin[ Y ≔ bound ]⟨ inactive ⟩) query
    | no query≢bound | nothing
    rewrite rename-liveSlot? (delete↪ᵗ ρ Y) Ψ query | slot-eq = refl
rename-liveSlot? ρ@(skip η)
    (Ψ ,begin[ Y ≔ bound ]⟨ inactive ⟩) query
    | no query≢bound | just X
    rewrite rename-liveSlot? (delete↪ᵗ ρ Y) Ψ query | slot-eq =
  cong just (sym (delete-punchIn ρ Y X))
rename-liveSlot? (keep ρ) (Ψ ,typ) query =
  trans (cong (mapMaybe suc) (rename-liveSlot? ρ Ψ query))
    (trans (mapMaybe-compose (toRenameᵗ ρ) suc (liveSlot? Ψ query))
      (trans (mapMaybe-pointwise (liveSlot? Ψ query)
          (λ X → sym (toRename-keep-eq ρ (suc X))))
        (sym (mapMaybe-compose suc (toRenameᵗ (keep ρ))
          (liveSlot? Ψ query)))))
rename-liveSlot? (skip ρ) (Ψ ,typ) query =
  trans (cong (mapMaybe suc) (rename-liveSlot? ρ (Ψ ,typ) query))
    (trans (mapMaybe-compose (toRenameᵗ ρ) suc
        (liveSlot? (Ψ ,typ) query))
      (mapMaybe-pointwise (liveSlot? (Ψ ,typ) query) (λ X → refl)))
rename-liveSlot? ρ (Ψ ,end[ Y ≔ bound ]) query =
  subst≡
    (λ η → liveSlot?
        (renameTyEnv (insert↪ᵗ ρ Y) Ψ
          ,end[ toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ bound ]) query
      ≡ mapMaybe (toRenameᵗ η) (liveSlot? (Ψ ,end[ Y ≔ bound ]) query))
    (delete-insert↪ᵗ ρ Y)
    (map-liveSlot?-end (insert↪ᵗ ρ Y) Ψ
      (renameTyEnv (insert↪ᵗ ρ Y) Ψ) Y bound query
      (rename-liveSlot? (insert↪ᵗ ρ Y) Ψ query))

renameTyEnv-insert : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} (ρ : Δ ↪ᵗ Δ′)
    (Ψ : TyEnv Θ Δ ℒ)
    (Y : TyVar (suc Δ)) (α : TyVar Θ)
    (inactive : Vec.lookup ℒ α ≡ false)
  → renameTyEnv (insert↪ᵗ ρ Y)
      (Ψ ,begin[ Y ≔ α ]⟨ inactive ⟩)
    ≡ renameTyEnv ρ Ψ
        ,begin[ toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ α ]⟨ inactive ⟩
renameTyEnv-insert ρ Ψ zero α inactive = refl
renameTyEnv-insert (keep ρ) Ψ (suc Y) α inactive
    rewrite delete-insert↪ᵗ ρ Y =
  refl
renameTyEnv-insert (skip ρ) Ψ (suc Y) α inactive
    rewrite delete-insert↪ᵗ ρ (suc Y) =
  refl

rename-∋typ : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} (ρ : Δ ↪ᵗ Δ′)
    {Ψ : TyEnv Θ Δ ℒ} {Y : TyVar Δ} {α : TyVar Θ}
  → Ψ ∋typ Y ≔ α
  → renameTyEnv ρ Ψ ∋typ toRenameᵗ ρ Y ≔ α
rename-∋typ (keep ρ) found-begin = found-begin
rename-∋typ (skip ρ) found-begin = found-begin
rename-∋typ ρ@(keep η)
    (skip-begin {Ψ = Ψ} {Y = Y} {α = α} {X = slot}
      {β = anchor} {inactive = inactive}
      Y∈) =
  subst≡
    (λ W → renameTyEnv (delete↪ᵗ ρ slot) Ψ
        ,begin[ toRenameᵗ ρ slot ≔ anchor ]⟨ inactive ⟩ ∋typ W ≔ α)
    (sym (delete-punchIn ρ slot Y))
    (skip-begin (rename-∋typ (delete↪ᵗ ρ slot) Y∈))
rename-∋typ ρ@(skip η)
    (skip-begin {Ψ = Ψ} {Y = Y} {α = α} {X = slot}
      {β = anchor} {inactive = inactive}
      Y∈) =
  subst≡
    (λ W → renameTyEnv (delete↪ᵗ ρ slot) Ψ
        ,begin[ toRenameᵗ ρ slot ≔ anchor ]⟨ inactive ⟩ ∋typ W ≔ α)
    (sym (delete-punchIn ρ slot Y))
    (skip-begin (rename-∋typ (delete↪ᵗ ρ slot) Y∈))
rename-∋typ (keep ρ) (skip-typ Y∈) =
  skip-typ (rename-∋typ ρ Y∈)
rename-∋typ (skip ρ) (skip-typ Y∈) =
  skip-typ (rename-∋typ ρ (skip-typ Y∈))
rename-∋typ ρ (skip-nu-binding Y∈) =
  skip-nu-binding (rename-∋typ ρ Y∈)
rename-∋typ ρ
    (skip-end {Ψ = Ψ} {Y = Y} {X = X} {β = bound} Y∈) =
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

rename-∋rep⁺ : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} (ρ : Δ ↪ᵗ Δ′)
    {Ψ : TyEnv Θ Δ ℒ} {α : TyVar Θ} {A⁺ : Ty⁺ Θ Δ}
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
    (sym (rename-begin⁺ ρ Y A⁺))
    (skip-begin (rename-∋rep⁺ (delete↪ᵗ ρ Y) α∈))
rename-∋rep⁺ ρ@(skip η)
    (skip-begin {a = a} {β = anchor} {A⁺ = A⁺} {Y = Y} α∈) =
  subst≡ (λ D⁺ → _ ∋rep⁺ _ ≔ D⁺)
    (sym (rename-begin⁺ ρ Y A⁺))
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
      {A⁺ = A⁺} α∈) =
  subst≡ (λ D⁺ → _ ∋rep⁺ _ ≔ D⁺) payload-eq
    (skip-end (rename-∋rep⁺ ρ⁺ α∈))
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
  rename-⇓ : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} (ρ : Δ ↪ᵗ Δ′)
      {Ψ : TyEnv Θ Δ ℒ} {A⁺ : Ty⁺ Θ Δ} {A : Ty Δ}
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
  rename-⇓ ρ {Ψ = Ψ}
      (⇓-ref-live {β = query} {Y = Y} live) =
    ⇓-ref-live
      (trans (rename-liveSlot? ρ Ψ query)
        (cong (mapMaybe (toRenameᵗ ρ)) live))
  rename-⇓ ρ (⇓-ref-dead dead α∈) =
    ⇓-ref-dead dead (rename-∋rep ρ α∈)

  rename-∋rep : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} (ρ : Δ ↪ᵗ Δ′)
      {Ψ : TyEnv Θ Δ ℒ} {α : TyVar Θ} {A : Ty Δ}
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

data RenameTarget : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ}
    (ρ : Δ ↪ᵗ Δ′) → TyEnv Θ Δ ℒ → TyEnv Θ Δ′ ℒ → Set where
  canonical-target : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {ℒ : Vec.Vec Bool Θ}
      {Ψ : TyEnv Θ Δ ℒ}
      --------------------------------------------------
    → RenameTarget ρ Ψ (renameTyEnv ρ Ψ)

  literal-wk-target : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ}
      -------------------------------------------
    → RenameTarget wk↪ᵗ Ψ (Ψ ,typ)

  target-typ : ∀ {Θ Δ Δ′}
      {ℒ : Vec.Vec Bool Θ}
      {ρ : suc Δ ↪ᵗ suc Δ′} {Ψ : TyEnv Θ Δ ℒ}
      {Φ : TyEnv Θ Δ′ ℒ} (X : TyVar (suc Δ)) (α : TyVar Θ)
      {inactive : Vec.lookup ℒ α ≡ false}
    → RenameTarget (delete↪ᵗ ρ X) Ψ Φ
      --------------------------------------------------------------
    → RenameTarget ρ (Ψ ,begin[ X ≔ α ]⟨ inactive ⟩)
        (Φ ,begin[ toRenameᵗ ρ X ≔ α ]⟨ inactive ⟩)

  target-lexical : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {ℒ : Vec.Vec Bool Θ}
      {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ Δ′ ℒ}
    → RenameTarget ρ Ψ Φ
      -----------------------------------------------
    → RenameTarget (keep ρ) (Ψ ,typ) (Φ ,typ)

  target-:= : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
      {ℒ : Vec.Vec Bool Θ}
      {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ Δ′ ℒ} {A : Ty Δ}
    → RenameTarget ρ Ψ Φ
      --------------------------------------------------
    → RenameTarget ρ (Ψ ,:= A)
        (Φ ,:= renameᵗ (toRenameᵗ ρ) A)

  target-end : ∀ {Θ Δ Δ′}
      {ℒ : Vec.Vec Bool Θ}
      {ρ : suc Δ ↪ᵗ suc Δ′}
      {Ψ : TyEnv Θ (suc Δ) ℒ} {Φ : TyEnv Θ (suc Δ′) ℒ}
      (Y : TyVar (suc Δ)) (β : TyVar Θ)
    → RenameTarget ρ Ψ Φ
      ------------------------------------------------------------
    → RenameTarget (delete↪ᵗ ρ Y) (Ψ ,end[ Y ≔ β ])
        (Φ ,end[ toRenameᵗ ρ Y ≔ β ])

renameTarget-∋typ : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ Δ′ ℒ}
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
renameTarget-∋typ (target-end Y bound target) (skip-end Y∈) =
  skip-end
    (subst≡ (λ Z → _ ∋typ Z ≔ _)
      (delete-punchIn _ Y _) (renameTarget-∋typ target Y∈))

renameTarget-liveSlot? : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ}
    {Φ : TyEnv Θ Δ′ ℒ}
  → RenameTarget ρ Ψ Φ
  → (query : TyVar Θ)
  → liveSlot? Φ query
    ≡ mapMaybe (toRenameᵗ ρ) (liveSlot? Ψ query)
renameTarget-liveSlot? {ρ = ρ} {Ψ = Ψ} canonical-target query =
  rename-liveSlot? ρ Ψ query
renameTarget-liveSlot? {Ψ = Ψ} literal-wk-target query
    with liveSlot? Ψ query
renameTarget-liveSlot? {Ψ = Ψ} literal-wk-target query | nothing = refl
renameTarget-liveSlot? {Ψ = Ψ} literal-wk-target query | just X =
  cong just (cong suc (sym (toRename-id-eq X)))
renameTarget-liveSlot? {ρ = ρ}
    (target-typ X anchor target) query with query ≟ anchor
renameTarget-liveSlot? {ρ = ρ}
    (target-typ X anchor target) .anchor | yes refl = refl
renameTarget-liveSlot? {ρ = ρ} {Ψ = Ψ ,begin[ X ≔ anchor ]⟨ inactive ⟩}
    (target-typ X anchor target) query | no query≢anchor
    with liveSlot? Ψ query in slot-eq
renameTarget-liveSlot? {ρ = ρ}
    (target-typ X anchor target) query | no query≢anchor | nothing
    rewrite renameTarget-liveSlot? target query | slot-eq = refl
renameTarget-liveSlot? {ρ = ρ}
    (target-typ X anchor target) query | no query≢anchor | just Y
    rewrite renameTarget-liveSlot? target query | slot-eq =
  cong just (sym (delete-punchIn ρ X Y))
renameTarget-liveSlot? {ρ = keep ρ} {Ψ = Ψ ,typ}
    (target-lexical target) query with liveSlot? Ψ query in slot-eq
renameTarget-liveSlot? {ρ = keep ρ}
    (target-lexical target) query | nothing
    rewrite renameTarget-liveSlot? target query | slot-eq = refl
renameTarget-liveSlot? {ρ = keep ρ}
    (target-lexical target) query | just X
    rewrite renameTarget-liveSlot? target query | slot-eq =
  cong just (sym (toRename-keep-eq ρ (suc X)))
renameTarget-liveSlot? (target-:= target) zero = refl
renameTarget-liveSlot? (target-:= target) (suc query) =
  renameTarget-liveSlot? target query
renameTarget-liveSlot?
    (target-end {ρ = injection} Y anchor target) query =
  map-liveSlot?-end injection _ _ Y anchor query
    (renameTarget-liveSlot? target query)

renameTarget-∋rep⁺ : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ Δ′ ℒ}
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
    (sym (rename-begin⁺ ρ X A⁺))
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
renameTarget-∋rep⁺ (target-end {ρ = ρ} Y anchor target)
    (skip-end {Y = .Y} {β = anchor} {a = a} {A⁺ = A⁺}
      α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (rename-end⁺ ρ Y anchor A⁺))
    (skip-end (renameTarget-∋rep⁺ target α∈))

mutual
  renameTarget-⇓ : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ Δ′ ℒ}
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
  renameTarget-⇓ {ρ = ρ} {Ψ = Ψ} target
      (⇓-ref-live {β = query} {Y = Y} live) =
    ⇓-ref-live
      (trans (renameTarget-liveSlot? target query)
        (cong (mapMaybe (toRenameᵗ ρ)) live))
  renameTarget-⇓ target (⇓-ref-dead dead α∈) =
    ⇓-ref-dead dead (renameTarget-∋rep target α∈)

  renameTarget-∋rep : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ Δ′ ℒ}
      {α : TyVar Θ} {A : Ty Δ}
    → RenameTarget ρ Ψ Φ
    → Ψ ∋rep α ≔ A
    → Φ ∋rep α ≔ renameᵗ (toRenameᵗ ρ) A
  renameTarget-∋rep target (∋rep-of α∈ A⇓) =
    ∋rep-of (renameTarget-∋rep⁺ target α∈) (renameTarget-⇓ target A⇓)


renameTarget-insert : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ Δ′ ℒ}
  → RenameTarget ρ Ψ Φ
  → (Y : TyVar (suc Δ)) (α : TyVar Θ)
  → (inactive : Vec.lookup ℒ α ≡ false)
  → RenameTarget (insert↪ᵗ ρ Y)
      (Ψ ,begin[ Y ≔ α ]⟨ inactive ⟩)
      (Φ ,begin[ toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ α ]⟨ inactive ⟩)
renameTarget-insert {ρ = ρ} {Ψ = Ψ} {Φ = Φ} target Y α inactive =
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


⊢renameᵗᵐ-target : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ Δ′ ℒ} {Γ : TermCtx Δ}
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
      {inactive = inactive} α∈ c⊢ M⊢) =
  ⊢reveal (renameTarget-∋rep target α∈) conversion⊢ body⊢
  where
  ρ⁺ = insert↪ᵗ ρ Y
  Y′ = toRenameᵗ ρ⁺ Y

  body⊢ =
    ⊢renameᵗᵐ-target (renameTarget-insert target Y α inactive) M⊢

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
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} {α = α}
      slot∈ α∈ c⊢ M⊢) =
  ⊢conceal slot⊢ lookup⊢ conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  ended-target = target-end Y α target

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
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y} {α = α}
      slot∈ α∈ c⊢ M⊢) =
  ⊢conceal slot⊢ lookup⊢ conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  ended-target = target-end Y α target

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

⊢renameᵗᵐ : ∀ {Θ Δ Δ′} {ℒ : Vec.Vec Bool Θ} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ ℒ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ M ⦂ renameᵗ (toRenameᵗ ρ) A
⊢renameᵗᵐ = ⊢renameᵗᵐ-target canonical-target

------------------------------------------------------------------------
-- Literal regular-context weakening at zero
------------------------------------------------------------------------

renameCtx-wk-eq : ∀ {Δ} (Γ : TermCtx Δ)
  → renameCtx (toRenameᵗ wk↪ᵗ) Γ ≡ renameCtx suc Γ
renameCtx-wk-eq [] = refl
renameCtx-wk-eq (A ∷ Γ) =
  cong₂ _∷_ (renameᵗ-wk-eq A) (renameCtx-wk-eq Γ)

⊢weakenᵗᵐ : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ} {Γ : TermCtx Δ}
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

exts-∋ : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ} {Γ Γ′ : TermCtx Δ}
    {σ : Subst Θ Δ} {A : Ty Δ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Ψ ∣ Γ′ ⊢ σ x ⦂ B)
  → ∀ {x B}
  → A ∷ Γ ∋ x ⦂ B
  → Ψ ∣ A ∷ Γ′ ⊢ exts σ x ⦂ B
exts-∋ σ⊢ Z = ⊢` Z
exts-∋ σ⊢ (S x∈) = ⊢rename-suc (σ⊢ x∈)

liftˢ-∋ : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ} {Γ Γ′ : TermCtx Δ}
    {σ : Subst Θ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Ψ ∣ Γ′ ⊢ σ x ⦂ A)
  → ∀ {x A}
  → renameCtx suc Γ ∋ x ⦂ A
  → Ψ ,typ ∣ renameCtx suc Γ′ ⊢ liftˢ σ x ⦂ A
liftˢ-∋ σ⊢ x∈ with lookup-renameCtx-inv x∈
liftˢ-∋ σ⊢ x∈ | B , B∈ , refl = ⊢weakenᵗᵐ (σ⊢ B∈)

⊢subst : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ} {Γ Γ′ : TermCtx Δ}
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

⊢[] : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ} {Γ : TermCtx Δ}
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
    → (Y : TyVar (suc Δ)) (A⁺ : Ty⁺ Θ Δ)
    → renameᶠ⁺ ρ (begin⁺ Y A⁺) ≡ begin⁺ Y (renameᶠ⁺ ρ A⁺)
renameᶠ⁺-begin ρ Y (＇⁺ X) = refl
renameᶠ⁺-begin ρ Y (‵⁺ ι) = refl
renameᶠ⁺-begin ρ Y ★⁺ = refl
renameᶠ⁺-begin ρ Y (A⁺ ⇒⁺ B⁺) =
  cong₂ _⇒⁺_ (renameᶠ⁺-begin ρ Y A⁺)
    (renameᶠ⁺-begin ρ Y B⁺)
renameᶠ⁺-begin ρ Y (`∀⁺ A⁺) =
  cong `∀⁺ (renameᶠ⁺-begin ρ (suc Y) A⁺)
renameᶠ⁺-begin ρ Y (ref α) = refl

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
  → begin⁺ Y (wkᶠ⁺ A⁺) ≡ renameᵗ⁺ (punchIn Y) (wkᶠ⁺ A⁺)
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

lookup-setLive-same : ∀ {Θ} (L : Vec.Vec Bool Θ)
    (α : TyVar Θ) (live : Bool)
  → Vec.lookup (setLive L α live) α ≡ live
lookup-setLive-same Vec.[] () live
lookup-setLive-same (old Vec.∷ L) zero live = refl
lookup-setLive-same (old Vec.∷ L) (suc α) live =
  lookup-setLive-same L α live

lookup-setLive-other : ∀ {Θ} {L : Vec.Vec Bool Θ}
    {α query : TyVar Θ} {live : Bool}
  → α ≢ query
  → Vec.lookup (setLive L α live) query ≡ Vec.lookup L query
lookup-setLive-other {L = old Vec.∷ L} {α = zero} {query = zero}
    α≢query =
  ⊥-elim (α≢query refl)
lookup-setLive-other {L = old Vec.∷ L} {α = zero}
    {query = suc query} α≢query = refl
lookup-setLive-other {L = old Vec.∷ L} {α = suc α}
    {query = zero} α≢query = refl
lookup-setLive-other {L = old Vec.∷ L} {α = suc α}
    {query = suc query} {live = live} α≢query =
  lookup-setLive-other {L = L} {α = α} {query = query}
    {live = live} (λ eq → α≢query (cong suc eq))

setLive-current : ∀ {Θ} {L : Vec.Vec Bool Θ}
    {α : TyVar Θ} {live : Bool}
  → Vec.lookup L α ≡ live
  → setLive L α live ≡ L
setLive-current {L = Vec.[]} {α = ()} eq
setLive-current {L = old Vec.∷ L} {α = zero} refl = refl
setLive-current {L = old Vec.∷ L} {α = suc α} eq =
  cong (old Vec.∷_) (setLive-current eq)

setLive-overwrite : ∀ {Θ} (L : Vec.Vec Bool Θ)
    (α : TyVar Θ) (old new : Bool)
  → setLive (setLive L α old) α new ≡ setLive L α new
setLive-overwrite Vec.[] () old new
setLive-overwrite (current Vec.∷ L) zero old new = refl
setLive-overwrite (current Vec.∷ L) (suc α) old new =
  cong (current Vec.∷_) (setLive-overwrite L α old new)

renameᶠ⁺-wkᶠ⁺-⌜⌝ : ∀ {Θ Θ′ Δ} (ρ : TyVar Θ → TyVar Θ′)
    (A : Ty Δ)
  → renameᶠ⁺ (extᵗ ρ) (wkᶠ⁺ {Θ = Θ} ⌜ A ⌝)
    ≡ wkᶠ⁺ {Θ = Θ′} ⌜ A ⌝
renameᶠ⁺-wkᶠ⁺-⌜⌝ {Θ = Θ} {Θ′ = Θ′} ρ A =
  trans (cong (renameᶠ⁺ (extᵗ ρ))
    (renameᶠ⁺-⌜⌝ (suc {n = Θ}) A))
    (trans (renameᶠ⁺-⌜⌝ (extᵗ ρ) A)
      (sym (renameᶠ⁺-⌜⌝ (suc {n = Θ′}) A)))

data AnchorTarget : ∀ {Θ Θ′ Δ}
    {L : Vec.Vec Bool Θ} {L′ : Vec.Vec Bool Θ′}
    (ρ : TyVar Θ → TyVar Θ′)
  → TyEnv Θ Δ L → TyEnv Θ′ Δ L′ → Set where
  visible-shift-target : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
      {Ψ : TyEnv Θ Δ L} {B : Ty Δ}
      -----------------------------------------
    → AnchorTarget suc Ψ (Ψ ,:= B)

  anchor-target-typ : ∀ {Θ Θ′ Δ}
      {L : Vec.Vec Bool Θ} {L′ : Vec.Vec Bool Θ′}
      {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ L} {Φ : TyEnv Θ′ Δ L′}
      (Y : TyVar (suc Δ)) (α : TyVar Θ)
      {inactive : Vec.lookup L α ≡ false}
      {inactive′ : Vec.lookup L′ (ρ α) ≡ false}
    → AnchorTarget ρ Ψ Φ
      --------------------------------------------------
    → AnchorTarget ρ (Ψ ,begin[ Y ≔ α ]⟨ inactive ⟩)
        (Φ ,begin[ Y ≔ ρ α ]⟨ inactive′ ⟩)

  anchor-target-lexical : ∀ {Θ Θ′ Δ}
      {L : Vec.Vec Bool Θ} {L′ : Vec.Vec Bool Θ′}
      {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ L} {Φ : TyEnv Θ′ Δ L′}
    → AnchorTarget ρ Ψ Φ
      --------------------------------------------
    → AnchorTarget ρ (Ψ ,typ) (Φ ,typ)

  anchor-target-:= : ∀ {Θ Θ′ Δ}
      {L : Vec.Vec Bool Θ} {L′ : Vec.Vec Bool Θ′}
      {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ L} {Φ : TyEnv Θ′ Δ L′} {A : Ty Δ}
    → AnchorTarget ρ Ψ Φ
      -----------------------------------------------
    → AnchorTarget (extᵗ ρ) (Ψ ,:= A) (Φ ,:= A)

  anchor-target-end : ∀ {Θ Θ′ Δ}
      {L : Vec.Vec Bool Θ} {L′ : Vec.Vec Bool Θ′}
      {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ (suc Δ) L} {Φ : TyEnv Θ′ (suc Δ) L′}
      (Y : TyVar (suc Δ)) (α : TyVar Θ)
    → AnchorTarget ρ Ψ Φ
      --------------------------------------------------
    → AnchorTarget ρ (Ψ ,end[ Y ≔ α ]) (Φ ,end[ Y ≔ ρ α ])

  -- Reachable allocation mints the fresh ν and its sole begin together.
  anchor-target-allocate : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
      {Ψ : TyEnv Θ Δ L} {B : Ty Δ}
      -------------------------------------------------------------
    → AnchorTarget suc (Ψ ,typ)
        ((Ψ ,:= B) ,begin[ zero ≔ zero ]⟨ refl ⟩)

-- U19's sixth obstruction and U20's tightened allocation are subsumed by
-- the live-set index: a second begin for the freshly allocated anchor is
-- unrepresentable because its flag is already true.

anchorTarget-liveBit : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
    {L : Vec.Vec Bool Θ} {L′ : Vec.Vec Bool Θ′}
    {Ψ : TyEnv Θ Δ L} {Φ : TyEnv Θ′ Δ L′}
  → (∀ {α β} → ρ α ≡ ρ β → α ≡ β)
  → AnchorTarget ρ Ψ Φ
  → (query : TyVar Θ)
  → Vec.lookup L query ≡ Vec.lookup L′ (ρ query)
anchorTarget-liveBit ρ-inj visible-shift-target query = refl
anchorTarget-liveBit {ρ = ρ} ρ-inj
    (anchor-target-typ {L = L} {L′ = L′} Y anchor target) query
    with query ≟ anchor | ρ query ≟ ρ anchor
anchorTarget-liveBit ρ-inj
    (anchor-target-typ {L = L} {L′ = L′} Y anchor target) .anchor
    | yes refl | yes refl =
  trans (lookup-setLive-same L anchor true)
    (sym (lookup-setLive-same L′ _ true))
anchorTarget-liveBit ρ-inj
    (anchor-target-typ {L = L} {L′ = L′} Y anchor target) .anchor
    | yes refl | no image≢image = ⊥-elim (image≢image refl)
anchorTarget-liveBit ρ-inj
    (anchor-target-typ {L = L} {L′ = L′} Y anchor target) query
    | no query≢anchor | yes image-eq =
  ⊥-elim (query≢anchor (ρ-inj image-eq))
anchorTarget-liveBit ρ-inj
    (anchor-target-typ {L = L} {L′ = L′} Y anchor target) query
    | no query≢anchor | no image≢image =
  trans (lookup-setLive-other {L = L} {α = anchor} {query = query}
      (λ eq → query≢anchor (sym eq)))
    (trans (anchorTarget-liveBit ρ-inj target query)
      (sym (lookup-setLive-other {L = L′} {α = _} {query = _}
        (λ eq → image≢image (sym eq)))))
anchorTarget-liveBit ρ-inj (anchor-target-lexical target) query =
  anchorTarget-liveBit ρ-inj target query
anchorTarget-liveBit ρ-inj (anchor-target-:= target) zero = refl
anchorTarget-liveBit ρ-inj (anchor-target-:= target) (suc query) =
  anchorTarget-liveBit
    (λ eq → fin-suc-injective (ρ-inj (cong suc eq))) target query
anchorTarget-liveBit {ρ = ρ} ρ-inj
    (anchor-target-end {L = L} {L′ = L′} Y anchor target) query
    with query ≟ anchor | ρ query ≟ ρ anchor
anchorTarget-liveBit ρ-inj
    (anchor-target-end {L = L} {L′ = L′} Y anchor target) .anchor
    | yes refl | yes refl =
  trans (lookup-setLive-same L anchor false)
    (sym (lookup-setLive-same L′ _ false))
anchorTarget-liveBit ρ-inj
    (anchor-target-end {L = L} {L′ = L′} Y anchor target) .anchor
    | yes refl | no image≢image = ⊥-elim (image≢image refl)
anchorTarget-liveBit ρ-inj
    (anchor-target-end {L = L} {L′ = L′} Y anchor target) query
    | no query≢anchor | yes image-eq =
  ⊥-elim (query≢anchor (ρ-inj image-eq))
anchorTarget-liveBit ρ-inj
    (anchor-target-end {L = L} {L′ = L′} Y anchor target) query
    | no query≢anchor | no image≢image =
  trans (lookup-setLive-other {L = L} {α = anchor} {query = query}
      (λ eq → query≢anchor (sym eq)))
    (trans (anchorTarget-liveBit ρ-inj target query)
      (sym (lookup-setLive-other {L = L′} {α = _} {query = _}
        (λ eq → image≢image (sym eq)))))
anchorTarget-liveBit ρ-inj anchor-target-allocate query = refl

anchorTarget-liveSlot? : ∀ {Θ Θ′ Δ}
    {ρ : TyVar Θ → TyVar Θ′}
    {L : Vec.Vec Bool Θ} {L′ : Vec.Vec Bool Θ′}
    {Ψ : TyEnv Θ Δ L} {Φ : TyEnv Θ′ Δ L′}
  → (∀ {α β} → ρ α ≡ ρ β → α ≡ β)
  → AnchorTarget ρ Ψ Φ
  → (query : TyVar Θ)
  → liveSlot? Φ (ρ query) ≡ liveSlot? Ψ query
anchorTarget-liveSlot? ρ-inj visible-shift-target query = refl
anchorTarget-liveSlot? {ρ = ρ} ρ-inj
    (anchor-target-typ Y anchor target) query
    with query ≟ anchor | ρ query ≟ ρ anchor
anchorTarget-liveSlot? ρ-inj
    (anchor-target-typ Y anchor target) .anchor
    | yes refl | yes refl = refl
anchorTarget-liveSlot? ρ-inj
    (anchor-target-typ Y anchor target) .anchor
    | yes refl | no image≢image = ⊥-elim (image≢image refl)
anchorTarget-liveSlot? ρ-inj
    (anchor-target-typ Y anchor target) query
    | no query≢anchor | yes image-eq =
  ⊥-elim (query≢anchor (ρ-inj image-eq))
anchorTarget-liveSlot? ρ-inj
    (anchor-target-typ Y anchor target) query
    | no query≢anchor | no image≢image =
  cong (mapMaybe (punchIn Y))
    (anchorTarget-liveSlot? ρ-inj target query)
anchorTarget-liveSlot? ρ-inj (anchor-target-lexical target) query =
  cong (mapMaybe suc) (anchorTarget-liveSlot? ρ-inj target query)
anchorTarget-liveSlot? ρ-inj (anchor-target-:= target) zero = refl
anchorTarget-liveSlot? ρ-inj (anchor-target-:= target) (suc query) =
  anchorTarget-liveSlot?
    (λ eq → fin-suc-injective (ρ-inj (cong suc eq))) target query
anchorTarget-liveSlot? {ρ = ρ} ρ-inj
    (anchor-target-end Y anchor target) query
    with query ≟ anchor | ρ query ≟ ρ anchor
anchorTarget-liveSlot? ρ-inj
    (anchor-target-end Y anchor target) .anchor
    | yes refl | yes refl = refl
anchorTarget-liveSlot? ρ-inj
    (anchor-target-end Y anchor target) .anchor
    | yes refl | no image≢image = ⊥-elim (image≢image refl)
anchorTarget-liveSlot? ρ-inj
    (anchor-target-end Y anchor target) query
    | no query≢anchor | yes image-eq =
  ⊥-elim (query≢anchor (ρ-inj image-eq))
anchorTarget-liveSlot? ρ-inj
    (anchor-target-end Y anchor target) query
    | no query≢anchor | no image≢image
    rewrite anchorTarget-liveSlot? ρ-inj target query = refl
anchorTarget-liveSlot? ρ-inj anchor-target-allocate query = refl

anchorTarget-∋typ : ∀ {Θ Θ′ Δ} {ℒ : Vec.Vec Bool Θ} {ℒ′ : Vec.Vec Bool Θ′} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ′ Δ ℒ′}
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
anchorTarget-∋typ ρ-inj anchor-target-allocate
    (skip-typ Y∈) =
  skip-begin (skip-nu-binding Y∈)
anchorTarget-∋typ ρ-inj (anchor-target-:= target)
    (skip-nu-binding Y∈) =
  skip-nu-binding
    (anchorTarget-∋typ
      (λ eq → fin-suc-injective (ρ-inj (cong suc eq)))
      target Y∈)
anchorTarget-∋typ ρ-inj (anchor-target-end Y anchor target)
    (skip-end Y∈) =
  skip-end (anchorTarget-∋typ ρ-inj target Y∈)

anchorTarget-∋rep⁺ : ∀ {Θ Θ′ Δ} {ℒ : Vec.Vec Bool Θ} {ℒ′ : Vec.Vec Bool Θ′} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ′ Δ ℒ′}
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
    (sym (renameᶠ⁺-begin ρ Y A⁺))
    (skip-begin (anchorTarget-∋rep⁺ ρ-inj target α∈))
anchorTarget-∋rep⁺ {ρ = ρ} ρ-inj (anchor-target-lexical target)
    (skip-typ {a = a} α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (renameᵗ⁺-renameᶠ⁺ suc ρ _)
    (skip-typ (anchorTarget-∋rep⁺ ρ-inj target α∈))
anchorTarget-∋rep⁺ ρ-inj anchor-target-allocate
    (skip-typ {a = a} α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺) payload-eq
    (skip-begin (S α∈))
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
anchorTarget-∋rep⁺ {ρ = ρ} ρ-inj
    (anchor-target-end Y anchor target)
    (skip-end {β = .anchor} {a = a} {A⁺ = A⁺} α∈) =
  subst≡ (λ B⁺ → _ ∋rep⁺ _ ≔ B⁺)
    (sym (renameᶠ⁺-end ρ Y anchor A⁺))
    (skip-end (anchorTarget-∋rep⁺ ρ-inj target α∈))

mutual
  anchorTarget-⇓ : ∀ {Θ Θ′ Δ} {ℒ : Vec.Vec Bool Θ} {ℒ′ : Vec.Vec Bool Θ′} {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ′ Δ ℒ′}
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
  anchorTarget-⇓ ρ-inj target
      (⇓-ref-live {β = query} {Y = Y} live) =
    ⇓-ref-live
      (trans (anchorTarget-liveSlot? ρ-inj target query) live)
  anchorTarget-⇓ ρ-inj target
      (⇓-ref-dead {β = query} dead α∈) =
    ⇓-ref-dead
      (trans (sym (anchorTarget-liveBit ρ-inj target query)) dead)
      (anchorTarget-∋rep ρ-inj target α∈)

  anchorTarget-∋rep : ∀ {Θ Θ′ Δ} {ℒ : Vec.Vec Bool Θ} {ℒ′ : Vec.Vec Bool Θ′} {ρ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ′ Δ ℒ′}
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

⊢renameᶿ-target : ∀ {Θ Θ′ Δ} {ℒ : Vec.Vec Bool Θ} {ℒ′ : Vec.Vec Bool Θ′} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ ℒ} {Φ : TyEnv Θ′ Δ ℒ′} {Γ : TermCtx Δ}
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
⊢renameᶿ-target ρ-inj target
    (⊢reveal {α = α} {inactive = inactive} α∈ c⊢ M⊢) =
  ⊢reveal (anchorTarget-∋rep ρ-inj target α∈) c⊢
    (⊢renameᶿ-target ρ-inj
      (anchor-target-typ _ α {inactive = inactive}
        {inactive′ = target-inactive} target) M⊢)
  where
  target-inactive =
    trans (sym (anchorTarget-liveBit ρ-inj target α)) inactive
⊢renameᶿ-target ρ-inj target
    (⊢conceal {Y = Y} {α = α} slot∈ α∈ c⊢ M⊢) =
  ⊢conceal (anchorTarget-∋typ ρ-inj target slot∈)
    (anchorTarget-∋rep ρ-inj ended-target α∈) c⊢
    (⊢renameᶿ-target ρ-inj ended-target M⊢)
  where
  ended-target = anchor-target-end Y α target
⊢renameᶿ-target ρ-inj target ⊢blame = ⊢blame

⊢shiftᶿ : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A B : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
    ---------------------------
  → Ψ ,:= B ∣ Γ ⊢ shiftᶿ M ⦂ A
⊢shiftᶿ M⊢ = ⊢renameᶿ-target fin-suc-injective
  visible-shift-target M⊢

⊢allocate-lexical : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ} {Γ : TermCtx (suc Δ)}
    {M : Term Θ (suc Δ)} {A : Ty (suc Δ)} {C : Ty Δ}
  → Ψ ,typ ∣ Γ ⊢ M ⦂ A
    ---------------------------------------------------
  → (Ψ ,:= C) ,begin[ zero ≔ zero ]⟨ refl ⟩
      ∣ Γ ⊢ shiftᶿ M ⦂ A
⊢allocate-lexical M⊢ = ⊢renameᶿ-target fin-suc-injective
  anchor-target-allocate M⊢

------------------------------------------------------------------------
∋:=-shift : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ}
    {α : TyVar Θ} {A B : Ty Δ}
  → Ψ ∋rep α ≔ A
  → (Ψ ,:= B) ∋rep (suc α) ≔ A
∋:=-shift =
  anchorTarget-∋rep fin-suc-injective visible-shift-target

∋rep-allocate-lexical : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ}
    {α : TyVar Θ} {A B : Ty Δ}
  → Ψ ∋rep α ≔ A
  → (Ψ ,:= B) ,begin[ zero ≔ zero ]⟨ refl ⟩
      ∋rep suc α ≔ ⇑ᵗ A
∋rep-allocate-lexical {Ψ = Ψ} {α = α} {A = A} α∈ =
  anchorTarget-∋rep fin-suc-injective
    anchor-target-allocate
    weakened
  where
  weaken-eq : ∀ X → toRenameᵗ wk↪ᵗ X ≡ suc X
  weaken-eq = toRename-wk-eq

  weakened : Ψ ,typ ∋rep α ≔ ⇑ᵗ A
  weakened =
    subst≡ (λ C → Ψ ,typ ∋rep α ≔ C)
      (renameᵗ-cong A weaken-eq)
      (renameTarget-∋rep literal-wk-target α∈)

∋rep-typ : ∀ {Θ Δ} {ℒ : Vec.Vec Bool Θ} {Ψ : TyEnv Θ Δ ℒ}
    {α : TyVar Θ} {A : Ty Δ}
  → Ψ ∋rep α ≔ A
  → Ψ ,typ ∋rep α ≔ ⇑ᵗ A
∋rep-typ {Ψ = Ψ} {α = α} {A = A} α∈ =
  subst≡ (λ C → Ψ ,typ ∋rep α ≔ C)
    (renameᵗ-cong A toRename-wk-eq)
    (renameTarget-∋rep literal-wk-target α∈)

------------------------------------------------------------------------
-- Lookup determinism under the intrinsic live-set index
------------------------------------------------------------------------

punchIn-injectiveᵗ : ∀ {Δ} (X : TyVar (suc Δ)) {Y Z : TyVar Δ}
  → punchIn X Y ≡ punchIn X Z
  → Y ≡ Z
punchIn-injectiveᵗ zero eq = fin-suc-injective eq
punchIn-injectiveᵗ (suc X) {zero} {zero} eq = refl
punchIn-injectiveᵗ (suc X) {zero} {suc z} ()
punchIn-injectiveᵗ (suc X) {suc Y} {zero} ()
punchIn-injectiveᵗ (suc X) {suc Y} {suc z} eq =
  cong suc (punchIn-injectiveᵗ X (fin-suc-injective eq))

begin-∋typ-view : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    {Ψ : TyEnv Θ Δ L} {X Z : TyVar (suc Δ)} {α β : TyVar Θ}
    {inactive : Vec.lookup L β ≡ false}
  → Ψ ,begin[ X ≔ β ]⟨ inactive ⟩ ∋typ Z ≔ α
  → (Z ≡ X × α ≡ β)
    ⊎ ∃[ Y ] (Z ≡ punchIn X Y × Ψ ∋typ Y ≔ α)
begin-∋typ-view found-begin = inj₁ (refl , refl)
begin-∋typ-view (skip-begin {Y = Y} Y∈) =
  inj₂ (Y , refl , Y∈)

∋typ-unique : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    {Ψ : TyEnv Θ Δ L} {X : TyVar Δ} {α β : TyVar Θ}
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

setLive-same-true : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    (environment : TyEnv Θ Δ L) (bound : TyVar Θ)
  → Vec.lookup (setLive L bound true) bound ≡ true
setLive-same-true {L = L} environment bound =
  lookup-setLive-same L bound true

setLive-other-true : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    (environment : TyEnv Θ Δ L) {bound query : TyVar Θ}
    {live : Bool}
  → bound ≢ query
  → Vec.lookup L query ≡ true
  → Vec.lookup (setLive L bound live) query ≡ true
setLive-other-true {L = L} environment {bound = bound}
    {query = query} {live = live} bound≢query query-live =
  trans (lookup-setLive-other {L = L} {α = bound} {query = query}
    {live = live} bound≢query) query-live

liveSlot?-sound : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    {β : TyVar Θ} {Y : TyVar Δ}
  → (environment : TyEnv Θ Δ L)
  → liveSlot? environment β ≡ just Y
  → Vec.lookup L β ≡ true
liveSlot?-sound {β = ()} ∅ eq
liveSlot?-sound {β = zero} (Ψ ,:= A) ()
liveSlot?-sound {β = suc query} (Ψ ,:= A) eq =
  liveSlot?-sound Ψ eq
liveSlot?-sound {β = query}
    (Ψ ,begin[ slot ≔ bound ]⟨ inactive ⟩) eq
    with query ≟ bound
liveSlot?-sound {β = .bound}
    (Ψ ,begin[ slot ≔ bound ]⟨ inactive ⟩) refl | yes refl =
  setLive-same-true Ψ bound
liveSlot?-sound {β = query}
    (Ψ ,begin[ slot ≔ bound ]⟨ inactive ⟩) eq | no query≢bound
    with liveSlot? Ψ query in slot-eq
liveSlot?-sound {β = query}
    (Ψ ,begin[ slot ≔ bound ]⟨ inactive ⟩) ()
    | no query≢bound | nothing
liveSlot?-sound {β = query}
    (Ψ ,begin[ slot ≔ bound ]⟨ inactive ⟩) refl
    | no query≢bound | just Y =
  setLive-other-true Ψ
    (λ bound≡query → query≢bound (sym bound≡query))
    (liveSlot?-sound Ψ slot-eq)
liveSlot?-sound {β = query} (Ψ ,typ) eq
    with liveSlot? Ψ query in slot-eq
liveSlot?-sound {β = query} (Ψ ,typ) () | nothing
liveSlot?-sound {β = query} (Ψ ,typ) refl | just Y =
  liveSlot?-sound Ψ slot-eq
liveSlot?-sound {β = query} (Ψ ,end[ slot ≔ bound ]) eq
    with query ≟ bound
liveSlot?-sound {β = .bound} (Ψ ,end[ slot ≔ bound ]) ()
    | yes refl
liveSlot?-sound {β = query} (Ψ ,end[ slot ≔ bound ]) eq
    | no query≢bound with liveSlot? Ψ query in slot-eq
liveSlot?-sound {β = query} (Ψ ,end[ slot ≔ bound ]) ()
    | no query≢bound | nothing
liveSlot?-sound {β = query} (Ψ ,end[ slot ≔ bound ]) eq
    | no query≢bound | just Y with slot ≟ Y
liveSlot?-sound {β = query} (Ψ ,end[ slot ≔ bound ]) ()
    | no query≢bound | just .slot | yes refl
liveSlot?-sound {β = query} (Ψ ,end[ slot ≔ bound ]) refl
    | no query≢bound | just Y | no slot≢Y =
  setLive-other-true Ψ
    (λ bound≡query → query≢bound (sym bound≡query))
    (liveSlot?-sound Ψ slot-eq)

∋rep⁺-unique : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    {Ψ : TyEnv Θ Δ L} {α : TyVar Θ} {A⁺ B⁺ : Ty⁺ Θ Δ}
  → Ψ ∋rep⁺ α ≔ A⁺
  → Ψ ∋rep⁺ α ≔ B⁺
  → A⁺ ≡ B⁺
∋rep⁺-unique Z Z = refl
∋rep⁺-unique (S A∈) (S B∈) =
  cong wkᶠ⁺ (∋rep⁺-unique A∈ B∈)
∋rep⁺-unique (skip-begin {Y = Y} A∈) (skip-begin B∈) =
  cong (begin⁺ Y) (∋rep⁺-unique A∈ B∈)
∋rep⁺-unique (skip-typ A∈) (skip-typ B∈) =
  cong typ⁺ (∋rep⁺-unique A∈ B∈)
∋rep⁺-unique (skip-end {Y = Y} {β = bound} A∈) (skip-end B∈) =
  cong (end⁺ Y bound) (∋rep⁺-unique A∈ B∈)

mutual
  ⇓-unique : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
      {Ψ : TyEnv Θ Δ L} {A⁺ : Ty⁺ Θ Δ} {A B : Ty Δ}
    → Ψ ⊢ A⁺ ⇓ A
    → Ψ ⊢ A⁺ ⇓ B
    → A ≡ B
  ⇓-unique ⇓-var ⇓-var = refl
  ⇓-unique ⇓-base ⇓-base = refl
  ⇓-unique ⇓-star ⇓-star = refl
  ⇓-unique (⇓-fun A⇓ B⇓) (⇓-fun A⇓′ B⇓′) =
    cong₂ _⇒_ (⇓-unique A⇓ A⇓′) (⇓-unique B⇓ B⇓′)
  ⇓-unique (⇓-all A⇓) (⇓-all B⇓) =
    cong `∀ (⇓-unique A⇓ B⇓)
  ⇓-unique (⇓-ref-live live₁) (⇓-ref-live live₂)
      with trans (sym live₁) live₂
  ⇓-unique (⇓-ref-live live₁) (⇓-ref-live live₂) | refl = refl
  ⇓-unique {Ψ = Ψ} (⇓-ref-live live) (⇓-ref-dead dead B∈)
      with trans (sym (liveSlot?-sound Ψ live)) dead
  ⇓-unique {Ψ = Ψ} (⇓-ref-live live) (⇓-ref-dead dead B∈) | ()
  ⇓-unique {Ψ = Ψ} (⇓-ref-dead dead A∈) (⇓-ref-live live)
      with trans (sym dead) (liveSlot?-sound Ψ live)
  ⇓-unique {Ψ = Ψ} (⇓-ref-dead dead A∈) (⇓-ref-live live) | ()
  ⇓-unique (⇓-ref-dead dead₁ A∈) (⇓-ref-dead dead₂ B∈) =
    ∋rep-unique A∈ B∈

  ∋rep-unique : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
      {Ψ : TyEnv Θ Δ L} {α : TyVar Θ} {A B : Ty Δ}
    → Ψ ∋rep α ≔ A
    → Ψ ∋rep α ≔ B
    → A ≡ B
  ∋rep-unique (∋rep-of A∈ A⇓) (∋rep-of B∈ B⇓)
      with ∋rep⁺-unique A∈ B∈
  ∋rep-unique (∋rep-of A∈ A⇓) (∋rep-of B∈ B⇓) | refl =
    ⇓-unique A⇓ B⇓

⇓-⌜⌝ : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    {Ψ : TyEnv Θ Δ L} {A : Ty Δ}
  → Ψ ⊢ ⌜ A ⌝ ⇓ A
⇓-⌜⌝ {A = ＇ X} = ⇓-var
⇓-⌜⌝ {A = ‵ ι} = ⇓-base
⇓-⌜⌝ {A = ★} = ⇓-star
⇓-⌜⌝ {A = A ⇒ B} = ⇓-fun ⇓-⌜⌝ ⇓-⌜⌝
⇓-⌜⌝ {A = `∀ A} = ⇓-all ⇓-⌜⌝

∋rep-here : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    {Ψ : TyEnv Θ Δ L} {A : Ty Δ}
  → Ψ ,:= A ∋rep zero ≔ A
∋rep-here {Θ = Θ} {Ψ = Ψ} {A = A} =
  ∋rep-of Z
    (subst≡ (λ A⁺ → Ψ ,:= A ⊢ A⁺ ⇓ A)
      (sym (renameᶠ⁺-⌜⌝ (suc {n = Θ}) A)) ⇓-⌜⌝)

∋rep-here-begin : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
    {Ψ : TyEnv Θ Δ L} {A : Ty Δ} {Y : TyVar (suc Δ)}
    {α : TyVar (suc Θ)}
    {inactive : Vec.lookup (false Vec.∷ L) α ≡ false}
  → (Ψ ,:= A) ,begin[ Y ≔ α ]⟨ inactive ⟩
      ∋rep zero ≔ wkᵗ Y A
∋rep-here-begin {Θ = Θ} {Ψ = Ψ} {A = A} {Y = Y}
    {α = anchor} {inactive = inactive} =
  ∋rep-of (skip-begin Z)
    (subst≡ (λ A⁺ →
      (Ψ ,:= A) ,begin[ Y ≔ anchor ]⟨ inactive ⟩
        ⊢ A⁺ ⇓ wkᵗ Y A)
      (sym (trans (cong (begin⁺ Y)
        (renameᶠ⁺-⌜⌝ (suc {n = Θ}) A))
        (begin⁺-⌜⌝ Y A))) ⇓-⌜⌝)
