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

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

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
    entry anchor : TyVar Θ

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

delete-delete↪ᵗ : ∀ {Δ Δ′} (ρ : suc (suc Δ) ↪ᵗ suc (suc Δ′))
    (X Y : TyVar (suc (suc Δ)))
    (X≢Y : X ≢ Y) (Y≢X : Y ≢ X)
  → delete↪ᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y)
    ≡ delete↪ᵗ (delete↪ᵗ ρ Y) (punchOut Y X Y≢X)
delete-delete↪ᵗ (keep ρ) zero zero X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ (keep ρ) zero (suc Y) X≢Y Y≢X = refl
delete-delete↪ᵗ (keep ρ) (suc X) zero X≢Y Y≢X = refl
delete-delete↪ᵗ {Δ′ = zero} (keep (keep empty))
    (suc zero) (suc zero) X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ = zero} {Δ′ = suc Δ′}
    (keep (keep ρ)) (suc zero) (suc zero) X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ = zero} {Δ′ = suc Δ′}
    (keep (skip ρ)) (suc zero) (suc zero) X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (keep ρ)) (suc X) (suc Y) X≢Y Y≢X
    rewrite delete-keep-suc (keep ρ) X
      | delete-keep-suc (keep ρ) Y
      | delete-keep-suc (delete↪ᵗ (keep ρ) X)
          (punchOut X Y (λ eq → X≢Y (cong suc eq)))
      | delete-keep-suc (delete↪ᵗ (keep ρ) Y)
          (punchOut Y X (λ eq → Y≢X (cong suc eq))) =
  cong keep (delete-delete↪ᵗ (keep ρ) X Y
    (λ eq → X≢Y (cong suc eq))
    (λ eq → Y≢X (cong suc eq)))
delete-delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep (skip ρ)) (suc X) (suc Y) X≢Y Y≢X
    rewrite delete-keep-suc (skip ρ) X
      | delete-keep-suc (skip ρ) Y
      | delete-keep-suc (delete↪ᵗ (skip ρ) X)
          (punchOut X Y (λ eq → X≢Y (cong suc eq)))
      | delete-keep-suc (delete↪ᵗ (skip ρ) Y)
          (punchOut Y X (λ eq → Y≢X (cong suc eq))) =
  cong keep (delete-delete↪ᵗ (skip ρ) X Y
    (λ eq → X≢Y (cong suc eq))
    (λ eq → Y≢X (cong suc eq)))
delete-delete↪ᵗ (skip ρ) zero zero X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ′ = suc Δ′}
    (skip (keep ρ)) zero (suc Y) X≢Y Y≢X
    rewrite delete-skip (keep ρ) zero
      | delete-skip (keep ρ) (suc Y)
      | delete-skip (delete↪ᵗ (keep ρ) zero) Y
      | delete-skip (delete↪ᵗ (keep ρ) (suc Y)) zero =
  cong skip (delete-delete↪ᵗ (keep ρ) zero (suc Y) X≢Y Y≢X)
delete-delete↪ᵗ {Δ′ = suc Δ′}
    (skip (skip ρ)) zero (suc Y) X≢Y Y≢X
    rewrite delete-skip (skip ρ) zero
      | delete-skip (skip ρ) (suc Y)
      | delete-skip (delete↪ᵗ (skip ρ) zero) Y
      | delete-skip (delete↪ᵗ (skip ρ) (suc Y)) zero =
  cong skip (delete-delete↪ᵗ (skip ρ) zero (suc Y) X≢Y Y≢X)
delete-delete↪ᵗ {Δ′ = suc Δ′}
    (skip (keep ρ)) (suc X) zero X≢Y Y≢X
    rewrite delete-skip (keep ρ) (suc X)
      | delete-skip (keep ρ) zero
      | delete-skip (delete↪ᵗ (keep ρ) (suc X)) zero
      | delete-skip (delete↪ᵗ (keep ρ) zero) X =
  cong skip (delete-delete↪ᵗ (keep ρ) (suc X) zero X≢Y Y≢X)
delete-delete↪ᵗ {Δ′ = suc Δ′}
    (skip (skip ρ)) (suc X) zero X≢Y Y≢X
    rewrite delete-skip (skip ρ) (suc X)
      | delete-skip (skip ρ) zero
      | delete-skip (delete↪ᵗ (skip ρ) (suc X)) zero
      | delete-skip (delete↪ᵗ (skip ρ) zero) X =
  cong skip (delete-delete↪ᵗ (skip ρ) (suc X) zero X≢Y Y≢X)
delete-delete↪ᵗ {Δ = zero} {Δ′ = suc Δ′}
    (skip (keep ρ)) (suc zero) (suc zero) X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ = zero} {Δ′ = suc Δ′}
    (skip (skip ρ)) (suc zero) (suc zero) X≢Y Y≢X =
  ⊥-elim (X≢Y refl)
delete-delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′}
    (skip (keep ρ)) (suc X) (suc Y) X≢Y Y≢X
    rewrite delete-skip (keep ρ) (suc X)
      | delete-skip (keep ρ) (suc Y)
      | delete-skip (delete↪ᵗ (keep ρ) (suc X))
          (suc (punchOut X Y (λ eq → X≢Y (cong suc eq))))
      | delete-skip (delete↪ᵗ (keep ρ) (suc Y))
          (suc (punchOut Y X (λ eq → Y≢X (cong suc eq)))) =
  cong skip (delete-delete↪ᵗ (keep ρ) (suc X) (suc Y) X≢Y Y≢X)
delete-delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′}
    (skip (skip ρ)) (suc X) (suc Y) X≢Y Y≢X
    rewrite delete-skip (skip ρ) (suc X)
      | delete-skip (skip ρ) (suc Y)
      | delete-skip (delete↪ᵗ (skip ρ) (suc X))
          (suc (punchOut X Y (λ eq → X≢Y (cong suc eq))))
      | delete-skip (delete↪ᵗ (skip ρ) (suc Y))
          (suc (punchOut Y X (λ eq → Y≢X (cong suc eq)))) =
  cong skip (delete-delete↪ᵗ (skip ρ) (suc X) (suc Y) X≢Y Y≢X)

rename-resolve-var : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (C : Ty Δ) (X : TyVar (suc Δ))
  → renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) (resolveSubᵗ Y C X)
    ≡ resolveSubᵗ (toRenameᵗ ρ Y)
        (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) C)
        (toRenameᵗ ρ X)
rename-resolve-var ρ Y C X
    with Y ≟ X | toRenameᵗ ρ Y ≟ toRenameᵗ ρ X
rename-resolve-var ρ Y C .Y | yes refl | yes refl = refl
rename-resolve-var ρ Y C .Y | yes refl | no Y≢Y =
  ⊥-elim (Y≢Y refl)
rename-resolve-var ρ Y C X | no Y≢X | yes eq =
  ⊥-elim (Y≢X (toRenameᵗ-injective ρ eq))
rename-resolve-var ρ Y C X | no Y≢X | no ρY≢ρX =
  cong ＇_ (rename-punchOut ρ Y X Y≢X ρY≢ρX)

rename-resolve : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (C : Ty Δ) (A : Ty (suc Δ))
  → renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y))
      (substᵗ (resolveSubᵗ Y C) A)
    ≡ substᵗ
        (resolveSubᵗ (toRenameᵗ ρ Y)
          (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) C))
        (renameᵗ (toRenameᵗ ρ) A)
rename-resolve ρ Y C A =
  trans (renameᵗ-subst (toRenameᵗ (delete↪ᵗ ρ Y))
      (resolveSubᵗ Y C) A)
    (trans (substᵗ-cong A (rename-resolve-var ρ Y C))
      (sym (substᵗ-rename
        (resolveSubᵗ (toRenameᵗ ρ Y)
          (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y)) C))
        (toRenameᵗ ρ) A)))

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

rename-∋rep : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {Ψ : TyEnv Θ Δ} {α : TyVar Θ} {A : Ty Δ}
  → Ψ ∋rep α ≔ A
  → renameTyEnv ρ Ψ ∋rep α ≔
      renameᵗ (toRenameᵗ ρ) A
rename-∋rep ρ Z = Z
rename-∋rep ρ (S α∈) = S (rename-∋rep ρ α∈)
rename-∋rep ρ@(keep η)
    (skip-begin {A = A} {Y = Y} α∈) =
  subst≡
    (λ D → _ ∋rep _ ≔ D)
    (sym (rename-delete-wk ρ Y A))
    (skip-begin (rename-∋rep (delete↪ᵗ ρ Y) α∈))
rename-∋rep ρ@(skip η)
    (skip-begin {A = A} {Y = Y} α∈) =
  subst≡
    (λ D → _ ∋rep _ ≔ D)
    (sym (rename-delete-wk ρ Y A))
    (skip-begin (rename-∋rep (delete↪ᵗ ρ Y) α∈))
rename-∋rep (keep ρ) (skip-typ {A = A} α∈) =
  subst≡ (λ C → _ ∋rep _ ≔ C)
    (sym (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
      (renameᵗ-shift (toRenameᵗ ρ) A)))
    (skip-typ (rename-∋rep ρ α∈))
rename-∋rep (skip ρ) (skip-typ {A = A} α∈) =
  subst≡ (λ C → _ ∋rep _ ≔ C)
    (renameᵗ-comp (toRenameᵗ ρ) suc (⇑ᵗ A))
    (skip-typ (rename-∋rep ρ (skip-typ α∈)))
rename-∋rep ρ
    (skip-end {Ψ = Ψ} {Y = Y} {α = α} {a = a}
      {A = A} {B = B} {C = C} slot∈ rep∈ A∈ eq) =
  skip-end (rename-∋typ ρ⁺ slot∈) rep′ A′ eq′
  where
  ρ⁺ = insert↪ᵗ ρ Y
  Y′ = toRenameᵗ ρ⁺ Y
  deleted-eq = delete-insert↪ᵗ ρ Y
  rep′ = subst≡
    (λ D → renameTyEnv ρ⁺ Ψ ∋rep α ≔ D)
    (rename-insert-wk ρ Y C)
    (rename-∋rep ρ⁺ rep∈)
  A′ = rename-∋rep ρ⁺ A∈
  resolved-rename =
    subst≡
      (λ η →
        renameᵗ (toRenameᵗ η) (substᵗ (resolveSubᵗ Y C) A)
        ≡ substᵗ (resolveSubᵗ Y′ (renameᵗ (toRenameᵗ η) C))
            (renameᵗ (toRenameᵗ ρ⁺) A))
      deleted-eq (rename-resolve ρ⁺ Y C A)
  eq′ : substᵗ (resolveSubᵗ Y′
      (renameᵗ (toRenameᵗ ρ) C))
      (renameᵗ (toRenameᵗ ρ⁺) A)
    ≡ renameᵗ (toRenameᵗ ρ) B
  eq′ =
    trans (sym resolved-rename)
      (cong (renameᵗ (toRenameᵗ ρ)) eq)


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

renameTarget-∋rep : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ Δ′}
    {α : TyVar Θ} {A : Ty Δ}
  → RenameTarget ρ Ψ Φ
  → Ψ ∋rep α ≔ A
  → Φ ∋rep α ≔
      renameᵗ (toRenameᵗ ρ) A
renameTarget-∋rep {ρ = ρ} canonical-target α∈ = rename-∋rep ρ α∈
renameTarget-∋rep {A = A} literal-wk-target α∈ =
  subst≡ (λ C → _ ∋rep _ ≔ C) (sym (renameᵗ-wk-eq A))
    (skip-typ α∈)
renameTarget-∋rep {ρ = ρ} (target-typ X anchor target)
    (skip-begin {A = A} α∈) =
  subst≡ (λ C → _ ∋rep _ ≔ C)
    (sym (rename-delete-wk ρ X A))
    (skip-begin (renameTarget-∋rep target α∈))
renameTarget-∋rep {ρ = keep ρ} (target-lexical target)
    (skip-typ {A = A} α∈) =
  subst≡ (λ C → _ ∋rep _ ≔ C)
    (sym (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq _))
      (renameᵗ-shift _ A)))
    (skip-typ (renameTarget-∋rep target α∈))
renameTarget-∋rep (target-:= target) Z = Z
renameTarget-∋rep (target-:= target) (S α∈) =
  S (renameTarget-∋rep target α∈)
renameTarget-∋rep {A = B}
    (target-end { ρ = ρ } Y target)
    (skip-end {A = A} {C = C} slot∈ rep∈ A∈ eq) =
  skip-end (renameTarget-∋typ target slot∈) rep′ A′ eq′
  where
  Y′ = toRenameᵗ ρ Y
  rep′ = subst≡
    (λ D → _ ∋rep _ ≔ D)
    (rename-delete-wk ρ Y C)
    (renameTarget-∋rep target rep∈)
  A′ = renameTarget-∋rep target A∈
  eq′ = trans (sym (rename-resolve ρ Y C A))
    (cong (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y))) eq)


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

unbegin-∋rep : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {X : TyVar (suc Δ)} {β a : TyVar Θ} {A : Ty (suc Δ)}
  → Ψ ,begin[ X ≔ β ] ∋rep a ≔ A
  → ∃[ B ] (Ψ ∋rep a ≔ B × A ≡ wkᵗ X B)
unbegin-∋rep (skip-begin {A = A} α∈) = A , α∈ , refl

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

∋rep-unique : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {α : TyVar Θ} {A B : Ty Δ}
  → Ψ ∋rep α ≔ A
  → Ψ ∋rep α ≔ B
  → A ≡ B
∋rep-unique Z Z = refl
∋rep-unique (S A∈) (S B∈) = ∋rep-unique A∈ B∈
∋rep-unique (skip-begin A∈) (skip-begin B∈) =
  cong (wkᵗ _) (∋rep-unique A∈ B∈)
∋rep-unique (skip-typ A∈) (skip-typ B∈) =
  cong ⇑ᵗ (∋rep-unique A∈ B∈)
∋rep-unique (skip-end {Y = X} {C = C} slot₁ rep₁ A∈ eq₁)
    (skip-end {C = D} slot₂ rep₂ B∈ eq₂)
    with ∋typ-unique slot₁ slot₂
∋rep-unique (skip-end {Y = X} {C = C} slot₁ rep₁ A∈ eq₁)
    (skip-end {C = D} slot₂ rep₂ B∈ eq₂) | refl
    with wkᵗ-injective X (∋rep-unique rep₁ rep₂)
       | ∋rep-unique A∈ B∈
∋rep-unique (skip-end {Y = X} {C = C} slot₁ rep₁ A∈ eq₁)
    (skip-end {C = .C} slot₂ rep₂ B∈ eq₂) | refl | refl | refl =
  trans (sym eq₁) eq₂

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
      {X : TyVar (suc Δ)} {β : TyVar (suc Θ)} {C : Ty Δ}
    → Ψ ∋rep zero ≔ C
    → SameTarget (Ψ ,begin[ X ≔ β ])
        (((Ψ ,begin[ zero ≔ zero ])
          ,begin[ suc X ≔ β ]) ,end[ zero ])

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

sameTarget-∋rep : ∀ {Θ Δ} {Ψ Φ : TyEnv Θ Δ}
    {α : TyVar Θ} {A : Ty Δ}
  → SameTarget Ψ Φ
  → Ψ ∋rep α ≔ A
  → Φ ∋rep α ≔ A
sameTarget-∋rep (same-bracket {X = X} {C = C} α∈) a∈ =
  skip-end found-begin (skip-begin α∈) (skip-begin a∈)
    (resolve-wkᵗ X C _)
sameTarget-∋rep same-unbracket
    (skip-end {Y = X} {C = C} slot∈ rep∈ a∈ eq)
    with unbegin-∋rep a∈
sameTarget-∋rep same-unbracket
    (skip-end {Y = X} {C = C} slot∈ rep∈ a∈ eq)
    | A , a∈′ , refl =
  subst≡ (λ B → _ ∋rep _ ≔ B)
    (trans (sym (resolve-wkᵗ X C A)) eq) a∈′
sameTarget-∋rep (same-fresh-before-begin {X = X} {C = C} fresh∈)
    (skip-begin {A = A} a∈) =
  skip-end (skip-begin found-begin) fresh-rep target-rep target-eq
  where
  fresh-rep = subst≡ (λ B → _ ∋rep zero ≔ B)
    (sym (resolve-wk-exchange X C))
    (skip-begin (skip-begin fresh∈))
  target-rep = skip-begin (skip-begin a∈)
  target-eq = trans
    (cong (substᵗ (resolveSubᵗ zero (wkᵗ X C)))
      (sym (resolve-wk-exchange X A)))
    (resolve-wkᵗ zero (wkᵗ X C) (wkᵗ X A))
sameTarget-∋rep (same-begin target) (skip-begin α∈) =
  skip-begin (sameTarget-∋rep target α∈)
sameTarget-∋rep (same-typ target) (skip-typ α∈) =
  skip-typ (sameTarget-∋rep target α∈)
sameTarget-∋rep (same-nu target) Z = Z
sameTarget-∋rep (same-nu target) (S α∈) =
  S (sameTarget-∋rep target α∈)
sameTarget-∋rep (same-end target)
    (skip-end slot∈ rep∈ a∈ eq) =
  skip-end (sameTarget-∋typ target slot∈)
    (sameTarget-∋rep target rep∈)
    (sameTarget-∋rep target a∈) eq

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

anchorTarget-∋rep : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ Δ} {Φ : TyEnv Θ′ Δ}
    {α : TyVar Θ} {A : Ty Δ}
  → (∀ {β γ} → ρ β ≡ ρ γ → β ≡ γ)
  → AnchorTarget ρ Ψ Φ
  → Ψ ∋rep α ≔ A
  → Φ ∋rep (ρ α) ≔ A
anchorTarget-∋rep ρ-inj visible-shift-target α∈ = S α∈
anchorTarget-∋rep ρ-inj (anchor-target-typ Y anchor target)
    (skip-begin α∈) =
  skip-begin (anchorTarget-∋rep ρ-inj target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-lexical target)
    (skip-typ α∈) =
  skip-typ (anchorTarget-∋rep ρ-inj target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-allocate target)
    (skip-typ α∈) =
  skip-begin (anchorTarget-∋rep ρ-inj target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-:= target) Z = Z
anchorTarget-∋rep ρ-inj (anchor-target-:= target) (S α∈) =
  S (anchorTarget-∋rep
    (λ eq → fin-suc-injective (ρ-inj (cong suc eq))) target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-end Y target)
    (skip-end slot∈ rep∈ A∈ eq) =
  skip-end (anchorTarget-∋typ ρ-inj target slot∈)
    (anchorTarget-∋rep ρ-inj target rep∈)
    (anchorTarget-∋rep ρ-inj target A∈) eq


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
∋:=-shift = S
