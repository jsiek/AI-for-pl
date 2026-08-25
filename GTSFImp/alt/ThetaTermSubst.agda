module alt.ThetaTermSubst where

-- File Charter:
--   * Proves typing preservation for parallel term renaming and
--     regular-context injection renaming in the Θ-indexed calculus.
--   * Defines the action of regular-context injections on binder telescopes
--     and proves typing preservation for the general term action
--     `renameᵗᵐ` from alt.ThetaReduction.
--   * Reveal scopes are retained verbatim between `,begin[_≔_]` and their
--     popping `,end[_]` markers.  This file transports the lazy, mode-indexed
--     lookups across regular and anchor renamings; it performs no telescope
--     entry surgery.

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
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
    A B C : Ty Δ
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

renamePending : ∀ {Δ Δ′}
  → Δ ↪ᵗ Δ′ → List (TyVar Δ) → List (TyVar Δ′)
renamePending ρ pending = map (toRenameᵗ ρ) pending

renameMode : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → Mode Δ → Mode Δ′
renameMode ρ (know pending) = know (renamePending ρ pending)
renameMode ρ opaq = opaq

transportPendingLookup : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {α : TyVar Θ} {A : Ty Δ} {pending pending′}
  → pending ≡ pending′
  → Ψ ∋rep[ know pending ] α ≔ A
  → Ψ ∋rep[ know pending′ ] α ≔ A
transportPendingLookup refl α∈ = α∈

renamePending-∈ : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {X : TyVar Δ} {pending : List (TyVar Δ)}
  → X ∈ pending
  → toRenameᵗ ρ X ∈ renamePending ρ pending
renamePending-∈ ρ (here refl) = here refl
renamePending-∈ ρ (there X∈) = there (renamePending-∈ ρ X∈)

renamePending-reflect-∈ : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {X : TyVar Δ} {pending : List (TyVar Δ)}
  → toRenameᵗ ρ X ∈ renamePending ρ pending
  → X ∈ pending
renamePending-reflect-∈ ρ {pending = []} ()
renamePending-reflect-∈ ρ {pending = Y ∷ pending} (here eq) =
  here (toRenameᵗ-injective ρ eq)
renamePending-reflect-∈ ρ {pending = Y ∷ pending} (there X∈) =
  there (renamePending-reflect-∈ ρ X∈)

renamePending-∉ : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {X : TyVar Δ} {pending : List (TyVar Δ)}
  → X ∉ pending
  → toRenameᵗ ρ X ∉ renamePending ρ pending
renamePending-∉ ρ X∉ X∈ =
  X∉ (renamePending-reflect-∈ ρ X∈)

rename-dropSlot : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (pending : List (TyVar (suc Δ)))
  → dropSlot (toRenameᵗ ρ Y) (renamePending ρ pending)
    ≡ renamePending (delete↪ᵗ ρ Y) (dropSlot Y pending)
rename-dropSlot ρ Y [] = refl
rename-dropSlot ρ Y (X ∷ pending)
    with Y ≟ X | toRenameᵗ ρ Y ≟ toRenameᵗ ρ X
rename-dropSlot ρ Y (.Y ∷ pending) | yes refl | yes refl =
  rename-dropSlot ρ Y pending
rename-dropSlot ρ Y (.Y ∷ pending) | yes refl | no Y≠Y =
  ⊥-elim (Y≠Y refl)
rename-dropSlot ρ Y (X ∷ pending) | no Y≠X | yes eq =
  ⊥-elim (Y≠X (toRenameᵗ-injective ρ eq))
rename-dropSlot ρ Y (X ∷ pending) | no Y≠X | no ρY≠ρX =
  cong₂ _∷_ (sym (rename-punchOut ρ Y X Y≠X ρY≠ρX))
    (rename-dropSlot ρ Y pending)

renamePending-punchIn : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ)) (pending : List (TyVar Δ))
  → renamePending (insert↪ᵗ ρ Y) (map (punchIn Y) pending)
    ≡ map (punchIn (toRenameᵗ (insert↪ᵗ ρ Y) Y))
        (renamePending ρ pending)
renamePending-punchIn ρ Y [] = refl
renamePending-punchIn ρ Y (X ∷ pending) =
  cong₂ _∷_ (insert-punchIn ρ Y X)
    (renamePending-punchIn ρ Y pending)

renamePending-insert : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (Y : TyVar (suc Δ)) (pending : List (TyVar Δ))
  → renamePending (insert↪ᵗ ρ Y)
      (Y ∷ map (punchIn Y) pending)
    ≡ toRenameᵗ (insert↪ᵗ ρ Y) Y
        ∷ map (punchIn (toRenameᵗ (insert↪ᵗ ρ Y) Y))
            (renamePending ρ pending)
renamePending-insert ρ Y pending =
  cong (toRenameᵗ (insert↪ᵗ ρ Y) Y ∷_)
    (renamePending-punchIn ρ Y pending)

renamePending-delete : ∀ {Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Y : TyVar (suc Δ)) (pending : List (TyVar Δ))
  → renamePending ρ (Y ∷ map (punchIn Y) pending)
    ≡ toRenameᵗ ρ Y ∷ map (punchIn (toRenameᵗ ρ Y))
        (renamePending (delete↪ᵗ ρ Y) pending)
renamePending-delete ρ Y [] = refl
renamePending-delete ρ Y (X ∷ pending) =
  cong₂ _∷_ refl
    (cong₂ _∷_ (delete-punchIn ρ Y X)
      (renamePending-delete-tail ρ Y pending))
  where
  renamePending-delete-tail : ∀ {Δ Δ′}
      (η : suc Δ ↪ᵗ suc Δ′) (slot′ : TyVar (suc Δ))
      (rest : List (TyVar Δ))
    → renamePending η (map (punchIn slot′) rest)
      ≡ map (punchIn (toRenameᵗ η slot′))
          (renamePending (delete↪ᵗ η slot′) rest)
  renamePending-delete-tail η slot′ [] = refl
  renamePending-delete-tail η slot′ (item ∷ rest) =
    cong₂ _∷_ (delete-punchIn η slot′ item)
      (renamePending-delete-tail η slot′ rest)

renamePending-keep-suc : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (pending : List (TyVar Δ))
  → renamePending (keep ρ) (map suc pending)
    ≡ map suc (renamePending ρ pending)
renamePending-keep-suc ρ [] = refl
renamePending-keep-suc ρ (X ∷ pending) =
  cong (suc (toRenameᵗ ρ X) ∷_)
    (renamePending-keep-suc ρ pending)

renamePending-skip : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    (pending : List (TyVar Δ))
  → renamePending (skip ρ) pending
    ≡ map suc (renamePending ρ pending)
renamePending-skip ρ [] = refl
renamePending-skip ρ (X ∷ pending) =
  cong (suc (toRenameᵗ ρ X) ∷_)
    (renamePending-skip ρ pending)

renamePending-wk : ∀ {Δ} (pending : List (TyVar Δ))
  → renamePending wk↪ᵗ pending ≡ map suc pending
renamePending-wk [] = refl
renamePending-wk (X ∷ pending) =
  cong₂ _∷_ (toRename-wk-eq X) (renamePending-wk pending)

rename-∋typ : ∀ {Θ Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {Ψ : TyEnv Θ Δ} {Y : TyVar Δ} {α : TyVar Θ}
  → Ψ ∋typ Y ≔ α
  → renameTyEnv ρ Ψ ∋typ toRenameᵗ ρ Y ≔ α
rename-∋typ (keep ρ) here-typ = here-typ
rename-∋typ (skip ρ) here-typ = here-typ
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
    {Ψ : TyEnv Θ Δ} {α : TyVar Θ} {A : Ty Δ} {mode}
  → Ψ ∋rep[ mode ] α ≔ A
  → renameTyEnv ρ Ψ ∋rep[ renameMode ρ mode ] α ≔
      renameᵗ (toRenameᵗ ρ) A
rename-∋rep ρ Z = Z
rename-∋rep ρ (S α∈) = S (rename-∋rep ρ α∈)
rename-∋rep ρ@(keep η)
    (skip-begin-pending {A = A} {Y = Y} {pending = pending}
      Y∈ α∈) =
  subst≡
    (λ D → _∋rep[_]_≔_ _ _ _ D)
    (sym (rename-delete-wk ρ Y A))
    (skip-begin-pending (renamePending-∈ ρ Y∈)
      (subst≡
        (λ pending′ → _∋rep[_]_≔_ _ (know pending′) _ _)
        (sym (rename-dropSlot ρ Y pending))
        (rename-∋rep (delete↪ᵗ ρ Y) α∈)))
rename-∋rep ρ@(skip η)
    (skip-begin-pending {A = A} {Y = Y} {pending = pending}
      Y∈ α∈) =
  subst≡
    (λ D → _∋rep[_]_≔_ _ _ _ D)
    (sym (rename-delete-wk ρ Y A))
    (skip-begin-pending (renamePending-∈ ρ Y∈)
      (subst≡
        (λ pending′ → _∋rep[_]_≔_ _ (know pending′) _ _)
        (sym (rename-dropSlot ρ Y pending))
        (rename-∋rep (delete↪ᵗ ρ Y) α∈)))
rename-∋rep ρ@(keep η)
    (skip-begin-live {A = A} {Y = Y} {pending = pending}
      Y∉ α∈) =
  subst≡ (λ D → _∋rep[_]_≔_ _ _ _ D)
    (sym (rename-delete-wk ρ Y A))
    (skip-begin-live (renamePending-∉ ρ Y∉)
      (rename-∋rep (delete↪ᵗ ρ Y) α∈))
rename-∋rep ρ@(skip η)
    (skip-begin-live {A = A} {Y = Y} {pending = pending}
      Y∉ α∈) =
  subst≡ (λ D → _∋rep[_]_≔_ _ _ _ D)
    (sym (rename-delete-wk ρ Y A))
    (skip-begin-live (renamePending-∉ ρ Y∉)
      (rename-∋rep (delete↪ᵗ ρ Y) α∈))
rename-∋rep ρ@(keep η)
    (skip-begin-opaq {A = A} {Y = Y} α∈) =
  subst≡ (λ D → _∋rep[_]_≔_ _ _ _ D)
    (sym (rename-delete-wk ρ Y A))
    (skip-begin-opaq (rename-∋rep (delete↪ᵗ ρ Y) α∈))
rename-∋rep ρ@(skip η)
    (skip-begin-opaq {A = A} {Y = Y} α∈) =
  subst≡ (λ D → _∋rep[_]_≔_ _ _ _ D)
    (sym (rename-delete-wk ρ Y A))
    (skip-begin-opaq (rename-∋rep (delete↪ᵗ ρ Y) α∈))
rename-∋rep (keep ρ)
    (skip-lexical-know {A = A} {pending = pending}
      {pending′ = pending′} eq α∈) =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C)
    (sym (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
      (renameᵗ-shift (toRenameᵗ ρ) A)))
    (skip-lexical-know pending-eq (rename-∋rep ρ α∈))
  where
  pending-eq : map suc (renamePending ρ pending)
    ≡ renamePending (keep ρ) pending′
  pending-eq = trans (sym (renamePending-keep-suc ρ pending))
    (cong (renamePending (keep ρ)) eq)
rename-∋rep (skip ρ)
    (skip-lexical-know {A = A} {pending = pending}
      {pending′ = pending′} eq α∈) =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C)
    (renameᵗ-comp (toRenameᵗ ρ) suc (⇑ᵗ A))
    (skip-lexical-know pending-eq
      (rename-∋rep ρ (skip-lexical-know eq α∈)))
  where
  pending-eq : map suc (renamePending ρ pending′)
    ≡ renamePending (skip ρ) pending′
  pending-eq = sym (renamePending-skip ρ pending′)
rename-∋rep (keep ρ) (skip-lexical-opaq {A = A} α∈) =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C)
    (sym (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
      (renameᵗ-shift (toRenameᵗ ρ) A)))
    (skip-lexical-opaq (rename-∋rep ρ α∈))
rename-∋rep (skip ρ) (skip-lexical-opaq {A = A} α∈) =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C)
    (renameᵗ-comp (toRenameᵗ ρ) suc (⇑ᵗ A))
    (skip-lexical-opaq
      (rename-∋rep ρ (skip-lexical-opaq α∈)))
rename-∋rep ρ
    (skip-end {Ψ = Ψ} {Y = Y} {α = α} {a = a}
      {A = A} {B = B} {C = C} {pending = pending}
      slot∈ rep∈ A∈ eq) =
  skip-end (rename-∋typ ρ⁺ slot∈) rep′ A′ eq′
  where
  ρ⁺ = insert↪ᵗ ρ Y
  Y′ = toRenameᵗ ρ⁺ Y
  deleted-eq = delete-insert↪ᵗ ρ Y
  rep′ = subst≡
    (λ D → _∋rep[_]_≔_ (renameTyEnv ρ⁺ Ψ)
      (know (Y′ ∷ map (punchIn Y′) (renamePending ρ pending))) α D)
    (rename-insert-wk ρ Y C)
    (transportPendingLookup
      (renamePending-insert ρ Y pending)
      (rename-∋rep ρ⁺ rep∈))
  A′ = transportPendingLookup
    (renamePending-insert ρ Y pending)
    (rename-∋rep ρ⁺ A∈)
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

{- Obsolete eager-deletion transport (removed with `_∖_`).
renameTyEnv-typ : ∀ {Θ Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Ψ : TyEnv Θ Δ) (X : TyVar (suc Δ)) (α : TyVar Θ)
  → renameTyEnv ρ (Ψ ,begin[ X ≔ α ])
    ≡ renameTyEnv (delete↪ᵗ ρ X) Ψ ,begin[ toRenameᵗ ρ X ≔ α ]
renameTyEnv-typ (keep ρ) Ψ X α = refl
renameTyEnv-typ (skip ρ) Ψ X α = refl

renameTyEnv-∖-typ-other : ∀ {Θ Δ Δ′}
    (ρ : suc (suc Δ) ↪ᵗ suc (suc Δ′))
    (Ψ : TyEnv Θ (suc Δ)) (X Y : TyVar (suc (suc Δ)))
    (α : TyVar Θ)
    (X≢Y : X ≢ Y) (Y≢X : Y ≢ X)
  → renameTyEnv (delete↪ᵗ ρ X) Ψ
      ∖ toRenameᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y)
    ≡ renameTyEnv
        (delete↪ᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y))
        (Ψ ∖ punchOut X Y X≢Y)
  → (renameTyEnv (delete↪ᵗ ρ X) Ψ
       ∖ toRenameᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y))
      ,begin[ toRenameᵗ (delete↪ᵗ ρ Y) (punchOut Y X Y≢X) ≔ α ]
    ≡ renameTyEnv (delete↪ᵗ ρ Y)
        ((Ψ ∖ punchOut X Y X≢Y)
          ,begin[ punchOut Y X Y≢X ≔ α ])
renameTyEnv-∖-typ-other ρ Ψ X Y α X≢Y Y≢X ih
    rewrite ih
      | delete-delete↪ᵗ ρ X Y X≢Y Y≢X
      | renameTyEnv-typ (delete↪ᵗ ρ Y)
          (Ψ ∖ punchOut X Y X≢Y) (punchOut Y X Y≢X) α =
  refl

no-typ-case : ∀ {Θ Δ Δ′}
    (ρ : suc (suc Δ) ↪ᵗ suc (suc Δ′))
    (Ψ : TyEnv Θ (suc Δ)) (X Y : TyVar (suc (suc Δ)))
    (α : TyVar Θ)
    (X≢Y : X ≢ Y)
  → renameTyEnv (delete↪ᵗ ρ X) Ψ
      ∖ toRenameᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y)
    ≡ renameTyEnv
        (delete↪ᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y))
        (Ψ ∖ punchOut X Y X≢Y)
  → renameTyEnv ρ (Ψ ,begin[ X ≔ α ]) ∖ toRenameᵗ ρ Y
    ≡ renameTyEnv (delete↪ᵗ ρ Y)
        ((Ψ ∖ punchOut X Y X≢Y)
          ,begin[ punchOut Y X (λ eq → X≢Y (sym eq)) ≔ α ])
no-typ-case ρ Ψ X Y α X≢Y ih =
  trans
    (cong (λ Ψ′ → Ψ′ ∖ toRenameᵗ ρ Y)
      (renameTyEnv-typ ρ Ψ X α))
    (trans
      (∖-typ-other (renameTyEnv (delete↪ᵗ ρ X) Ψ)
        (toRenameᵗ ρ X) (toRenameᵗ ρ Y) α ρX≢ρY ρY≢ρX)
      (trans
        (cong₂ (λ Ψ′ Z → Ψ′ ,begin[ Z ≔ α ])
          (cong (λ Z → renameTyEnv (delete↪ᵗ ρ X) Ψ ∖ Z)
            (sym (rename-punchOut ρ X Y X≢Y ρX≢ρY)))
          (sym (rename-punchOut ρ Y X Y≢X ρY≢ρX)))
        (trans
          (renameTyEnv-∖-typ-other ρ Ψ X Y α X≢Y Y≢X ih)
          (cong (renameTyEnv (delete↪ᵗ ρ Y))
            (cong (λ Z →
              (Ψ ∖ punchOut X Y X≢Y) ,begin[ Z ≔ α ])
              (punchOut-proof Y X Y≢X
                (λ eq → X≢Y (sym eq))))))))
  where
  Y≢X = λ eq → X≢Y (sym eq)
  ρX≢ρY = λ eq → X≢Y (toRenameᵗ-injective ρ eq)
  ρY≢ρX = λ eq → Y≢X (toRenameᵗ-injective ρ eq)

cross-typ-case : ∀ {Θ Δ Δ′}
    (ρ : suc (suc Δ) ↪ᵗ suc (suc Δ′))
    (Ψ : TyEnv Θ (suc Δ)) (X : TyVar (suc (suc Δ)))
    (Y : TyVar (suc Δ)) (α : TyVar Θ)
  → renameTyEnv (delete↪ᵗ ρ X) Ψ
      ∖ toRenameᵗ (delete↪ᵗ ρ X) Y
    ≡ renameTyEnv (delete↪ᵗ (delete↪ᵗ ρ X) Y) (Ψ ∖ Y)
  → renameTyEnv ρ (Ψ ,begin[ X ≔ α ])
      ∖ toRenameᵗ ρ (punchIn X Y)
    ≡ renameTyEnv (delete↪ᵗ ρ (punchIn X Y))
        ((Ψ ,begin[ X ≔ α ]) ∖ punchIn X Y)
cross-typ-case ρ Ψ X Y α ih with X ≟ punchIn X Y
cross-typ-case ρ Ψ X Y α ih | yes X≡Y =
  ⊥-elim (punchIn≢ X Y X≡Y)
cross-typ-case ρ Ψ X Y α ih | no X≢Y =
  no-typ-case ρ Ψ X (punchIn X Y) α X≢Y transported-ih
  where
  removed = punchOut X (punchIn X Y) X≢Y
  retained = punchOut (punchIn X Y) X (λ eq → X≢Y (sym eq))
  transported-ih =
    subst≡
      (λ Z → renameTyEnv (delete↪ᵗ ρ X) Ψ
          ∖ toRenameᵗ (delete↪ᵗ ρ X) Z
        ≡ renameTyEnv (delete↪ᵗ (delete↪ᵗ ρ X) Z) (Ψ ∖ Z))
      (sym (punchOut-punchIn X Y X≢Y)) ih

renameTyEnv-∖ : ∀ {Θ Δ Δ′} (ρ : suc Δ ↪ᵗ suc Δ′)
    (Ψ : TyEnv Θ (suc Δ)) (Y : TyVar (suc Δ))
    {α : TyVar Θ}
  → Ψ ∋typ Y ≔ α
  → renameTyEnv ρ Ψ ∖ toRenameᵗ ρ Y
    ≡ renameTyEnv (delete↪ᵗ ρ Y) (Ψ ∖ Y)
renameTyEnv-∖ (keep ρ) (Ψ ,begin[ Y ≔ α ]) Y here-typ
    rewrite ∖-typ-here (renameTyEnv (delete↪ᵗ (keep ρ) Y) Ψ)
              (toRenameᵗ (keep ρ) Y) α
      | ∖-typ-here Ψ Y α =
  refl
renameTyEnv-∖ (skip ρ) (Ψ ,begin[ Y ≔ α ]) Y here-typ
    rewrite ∖-typ-here (renameTyEnv (delete↪ᵗ (skip ρ) Y) Ψ)
              (toRenameᵗ (skip ρ) Y) α
      | ∖-typ-here Ψ Y α =
  refl
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′} ρ@(keep (keep η))
    (Ψ ,begin[ X ≔ α ]) .(punchIn X Y) (skip-begin {Y = Y} Y∈) =
  cross-typ-case ρ Ψ X Y α
    (renameTyEnv-∖ (delete↪ᵗ ρ X) Ψ Y Y∈)
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′} ρ@(keep (skip η))
    (Ψ ,begin[ X ≔ α ]) .(punchIn X Y) (skip-begin {Y = Y} Y∈) =
  cross-typ-case ρ Ψ X Y α
    (renameTyEnv-∖ (delete↪ᵗ ρ X) Ψ Y Y∈)
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′} ρ@(skip (keep η))
    (Ψ ,begin[ X ≔ α ]) .(punchIn X Y) (skip-begin {Y = Y} Y∈) =
  cross-typ-case ρ Ψ X Y α
    (renameTyEnv-∖ (delete↪ᵗ ρ X) Ψ Y Y∈)
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′} ρ@(skip (skip η))
    (Ψ ,begin[ X ≔ α ]) .(punchIn X Y) (skip-begin {Y = Y} Y∈) =
  cross-typ-case ρ Ψ X Y α
    (renameTyEnv-∖ (delete↪ᵗ ρ X) Ψ Y Y∈)
renameTyEnv-∖ (keep ρ) (Ψ ,typ) zero ()
renameTyEnv-∖ (skip ρ) (Ψ ,typ) zero ()
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = zero} (keep ())
    (Ψ ,typ) (suc Y) (skip-typ Y∈)
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = zero} (skip ())
    (Ψ ,typ) (suc Y) (skip-typ Y∈)
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    (keep ρ) (Ψ ,typ) (suc Y)
    (skip-typ Y∈)
    rewrite delete-keep-suc ρ Y | ∖-typ-zero-suc Ψ Y =
  cong _,typ (renameTyEnv-∖ ρ Ψ Y Y∈)
renameTyEnv-∖ {Δ = suc Δ} {Δ′ = suc Δ′}
    (skip ρ) (Ψ ,typ) (suc Y)
    (skip-typ Y∈)
    rewrite delete-skip ρ (suc Y) | ∖-typ-zero-suc Ψ Y =
  cong _,typ (renameTyEnv-∖ ρ (Ψ ,typ) (suc Y)
    (skip-typ Y∈))
renameTyEnv-∖ ρ (Ψ ,:= A) Y
    (skip-nu-binding {α = α} Y∈)
    with deleteSlot Ψ Y
       | deleteSlot (renameTyEnv ρ Ψ) (toRenameᵗ ρ Y)
       | renameTyEnv-∖ ρ Ψ Y Y∈
       | deletedRep-anchor Ψ Y Y∈
       | deletedRep-anchor (renameTyEnv ρ Ψ)
           (toRenameᵗ ρ Y) (rename-∋typ ρ Y∈)
renameTyEnv-∖ ρ (Ψ ,:= A) Y
    (skip-nu-binding {α = α} Y∈)
    | delete-view Φ C | delete-view Φ′ C′ | env-eq
    | source-rep-eq | target-rep-eq =
  cong₂ _,:=_ env-eq type-eq
  where
  deletedρ = delete↪ᵗ ρ Y
  rep-eq : C′ ≡ renameᵗ (toRenameᵗ deletedρ) C
  rep-eq =
    trans target-rep-eq
      (trans (cong (λ Ω → anchorRep Ω α) env-eq)
        (trans (rename-anchorRep deletedρ Φ α)
          (cong (renameᵗ (toRenameᵗ deletedρ))
            (sym source-rep-eq))))
  type-eq =
    trans (cong
      (λ D → substᵗ (resolveSubᵗ (toRenameᵗ ρ Y) D)
        (renameᵗ (toRenameᵗ ρ) A)) rep-eq)
      (sym (rename-resolve ρ Y C A))
-}

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
renameTarget-∋typ (target-typ X anchor target) here-typ = here-typ
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
    {α : TyVar Θ} {A : Ty Δ} {mode}
  → RenameTarget ρ Ψ Φ
  → Ψ ∋rep[ mode ] α ≔ A
  → Φ ∋rep[ renameMode ρ mode ] α ≔
      renameᵗ (toRenameᵗ ρ) A
renameTarget-∋rep {ρ = ρ} canonical-target α∈ = rename-∋rep ρ α∈
renameTarget-∋rep {A = A} {mode = know pending}
    literal-wk-target α∈ =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C) (sym (renameᵗ-wk-eq A))
    (subst≡ (λ pending′ → _∋rep[_]_≔_ _ (know pending′) _ _)
      (sym (renamePending-wk pending))
      (skip-lexical-know refl α∈))
renameTarget-∋rep {A = A} {mode = opaq}
    literal-wk-target α∈ =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C) (sym (renameᵗ-wk-eq A))
    (skip-lexical-opaq α∈)
renameTarget-∋rep {ρ = ρ} (target-typ X anchor target)
    (skip-begin-pending {A = A} {pending = pending} X∈ α∈) =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C)
    (sym (rename-delete-wk ρ X A))
    (skip-begin-pending (renamePending-∈ ρ X∈)
      (subst≡ (λ pending′ → _∋rep[_]_≔_ _ (know pending′) _ _)
        (sym (rename-dropSlot ρ X pending))
        (renameTarget-∋rep target α∈)))
renameTarget-∋rep {ρ = ρ} (target-typ X anchor target)
    (skip-begin-live {A = A} {pending = pending} X∉ α∈) =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C)
    (sym (rename-delete-wk ρ X A))
    (skip-begin-live (renamePending-∉ ρ X∉)
      (renameTarget-∋rep target α∈))
renameTarget-∋rep {ρ = ρ} (target-typ X anchor target)
    (skip-begin-opaq {A = A} α∈) =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C)
    (sym (rename-delete-wk ρ X A))
    (skip-begin-opaq (renameTarget-∋rep target α∈))
renameTarget-∋rep {ρ = keep ρ} (target-lexical target)
    (skip-lexical-know {A = A} {pending = pending}
      {pending′ = pending′} eq α∈) =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C)
    (sym (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq _))
      (renameᵗ-shift _ A)))
    (skip-lexical-know pending-eq
      (renameTarget-∋rep target α∈))
  where
  pending-eq : map suc (renamePending ρ pending)
    ≡ renamePending (keep ρ) pending′
  pending-eq = trans (sym (renamePending-keep-suc ρ pending))
    (cong (renamePending (keep ρ)) eq)
renameTarget-∋rep (target-lexical target)
    (skip-lexical-opaq {A = A} α∈) =
  subst≡ (λ C → _∋rep[_]_≔_ _ _ _ C)
    (sym (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq _))
      (renameᵗ-shift _ A)))
    (skip-lexical-opaq (renameTarget-∋rep target α∈))
renameTarget-∋rep (target-:= target) Z = Z
renameTarget-∋rep (target-:= target) (S α∈) =
  S (renameTarget-∋rep target α∈)
renameTarget-∋rep {A = B}
    (target-end { ρ = ρ } Y target)
    (skip-end {A = A} {C = C} {pending = pending}
      slot∈ rep∈ A∈ eq) =
  skip-end (renameTarget-∋typ target slot∈) rep′ A′ eq′
  where
  Y′ = toRenameᵗ ρ Y
  rep′ = subst≡
    (λ D → _∋rep[_]_≔_ _
      (know (Y′ ∷ map (punchIn Y′)
        (renamePending (delete↪ᵗ ρ Y) pending))) _ D)
    (rename-delete-wk ρ Y C)
    (transportPendingLookup
      (renamePending-delete ρ Y pending)
      (renameTarget-∋rep target rep∈))
  A′ = transportPendingLookup
    (renamePending-delete ρ Y pending)
    (renameTarget-∋rep target A∈)
  eq′ = trans (sym (rename-resolve ρ Y C A))
    (cong (renameᵗ (toRenameᵗ (delete↪ᵗ ρ Y))) eq)

{- Obsolete eager-deletion target transport (removed with `_∖_`).
delete-id↪ᵗ : ∀ {Δ} (Y : TyVar (suc Δ))
  → delete↪ᵗ id↪ᵗ Y ≡ id↪ᵗ
delete-id↪ᵗ {Δ = zero} zero = refl
delete-id↪ᵗ {Δ = suc Δ} zero = refl
delete-id↪ᵗ {Δ = suc Δ} (suc Y) = cong keep (delete-id↪ᵗ Y)

delete-wk↪ᵗ : ∀ {Δ} (Y : TyVar (suc Δ))
  → delete↪ᵗ wk↪ᵗ Y ≡ wk↪ᵗ
delete-wk↪ᵗ Y = cong skip (delete-id↪ᵗ Y)

∖-literal-wk : ∀ {Θ Δ} (Ψ : TyEnv Θ (suc Δ))
    (Y : TyVar (suc Δ))
  → (Ψ ,typ) ∖ toRenameᵗ wk↪ᵗ Y
    ≡ (Ψ ∖ Y) ,typ
∖-literal-wk Ψ Y rewrite toRename-id-eq Y = refl

renameTarget-delete-typ : ∀ {Θ Δ Δ′}
    {ρ : suc (suc Δ) ↪ᵗ suc (suc Δ′)}
    {Ψ : TyEnv Θ (suc Δ)} {Φ : TyEnv Θ (suc Δ′)}
    (X Y : TyVar (suc (suc Δ)))
    (α : TyVar Θ)
    (X≢Y : X ≢ Y) (Y≢X : Y ≢ X)
    (ρX≢ρY : toRenameᵗ ρ X ≢ toRenameᵗ ρ Y)
    (ρY≢ρX : toRenameᵗ ρ Y ≢ toRenameᵗ ρ X)
  → RenameTarget (delete↪ᵗ ρ X) Ψ Φ
  → RenameTarget
      (delete↪ᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y))
      (Ψ ∖ punchOut X Y X≢Y)
      (Φ ∖ toRenameᵗ (delete↪ᵗ ρ X) (punchOut X Y X≢Y))
  → RenameTarget (delete↪ᵗ ρ Y)
      ((Ψ ∖ punchOut X Y X≢Y) ,begin[ punchOut Y X Y≢X ≔ α ])
      ((Φ ∖ punchOut (toRenameᵗ ρ X) (toRenameᵗ ρ Y)
          ρX≢ρY)
        ,begin[ punchOut (toRenameᵗ ρ Y) (toRenameᵗ ρ X)
          ρY≢ρX ≔ α ])
renameTarget-delete-typ {ρ = ρ} {Ψ = Ψ} {Φ = Φ}
    X Y α X≢Y Y≢X ρX≢ρY ρY≢ρX target deleted-target =
  retained-target
  where
  source-Y = punchOut X Y X≢Y
  source-X = punchOut Y X Y≢X
  target-Y = punchOut (toRenameᵗ ρ X) (toRenameᵗ ρ Y) ρX≢ρY
  target-X = punchOut (toRenameᵗ ρ Y) (toRenameᵗ ρ X) ρY≢ρX

  deleted-injection-eq = delete-delete↪ᵗ ρ X Y X≢Y Y≢X
  deleted-target-env-eq = cong (Φ ∖_)
    (rename-punchOut ρ X Y X≢Y ρX≢ρY)

  normalized-deleted-target =
    subst≡
      (λ η → RenameTarget η (Ψ ∖ source-Y)
        (Φ ∖ toRenameᵗ (delete↪ᵗ ρ X) source-Y))
      deleted-injection-eq deleted-target

  underlying-target =
    subst≡
      (λ Φ′ → RenameTarget
        (delete↪ᵗ (delete↪ᵗ ρ Y) source-X)
        (Ψ ∖ source-Y) Φ′)
      deleted-target-env-eq normalized-deleted-target

  retained-target₀ = target-typ source-X α underlying-target

  retained-slot-eq = rename-punchOut ρ Y X Y≢X ρY≢ρX

  retained-target =
    subst≡
      (λ Z → RenameTarget (delete↪ᵗ ρ Y)
        ((Ψ ∖ source-Y) ,begin[ source-X ≔ α ])
        ((Φ ∖ target-Y) ,begin[ Z ≔ α ]))
      retained-slot-eq retained-target₀

renameTarget-delete-cross : ∀ {Θ Δ Δ′}
    {ρ : suc (suc Δ) ↪ᵗ suc (suc Δ′)}
    {Ψ : TyEnv Θ (suc Δ)} {Φ : TyEnv Θ (suc Δ′)}
    (X : TyVar (suc (suc Δ))) (Y : TyVar (suc Δ))
    (α : TyVar Θ)
  → RenameTarget (delete↪ᵗ ρ X) Ψ Φ
  → RenameTarget (delete↪ᵗ (delete↪ᵗ ρ X) Y) (Ψ ∖ Y)
      (Φ ∖ toRenameᵗ (delete↪ᵗ ρ X) Y)
  → RenameTarget (delete↪ᵗ ρ (punchIn X Y))
      ((Ψ ,begin[ X ≔ α ]) ∖ punchIn X Y)
      ((Φ ,begin[ toRenameᵗ ρ X ≔ α ])
        ∖ toRenameᵗ ρ (punchIn X Y))
renameTarget-delete-cross {ρ = ρ} {Ψ = Ψ} {Φ = Φ}
    X Y α target deleted-target
    with X ≟ punchIn X Y
       | toRenameᵗ ρ X ≟ toRenameᵗ ρ (punchIn X Y)
renameTarget-delete-cross X Y α target deleted-target
    | yes X≡Y | target-X≟Y =
  ⊥-elim (punchIn≢ X Y X≡Y)
renameTarget-delete-cross {ρ = ρ} X Y α target deleted-target
    | no X≢Y | yes ρX≡ρY =
  ⊥-elim (X≢Y (toRenameᵗ-injective ρ ρX≡ρY))
renameTarget-delete-cross {ρ = ρ} {Ψ = Ψ} {Φ = Φ}
    X Y α target deleted-target | no X≢Y | no ρX≢ρY =
  explicit-target
  where
  removed = punchOut X (punchIn X Y) X≢Y
  reverse = λ eq → X≢Y (sym eq)
  target-reverse = λ eq → ρX≢ρY (sym eq)
  transported-target =
    subst≡
      (λ Z → RenameTarget (delete↪ᵗ (delete↪ᵗ ρ X) Z)
        (Ψ ∖ Z) (Φ ∖ toRenameᵗ (delete↪ᵗ ρ X) Z))
      (sym (punchOut-punchIn X Y X≢Y)) deleted-target
  explicit-target = renameTarget-delete-typ X (punchIn X Y) α
    X≢Y reverse ρX≢ρY target-reverse target transported-target

renameTarget-delete : ∀ {Θ Δ Δ′} {ρ : suc Δ ↪ᵗ suc Δ′}
    {Ψ : TyEnv Θ (suc Δ)} {Φ : TyEnv Θ (suc Δ′)}
  → RenameTarget ρ Ψ Φ
  → (Y : TyVar (suc Δ))
  → {α : TyVar Θ}
  → Ψ ∋typ Y ≔ α
  → RenameTarget (delete↪ᵗ ρ Y) (Ψ ∖ Y)
      (Φ ∖ toRenameᵗ ρ Y)
renameTarget-delete {ρ = ρ} {Ψ = Ψ} canonical-target Y Y∈ =
  subst≡
    (λ Φ′ → RenameTarget (delete↪ᵗ ρ Y) (Ψ ∖ Y) Φ′)
    (sym (renameTyEnv-∖ ρ Ψ Y Y∈)) canonical-target
renameTarget-delete {Ψ = Ψ} literal-wk-target Y Y∈ =
  subst≡
    (λ Φ′ → RenameTarget (delete↪ᵗ wk↪ᵗ Y) (Ψ ∖ Y) Φ′)
    (sym (∖-literal-wk Ψ Y))
    (subst≡
      (λ η → RenameTarget η (Ψ ∖ Y) ((Ψ ∖ Y) ,typ))
      (sym (delete-wk↪ᵗ Y)) literal-wk-target)
renameTarget-delete {ρ = ρ} {Ψ = Ψ ,begin[ X ≔ α ]}
    {Φ = Φ ,begin[ .(toRenameᵗ ρ X) ≔ .α ]}
    (target-typ .X .α target) .X here-typ
    rewrite ∖-typ-here Ψ X α
      | ∖-typ-here Φ (toRenameᵗ ρ X) α =
  target
renameTarget-delete {Δ = suc Δ} {Δ′ = zero} {ρ = keep ()}
    (target-typ X α target) .(punchIn X Y)
    (skip-begin {Y = Y} Y∈)
renameTarget-delete {Δ = suc Δ} {Δ′ = zero} {ρ = skip ()}
    (target-typ X α target) .(punchIn X Y)
    (skip-begin {Y = Y} Y∈)
renameTarget-delete {Δ = suc Δ} {Δ′ = suc Δ′} {ρ = ρ}
    {Ψ = Ψ ,begin[ X ≔ α ]}
    {Φ = Φ ,begin[ .(toRenameᵗ ρ X) ≔ .α ]}
    (target-typ .X .α target) .(punchIn X Y)
    (skip-begin {Y = Y} Y∈) =
  renameTarget-delete-cross {ρ = ρ} X Y α target
    (renameTarget-delete target Y Y∈)
renameTarget-delete (target-lexical target) zero ()
renameTarget-delete {Δ = suc Δ} {Δ′ = zero}
    (target-lexical {ρ = ()} target) (suc Y) (skip-typ Y∈)
renameTarget-delete {Δ = suc Δ} {Δ′ = suc Δ′} {ρ = keep ρ}
    {Ψ = Ψ ,typ} {Φ = Φ ,typ} (target-lexical target) (suc Y)
    (skip-typ Y∈)
    rewrite delete-keep-suc ρ Y
      | ∖-typ-zero-suc Ψ Y
      | ∖-typ-zero-suc Φ (toRenameᵗ ρ Y) =
  target-lexical (renameTarget-delete target Y Y∈)
renameTarget-delete {ρ = ρ} {Ψ = Ψ ,:= A}
    {Φ = Φ ,:= .(renameᵗ (toRenameᵗ ρ) A)}
    (target-:= target) Y (skip-nu-binding {α = α} Y∈)
    with deleteSlot Ψ Y
       | deleteSlot Φ (toRenameᵗ ρ Y)
       | renameTarget-delete target Y Y∈
       | deletedRep-anchor Ψ Y Y∈
       | deletedRep-anchor Φ (toRenameᵗ ρ Y)
           (renameTarget-∋typ target Y∈)
renameTarget-delete {ρ = ρ} (target-:= {A = A} target) Y
    (skip-nu-binding {α = α} Y∈)
    | delete-view Ψ′ C | delete-view Φ′ C′ | deleted-target
    | source-rep-eq | target-rep-eq =
  subst≡
    (λ B → RenameTarget deletedρ
      (Ψ′ ,:= substᵗ (resolveSubᵗ Y C) A) (Φ′ ,:= B))
    (sym target-type-eq) (target-:= deleted-target)
  where
  deletedρ = delete↪ᵗ ρ Y

  rep-eq : C′ ≡ renameᵗ (toRenameᵗ deletedρ) C
  rep-eq =
    trans target-rep-eq
      (trans
        (anchor-lookup-unique (anchorRep∈ Φ′ α)
          (renameTarget-∋:= deleted-target (anchorRep∈ Ψ′ α)))
        (cong (renameᵗ (toRenameᵗ deletedρ))
          (sym source-rep-eq)))

  target-type-eq :
      substᵗ (resolveSubᵗ (toRenameᵗ ρ Y) C′)
        (renameᵗ (toRenameᵗ ρ) A)
    ≡ renameᵗ (toRenameᵗ deletedρ)
        (substᵗ (resolveSubᵗ Y C) A)
  target-type-eq =
    trans
      (cong
        (λ D → substᵗ (resolveSubᵗ (toRenameᵗ ρ Y) D)
          (renameᵗ (toRenameᵗ ρ) A)) rep-eq)
      (sym (rename-resolve ρ Y C A))
-}

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

{- The canonical theorem is the `canonical-target` corollary below.
⊢renameᵗᵐ : ∀ {Θ Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
    {M : Term Θ Δ} {A : Ty Δ}
  → Ψ ∣ Γ ⊢ M ⦂ A
  → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ M ⦂ renameᵗ (toRenameᵗ ρ) A
⊢renameᵗᵐ (⊢` x∈) = ⊢` (renameᵗ-∋ _ x∈)
⊢renameᵗᵐ (⊢ƛ M⊢) = ⊢ƛ (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ (⊢· L⊢ M⊢) =
  ⊢· (⊢renameᵗᵐ L⊢) (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ {ρ = ρ} {Ψ = Ψ} {Γ = Γ} (⊢Λ {A = A} M⊢) =
  ⊢Λ body⊢
  where
  renamed-body⊢ = ⊢renameᵗᵐ M⊢

  body-context⊢ =
    subst≡
      (λ Γ′ → renameTyEnv ρ Ψ ,typ ∣ Γ′
        ⊢ renameᵗᵐ (keep ρ) _ ⦂ _)
      (renameCtx-keep-shift ρ Γ) renamed-body⊢

  body⊢ =
    subst≡
      (λ B → renameTyEnv ρ Ψ ,typ ∣
        renameCtx suc (renameCtx (toRenameᵗ ρ) Γ)
          ⊢ renameᵗᵐ (keep ρ) _ ⦂ B)
      (renameᵗ-cong A (toRename-keep-eq ρ)) body-context⊢
⊢renameᵗᵐ {Δ′ = Δ′} {ρ = ρ} {Ψ = Ψ} {Γ = Γ}
    {M = L ⦂∀ C [ A ]} (⊢⦂∀ L⊢) =
  subst≡
    (λ B → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
      ⊢ renameᵗᵐ ρ L ⦂∀ renameᵗ (toRenameᵗ (keep ρ)) C
        [ renameᵗ (toRenameᵗ ρ) A ] ⦂ B)
    result-eq (⊢⦂∀ body⊢)
  where
  body-eq = renameᵗ-cong C (toRename-keep-eq ρ)

  body⊢ =
    subst≡
      (λ B → renameTyEnv ρ Ψ ∣ renameCtx (toRenameᵗ ρ) Γ
        ⊢ renameᵗᵐ ρ L ⦂ `∀ B)
      (sym body-eq) (⊢renameᵗᵐ L⊢)

  result-eq = sym (rename-open↪ᵗ ρ C A)
⊢renameᵗᵐ {ρ = ρ} (⊢$ κ) =
  subst≡ (λ A → _ ∣ _ ⊢ $ κ ⦂ A)
    (constTy-renameᵗ (toRenameᵗ ρ) κ) (⊢$ κ)
⊢renameᵗᵐ (⊢⊕ addℕ L⊢ M⊢) =
  ⊢⊕ addℕ (⊢renameᵗᵐ L⊢) (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ (⊢⊕ and𝔹 L⊢ M⊢) =
  ⊢⊕ and𝔹 (⊢renameᵗᵐ L⊢) (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ {ρ = ρ} (⊢⟨⟩ M⊢ c) =
  ⊢⟨⟩ (⊢renameᵗᵐ M⊢) (renameᵐᶜ ρ c)
⊢renameᵗᵐ (⊢ν M⊢) = ⊢ν (⊢renameᵗᵐ M⊢)
⊢renameᵗᵐ {ρ = ρ}
    (⊢reveal {A = A} {B = B} {C = C} {Y = Y} {α = α}
      α∈ c⊢ M⊢) =
  ⊢reveal (rename-∋:= ρ α∈) conversion⊢ body⊢
  where
  ρ⁺ = insert↪ᵗ ρ Y
  Y′ = toRenameᵗ ρ⁺ Y

  body⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∣ [] ⊢ renameᵗᵐ ρ⁺ _
        ⦂ renameᵗ (toRenameᵗ ρ⁺) A)
      (renameTyEnv-insert ρ _ Y α) (⊢renameᵗᵐ M⊢)

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
⊢renameᵗᵐ {ρ = ρ⁺@(keep ρ)} {Ψ = Ψ}
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y}
      slot∈ α∈ c⊢ M⊢) =
  ⊢conceal slot⊢ lookup⊢ conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  env-eq = renameTyEnv-∖ ρ⁺ Ψ Y slot∈
  slot⊢ = rename-∋typ ρ⁺ slot∈

  lookup⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∋ _ := renameᵗ (toRenameᵗ deleted) C)
      (sym env-eq) (rename-∋:= deleted α∈)

  body⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∣ [] ⊢ renameᵗᵐ deleted _
        ⦂ renameᵗ (toRenameᵗ deleted) A)
      (sym env-eq) (⊢renameᵗᵐ M⊢)

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
⊢renameᵗᵐ {ρ = ρ⁺@(skip ρ)} {Ψ = Ψ}
    (⊢conceal {A = A} {C = C} {B = B} {Y = Y}
      slot∈ α∈ c⊢ M⊢) =
  ⊢conceal slot⊢ lookup⊢ conversion⊢ body⊢
  where
  deleted = delete↪ᵗ ρ⁺ Y
  Y′ = toRenameᵗ ρ⁺ Y
  env-eq = renameTyEnv-∖ ρ⁺ Ψ Y slot∈
  slot⊢ = rename-∋typ ρ⁺ slot∈

  lookup⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∋ _ := renameᵗ (toRenameᵗ deleted) C)
      (sym env-eq) (rename-∋:= deleted α∈)

  body⊢ =
    subst≡
      (λ Ψ′ → Ψ′ ∣ [] ⊢ renameᵗᵐ deleted _
        ⦂ renameᵗ (toRenameᵗ deleted) A)
      (sym env-eq) (⊢renameᵗᵐ M⊢)

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
⊢renameᵗᵐ ⊢blame = ⊢blame
-}

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
    (anchor-target-typ Y anchor target) here-typ = here-typ
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
    {α : TyVar Θ} {A : Ty Δ} {mode}
  → (∀ {β γ} → ρ β ≡ ρ γ → β ≡ γ)
  → AnchorTarget ρ Ψ Φ
  → _∋rep[_]_≔_ Ψ mode α A
  → _∋rep[_]_≔_ Φ mode (ρ α) A
anchorTarget-∋rep ρ-inj visible-shift-target α∈ = S α∈
anchorTarget-∋rep ρ-inj (anchor-target-typ Y anchor target)
    (skip-begin-pending Y∈ α∈) =
  skip-begin-pending Y∈ (anchorTarget-∋rep ρ-inj target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-typ Y anchor target)
    (skip-begin-live Y∉ α∈) =
  skip-begin-live Y∉ (anchorTarget-∋rep ρ-inj target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-typ Y anchor target)
    (skip-begin-opaq α∈) =
  skip-begin-opaq (anchorTarget-∋rep ρ-inj target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-lexical target)
    (skip-lexical-know eq α∈) =
  skip-lexical-know eq (anchorTarget-∋rep ρ-inj target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-lexical target)
    (skip-lexical-opaq α∈) =
  skip-lexical-opaq (anchorTarget-∋rep ρ-inj target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-allocate target)
    (skip-lexical-opaq α∈) =
  skip-begin-opaq (anchorTarget-∋rep ρ-inj target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-:= target) Z = Z
anchorTarget-∋rep ρ-inj (anchor-target-:= target) (S α∈) =
  S (anchorTarget-∋rep
    (λ eq → fin-suc-injective (ρ-inj (cong suc eq))) target α∈)
anchorTarget-∋rep ρ-inj (anchor-target-end Y target)
    (skip-end slot∈ rep∈ A∈ eq) =
  skip-end (anchorTarget-∋typ ρ-inj target slot∈)
    (anchorTarget-∋rep ρ-inj target rep∈)
    (anchorTarget-∋rep ρ-inj target A∈) eq

{- Obsolete eager-deletion anchor transport (removed with `_∖_`).
anchorTarget-delete : ∀ {Θ Θ′ Δ} {ρ : TyVar Θ → TyVar Θ′}
    {Ψ : TyEnv Θ (suc Δ)} {Φ : TyEnv Θ′ (suc Δ)}
  → AnchorTarget ρ Ψ Φ
  → (Y : TyVar (suc Δ))
  → {α : TyVar Θ}
  → Ψ ∋typ Y ≔ α
  → AnchorTarget ρ (Ψ ∖ Y) (Φ ∖ Y)
anchorTarget-delete {Ψ = Ψ} visible-shift-target Y Y∈
    with deleteSlot Ψ Y
anchorTarget-delete visible-shift-target Y Y∈
    | delete-view Φ C = visible-shift-target
anchorTarget-delete {ρ = ρ} {Ψ = Ψ ,begin[ X ≔ α ]}
    {Φ = Φ ,begin[ .X ≔ .(ρ α) ]}
    (anchor-target-typ .X .α target) .X here-typ
    rewrite ∖-typ-here Ψ X α | ∖-typ-here Φ X (ρ α) =
  target
anchorTarget-delete {Δ = suc Δ} {ρ = ρ} {Ψ = Ψ ,begin[ X ≔ α ]}
    {Φ = Φ ,begin[ .X ≔ .(ρ α) ]}
    (anchor-target-typ .X .α target) .(punchIn X Y)
    (skip-begin {Y = Y} Y∈)
    rewrite ∖-typ-other Ψ X (punchIn X Y) α (punchIn≢ X Y)
          (λ eq → punchIn≢ X Y (sym eq))
      | ∖-typ-other Φ X (punchIn X Y) (ρ α) (punchIn≢ X Y)
          (λ eq → punchIn≢ X Y (sym eq))
      | punchOut-punchIn X Y (punchIn≢ X Y) =
  anchor-target-typ
    (punchOut (punchIn X Y) X
      (λ eq → punchIn≢ X Y (sym eq))) α
    (anchorTarget-delete target Y Y∈)
anchorTarget-delete (anchor-target-lexical target) zero ()
anchorTarget-delete {Δ = suc Δ} {Ψ = Ψ ,typ} {Φ = Φ ,typ}
    (anchor-target-lexical target) (suc Y) (skip-typ Y∈)
    rewrite ∖-typ-zero-suc Ψ Y | ∖-typ-zero-suc Φ Y =
  anchor-target-lexical (anchorTarget-delete target Y Y∈)
anchorTarget-delete {Φ = Φ ,begin[ zero ≔ zero ]}
    (anchor-target-allocate target) zero ()
anchorTarget-delete { Δ = suc Δ } { Ψ = Ψ ,typ }
    { Φ = Φ ,begin[ zero ≔ zero ] }
    (anchor-target-allocate target) (suc Y) (skip-typ Y∈) =
  anchor-target-allocate (anchorTarget-delete target Y Y∈)
anchorTarget-delete {Ψ = Ψ ,:= A} {Φ = Φ ,:= .A}
    (anchor-target-:= target) Y
    (skip-nu-binding {α = α} Y∈)
    with deleteSlot Ψ Y | deleteSlot Φ Y
       | anchorTarget-delete target Y Y∈
       | deletedRep-anchor Ψ Y Y∈
       | deletedRep-anchor Φ Y (anchorTarget-∋typ target Y∈)
anchorTarget-delete (anchor-target-:= {A = A} target) Y
    (skip-nu-binding {α = α} Y∈)
    | delete-view Ψ′ C | delete-view Φ′ C′ | deleted-target
    | source-rep-eq | target-rep-eq =
  subst≡
    (λ B → AnchorTarget _
      (Ψ′ ,:= substᵗ (resolveSubᵗ Y C) A) (Φ′ ,:= B))
    (sym type-eq) (anchor-target-:= deleted-target)
  where
  rep-eq : C′ ≡ C
  rep-eq =
    trans target-rep-eq
      (trans
        (anchor-lookup-unique (anchorRep∈ Φ′ _)
          (anchorTarget-∋:= deleted-target (anchorRep∈ Ψ′ α)))
        (sym source-rep-eq))

  type-eq : substᵗ (resolveSubᵗ Y C′) A
    ≡ substᵗ (resolveSubᵗ Y C) A
  type-eq = cong (λ D → substᵗ (resolveSubᵗ Y D) A) rep-eq
-}

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
  → Ψ ∋rep[ know [] ] α ≔ A
  → (Ψ ,:= B) ∋rep[ know [] ] (suc α) ≔ A
∋:=-shift = S
