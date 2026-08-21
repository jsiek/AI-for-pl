{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxAliasFocusModeProbe where

-- File Charter:
--   * Gives the two-Ctx world a scoped stack of target reveal boundaries.
--   * Keeps an administrative target allocation outside the stable world and
--     makes each direct store edge usable only through an exact reveal or
--     conceal rule.
--   * Checks the generic two-step beta := alpha, alpha := star reveal spine.
--     No rule resolves store aliases or mentions Lambda.

import Data.Fin as Fin
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using
  (Ty; TyVar; ★; ＇_; ‵_; _⇒_; renameᵗ)
open import TyStore using (TyStore; lookupStore; store-bind)
import TermCtx as TC
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import Conversion using (unseal; seal)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Term; `_; ƛ_; _·_; _↑_; _↓_)
open import proof.DGG.TwoCtxWorld
open import proof.DGG.TwoCtxWorldInvariants
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe


-- The administrative scope fixes one target allocation but does not place its
-- new variable in the stable center.  A mode stack records which target names
-- have been focused on X by exact direct-store boundaries.  The bottom mode
-- sees old target variables through the stable embedding and deliberately has
-- no view of the new target variable.

module AliasFocusModeᶠ₁
    {Cᴸ : Ctx} {Δᴿ} {Σᴿ : TyStore Δᴿ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : Cᴸ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar Δᴿ}
    (focus : TargetNameFocusᶠ₀ W X alpha)
    {Γᴿ⁺ : TC.TermCtx (suc Δᴿ)}
    (scope : TargetAliasBoundaryᶠ₀ focus
      ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ⁺ ⟩)
    where

  target-storeᶠ₁ : TyStore (suc Δᴿ)
  target-storeᶠ₁ = store-bind Σᴿ (＇ alpha)

  data TargetModeᶠ₁ : Set where
    stable-modeᶠ₁ : TargetModeᶠ₁
    push-focusᶠ₁ :
      TargetModeᶠ₁ → TyVar (suc Δᴿ) → TargetModeᶠ₁

  -- Variable views are intentionally relational.  Consequently, the pending
  -- allocation's zero variable has no stable-mode view.  A direct boundary
  -- must push its focus before an ordinary term can use that name.

  data TargetVarViewᶠ₁ :
      TargetModeᶠ₁ → TyVar (suc Δᴿ)
      → TyVar (centerᶜ W) → Set where

    stable-oldᶠ₁ : ∀ {Y Z}
      → toRenameᵗ (ηᴿᶜ W) Y ≡ Z
      → TargetVarViewᶠ₁ stable-modeᶠ₁ (Fin.suc Y) Z

    focus-hereᶠ₁ : ∀ {m Y Z}
      → toRenameᵗ (ηᴸᶜ W) X ≡ Z
      → TargetVarViewᶠ₁ (push-focusᶠ₁ m Y) Y Z

    focus-thereᶠ₁ : ∀ {m Y Y′ Z}
      → Y ≢ Y′
      → TargetVarViewᶠ₁ m Y′ Z
      → TargetVarViewᶠ₁ (push-focusᶠ₁ m Y) Y′ Z

  stable-new-unavailableᶠ₁ : ∀ {Z}
    → TargetVarViewᶠ₁ stable-modeᶠ₁ Fin.zero Z
    → ⊥
  stable-new-unavailableᶠ₁ ()

  -- This partial type view is enough for conversion spines and ordinary
  -- function structure.  Universals would lift the same mode stack; that
  -- orthogonal binder operation is deliberately outside this small probe.

  data TargetTypeViewᶠ₁ (m : TargetModeᶠ₁) :
      Ty (suc Δᴿ) → Ty (centerᶜ W) → Set where

    view-varᶠ₁ : ∀ {Y Z}
      → TargetVarViewᶠ₁ m Y Z
      → TargetTypeViewᶠ₁ m (＇ Y) (＇ Z)

    view-baseᶠ₁ : ∀ {ι}
      → TargetTypeViewᶠ₁ m (‵ ι) (‵ ι)

    view-starᶠ₁ : TargetTypeViewᶠ₁ m ★ ★

    view-funᶠ₁ : ∀ {A B A′ B′}
      → TargetTypeViewᶠ₁ m A A′
      → TargetTypeViewᶠ₁ m B B′
      → TargetTypeViewᶠ₁ m (A ⇒ B) (A′ ⇒ B′)

  data ScopedTypeImprecisionᶠ₁ (m : TargetModeᶠ₁) :
      Ty (Δᵉ Cᴸ) → Ty (suc Δᴿ) → Set where

    scoped-type-imprecisionᶠ₁ : ∀ {A B Bᶜ}
      → TargetTypeViewᶠ₁ m B Bᶜ
      → I._⊢_⊑_ (marksᶜ W)
          (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A) Bᶜ
      → ScopedTypeImprecisionᶠ₁ m A B

  -- An exact boundary names one source pivot, one target pivot, and their
  -- direct endpoint representations.  Its imprecision certificate is checked
  -- in the parent mode.  No store traversal occurs here.

  data ExactTargetBoundaryᶠ₁ (m : TargetModeᶠ₁) :
      (Y : TyVar (suc Δᴿ)) (R : Ty (suc Δᴿ))
      → ScopedTypeImprecisionᶠ₁ m (＇ X) R → Set where

    exact-target-boundaryᶠ₁ : ∀ {Y R q}
      → lookupStore (Σᵉ Cᴸ) X ≡ ＇ X
      → lookupStore target-storeᶠ₁ Y ≡ R
      → ExactTargetBoundaryᶠ₁ m Y R q

  data ValidTargetModeᶠ₁ : TargetModeᶠ₁ → Set where
    stable-validᶠ₁ : ValidTargetModeᶠ₁ stable-modeᶠ₁

    push-validᶠ₁ : ∀ {m Y R q}
      → ValidTargetModeᶠ₁ m
      → ExactTargetBoundaryᶠ₁ m Y R q
      → ValidTargetModeᶠ₁ (push-focusᶠ₁ m Y)

  -- Lambda and application stand for the ordinary syntax-directed cases:
  -- they preserve both the mode and its validity proof.  Only the exact
  -- target reveal/conceal cases cross a mode boundary.

  data ScopedTermImprecisionᶠ₁ :
      (m : TargetModeᶠ₁) → ValidTargetModeᶠ₁ m
      → Term (Δᵉ Cᴸ) → Term (suc Δᴿ) → Set where

    atom⊑atomᶠ₁ : ∀ {m ok x}
      → ScopedTermImprecisionᶠ₁ m ok (` x) (` x)

    ƛ⊑ƛᶠ₁ : ∀ {m ok M M′}
      → ScopedTermImprecisionᶠ₁ m ok M M′
      → ScopedTermImprecisionᶠ₁ m ok (ƛ M) (ƛ M′)

    ·⊑·ᶠ₁ : ∀ {m ok L L′ M M′}
      → ScopedTermImprecisionᶠ₁ m ok L L′
      → ScopedTermImprecisionᶠ₁ m ok M M′
      → ScopedTermImprecisionᶠ₁ m ok (L · M) (L′ · M′)

    target-revealᶠ₁ : ∀ {m ok Y R q M M′}
      → (boundary : ExactTargetBoundaryᶠ₁ m Y R q)
      → ScopedTermImprecisionᶠ₁
          (push-focusᶠ₁ m Y) (push-validᶠ₁ ok boundary) M M′
      → ScopedTermImprecisionᶠ₁ m ok M (M′ ↑ unseal Y R)

    target-concealᶠ₁ : ∀ {m ok Y R q M M′}
      → (boundary : ExactTargetBoundaryᶠ₁ m Y R q)
      → ScopedTermImprecisionᶠ₁ m ok M M′
      → ScopedTermImprecisionᶠ₁
          (push-focusᶠ₁ m Y) (push-validᶠ₁ ok boundary)
          M (M′ ↓ seal Y R)

  mode-depthᶠ₁ : TargetModeᶠ₁ → ℕ
  mode-depthᶠ₁ stable-modeᶠ₁ = zero
  mode-depthᶠ₁ (push-focusᶠ₁ m Y) = suc (mode-depthᶠ₁ m)


-- The checked strict-Lambda allocation geometry from the preceding probe is
-- only the producer of this generic scope.  None of the rules below inspect a
-- Lambda term or follow a store alias.

module StrictLambdaMode =
  AliasFocusModeᶠ₁ strict-lambda-focus strict-lambda-boundary

open StrictLambdaMode

alpha-modeᶠ₁ : TargetModeᶠ₁
alpha-modeᶠ₁ = push-focusᶠ₁ stable-modeᶠ₁ target-alpha⁺

stable-X-starᶠ₁ :
  ScopedTypeImprecisionᶠ₁ stable-modeᶠ₁ (＇ source-X) ★
stable-X-starᶠ₁ =
  scoped-type-imprecisionᶠ₁ view-starᶠ₁ (I.X⊑★ refl)

alpha-boundaryᶠ₁ :
  ExactTargetBoundaryᶠ₁ stable-modeᶠ₁ target-alpha⁺ ★
    stable-X-starᶠ₁
alpha-boundaryᶠ₁ =
  exact-target-boundaryᶠ₁ stable-X-self target-alpha-entry

alpha-validᶠ₁ : ValidTargetModeᶠ₁ alpha-modeᶠ₁
alpha-validᶠ₁ = push-validᶠ₁ stable-validᶠ₁ alpha-boundaryᶠ₁

alpha-viewᶠ₁ :
  TargetTypeViewᶠ₁ alpha-modeᶠ₁ (＇ target-alpha⁺)
    (＇ toRenameᵗ (ηᴸᶜ stable-world) source-X)
alpha-viewᶠ₁ = view-varᶠ₁ (focus-hereᶠ₁ refl)

alpha-X-alphaᶠ₁ :
  ScopedTypeImprecisionᶠ₁ alpha-modeᶠ₁
    (＇ source-X) (＇ target-alpha⁺)
alpha-X-alphaᶠ₁ =
  scoped-type-imprecisionᶠ₁ alpha-viewᶠ₁ I.X⊑X

beta-modeᶠ₁ : TargetModeᶠ₁
beta-modeᶠ₁ = push-focusᶠ₁ alpha-modeᶠ₁ target-beta

beta-boundaryᶠ₁ :
  ExactTargetBoundaryᶠ₁ alpha-modeᶠ₁ target-beta
    (＇ target-alpha⁺) alpha-X-alphaᶠ₁
beta-boundaryᶠ₁ =
  exact-target-boundaryᶠ₁ stable-X-self target-beta-entry

beta-validᶠ₁ : ValidTargetModeᶠ₁ beta-modeᶠ₁
beta-validᶠ₁ = push-validᶠ₁ alpha-validᶠ₁ beta-boundaryᶠ₁

beta-viewᶠ₁ :
  TargetTypeViewᶠ₁ beta-modeᶠ₁ (＇ target-beta)
    (＇ toRenameᵗ (ηᴸᶜ stable-world) source-X)
beta-viewᶠ₁ = view-varᶠ₁ (focus-hereᶠ₁ refl)

beta-X-betaᶠ₁ :
  ScopedTypeImprecisionᶠ₁ beta-modeᶠ₁
    (＇ source-X) (＇ target-beta)
beta-X-betaᶠ₁ =
  scoped-type-imprecisionᶠ₁ beta-viewᶠ₁ I.X⊑X

two-boundaries-require-two-pushes :
  mode-depthᶠ₁ beta-modeᶠ₁ ≡ suc (suc zero)
two-boundaries-require-two-pushes = refl

two-boundaries-are-not-one : ∀ {Y}
  → beta-modeᶠ₁ ≢ push-focusᶠ₁ stable-modeᶠ₁ Y
two-boundaries-are-not-one ()

two-target-revealsᶠ₁ :
  ScopedTermImprecisionᶠ₁ stable-modeᶠ₁ stable-validᶠ₁
    (` zero)
    (((` zero) ↑ unseal target-beta (＇ target-alpha⁺))
      ↑ unseal target-alpha⁺ ★)
two-target-revealsᶠ₁ =
  target-revealᶠ₁ alpha-boundaryᶠ₁
    (target-revealᶠ₁ beta-boundaryᶠ₁ atom⊑atomᶠ₁)
