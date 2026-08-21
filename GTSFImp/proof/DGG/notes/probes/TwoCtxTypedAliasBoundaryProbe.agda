{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxTypedAliasBoundaryProbe where

-- File Charter:
--   * Refines the two-Ctx alias-focus mode stack into a type-indexed skeletal
--     cast-term-imprecision surface.
--   * Ordinary syntax preserves its mode.  Exact target reveal/conceal rules
--     are the only constructors that cross one direct boundary.
--   * Checks the fully indexed beta := alpha, alpha := star target reveal
--     spine without resolving aliases or changing the stable world.

open import Data.Nat using (suc; zero)

open import Types using (Ty; TyVar; ★; ＇_; _⇒_; renameᵗ)
open import TyStore using (TyStore; store-bind)
import TermCtx as TC
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import Conversion using (unseal; seal)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Term; `_; ƛ_; _·_; _↑_; _↓_)
open import proof.DGG.TwoCtxWorld
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe
open import proof.DGG.notes.probes.TwoCtxAliasFocusModeProbe


module TypedAliasBoundaryᶠ₂
    {Cᴸ : Ctx} {Δᴿ} {Σᴿ : TyStore Δᴿ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : Cᴸ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar Δᴿ}
    (focus : TargetNameFocusᶠ₀ W X alpha)
    {Γᴿ⁺ : TC.TermCtx (suc Δᴿ)}
    (scope : TargetAliasBoundaryᶠ₀ focus
      ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ⁺ ⟩)
    where

  module Mode = AliasFocusModeᶠ₁ focus scope
  open Mode

  -- This is deliberately only the boundary-relevant CTI surface.  The atom
  -- case abstracts the term-context lookup; lambda and application retain the
  -- live relation's type indices and demonstrate that ordinary syntax cannot
  -- change a pending mode.

  data ScopedCastTermImprecisionᶠ₂ :
      (m : TargetModeᶠ₁) → ValidTargetModeᶠ₁ m
      → Term (Δᵉ Cᴸ) → Term (suc Δᴿ)
      → {A : Ty (Δᵉ Cᴸ)} {B : Ty (suc Δᴿ)}
      → ScopedTypeImprecisionᶠ₁ m A B → Set where

    atom⊑atomᶠ₂ : ∀ {m ok x A B p}
      → ScopedCastTermImprecisionᶠ₂ m ok (` x) (` x) {A} {B} p

    ƛ⊑ƛᶠ₂ : ∀
        {m ok M M′ A A′ B B′ Aᶜ Bᶜ}
        {view-A : TargetTypeViewᶠ₁ m A′ Aᶜ}
        {view-B : TargetTypeViewᶠ₁ m B′ Bᶜ}
        {pA : I._⊢_⊑_ (marksᶜ W)
          (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A) Aᶜ}
        {pB : I._⊢_⊑_ (marksᶜ W)
          (renameᵗ (toRenameᵗ (ηᴸᶜ W)) B) Bᶜ}
      → ScopedCastTermImprecisionᶠ₂ m ok M M′
          (scoped-type-imprecisionᶠ₁ view-B pB)
      → ScopedCastTermImprecisionᶠ₂ m ok (ƛ M) (ƛ M′)
          (scoped-type-imprecisionᶠ₁
            (view-funᶠ₁ view-A view-B) (I.⇒⊑⇒ pA pB))

    ·⊑·ᶠ₂ : ∀
        {m ok L L′ M M′ A A′ B B′ Aᶜ Bᶜ}
        {view-A : TargetTypeViewᶠ₁ m A′ Aᶜ}
        {view-B : TargetTypeViewᶠ₁ m B′ Bᶜ}
        {pA : I._⊢_⊑_ (marksᶜ W)
          (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A) Aᶜ}
        {pB : I._⊢_⊑_ (marksᶜ W)
          (renameᵗ (toRenameᵗ (ηᴸᶜ W)) B) Bᶜ}
      → ScopedCastTermImprecisionᶠ₂ m ok L L′
          (scoped-type-imprecisionᶠ₁
            (view-funᶠ₁ view-A view-B) (I.⇒⊑⇒ pA pB))
      → ScopedCastTermImprecisionᶠ₂ m ok M M′
          (scoped-type-imprecisionᶠ₁ view-A pA)
      → ScopedCastTermImprecisionᶠ₂ m ok (L · M) (L′ · M′)
          (scoped-type-imprecisionᶠ₁ view-B pB)

    target-revealᶠ₂ : ∀ {m ok Y R q M M′ p}
      → (boundary : ExactTargetBoundaryᶠ₁ m Y R q)
      → ScopedCastTermImprecisionᶠ₂
          (push-focusᶠ₁ m Y) (push-validᶠ₁ ok boundary) M M′
          {＇ X} {＇ Y} p
      → ScopedCastTermImprecisionᶠ₂ m ok M (M′ ↑ unseal Y R)
          {＇ X} {R} q

    target-concealᶠ₂ : ∀ {m ok Y R q M M′ p}
      → (boundary : ExactTargetBoundaryᶠ₁ m Y R q)
      → ScopedCastTermImprecisionᶠ₂ m ok M M′ {＇ X} {R} q
      → ScopedCastTermImprecisionᶠ₂
          (push-focusᶠ₁ m Y) (push-validᶠ₁ ok boundary)
          M (M′ ↓ seal Y R) {＇ X} {＇ Y} p


module StrictLambdaTyped =
  TypedAliasBoundaryᶠ₂ strict-lambda-focus strict-lambda-boundary

open StrictLambdaTyped
open StrictLambdaTyped.Mode

beta-atomᶠ₂ :
  ScopedCastTermImprecisionᶠ₂ beta-modeᶠ₁ beta-validᶠ₁
    (` zero) (` zero) {＇ source-X} {＇ target-beta} beta-X-betaᶠ₁
beta-atomᶠ₂ = atom⊑atomᶠ₂

beta-revealᶠ₂ :
  ScopedCastTermImprecisionᶠ₂ alpha-modeᶠ₁ alpha-validᶠ₁
    (` zero) ((` zero) ↑ unseal target-beta (＇ target-alpha⁺))
    {＇ source-X} {＇ target-alpha⁺} alpha-X-alphaᶠ₁
beta-revealᶠ₂ = target-revealᶠ₂ beta-boundaryᶠ₁ beta-atomᶠ₂

alpha-beta-revealsᶠ₂ :
  ScopedCastTermImprecisionᶠ₂
    stable-modeᶠ₁ stable-validᶠ₁
    (` zero)
    (((` zero) ↑ unseal target-beta (＇ target-alpha⁺))
      ↑ unseal target-alpha⁺ ★)
    {＇ source-X} {★} stable-X-starᶠ₁
alpha-beta-revealsᶠ₂ =
  target-revealᶠ₂ alpha-boundaryᶠ₁ beta-revealᶠ₂
