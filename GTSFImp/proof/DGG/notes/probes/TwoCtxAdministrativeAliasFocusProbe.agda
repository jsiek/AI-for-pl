{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe where

-- File Charter:
--   * Extends the two-Ctx skeleton with a boundary-scoped target name focus
--     and one nominal administrative alias edge.
--   * Represents the strict-Lambda geometry X focused on alpha, followed by
--     beta := alpha, without changing the stable world or resolving alpha.
--   * Checks the paired reveal rule indices at that boundary while retaining
--     the stable world's direct representation invariants.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([])
open import Data.Nat using (suc; zero)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import Types using
  (Ty; TyVar; ★; ＇_; substᵗ; renameᵗ)
import TyStore
open import TyStore using
  (lookupStore; store-empty; store-lift; store-bind)
import TermCtx as TC
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Γᵉ; _,ˢ_; ⇑ᵉᵗ)
open import Conversion using (Conv↑; unseal)
open import proof.DGG.TwoCtxWorld
open import proof.DGG.TwoCtxWorldInvariants


-- A focus is local authorization to read one old target name at the source
-- pivot's center point.  The stable embeddings remain separated.  The guard
-- compares direct store entries in the stable world; it is not an alias-chain
-- closure.

record TargetNameFocusᶠ₀ {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ)
    (X : TyVar (Δᵉ Cᴸ)) (alpha : TyVar (Δᵉ Cᴿ)) : Set where
  constructor target-name-focusᶠ₀
  field
    stable-points-separated :
      toRenameᵗ (ηᴸᶜ W) X ≢ toRenameᵗ (ηᴿᶜ W) alpha
    source-direct-self : lookupStore (Σᵉ Cᴸ) X ≡ ＇ X
    stable-direct-representations :
      lookupStore (Σᵉ Cᴸ) X ⊑ᵀ⟨ W ⟩ lookupStore (Σᵉ Cᴿ) alpha

open TargetNameFocusᶠ₀ public


focusTargetVarᶠ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {X alpha}
  → TargetNameFocusᶠ₀ W X alpha
  → TyVar (Δᵉ Cᴿ)
  → TyVar (centerᶜ W)
focusTargetVarᶠ₀ {W = W} {X = X} {alpha = alpha} focus Y
    with alpha ≟ Y
focusTargetVarᶠ₀ {W = W} {X = X} focus ._ | yes refl =
  toRenameᵗ (ηᴸᶜ W) X
focusTargetVarᶠ₀ {W = W} focus Y | no alpha≢Y =
  toRenameᵗ (ηᴿᶜ W) Y


focusTargetTyᶠ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {X alpha}
  → TargetNameFocusᶠ₀ W X alpha
  → Ty (Δᵉ Cᴿ)
  → Ty (centerᶜ W)
focusTargetTyᶠ₀ focus B =
  substᵗ (λ Y → ＇ focusTargetVarᶠ₀ focus Y) B


focus-sees-referent : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {X alpha}
    (focus : TargetNameFocusᶠ₀ W X alpha)
  → focusTargetVarᶠ₀ focus alpha ≡ toRenameᵗ (ηᴸᶜ W) X
focus-sees-referent {alpha = alpha} focus with alpha ≟ alpha
focus-sees-referent focus | yes refl = refl
focus-sees-referent focus | no alpha≢alpha = ⊥-elim (alpha≢alpha refl)


-- The boundary index records the target allocation literally as beta := alpha
-- and keeps the lifted term context as an equality premise.  No defined
-- function occurs in the data constructor's endpoint index.

data TargetAliasBoundaryᶠ₀ {Cᴸ : Ctx}
    {Δᴿ} {Σᴿ : TyStore.TyStore Δᴿ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : Cᴸ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar Δᴿ}
    (focus : TargetNameFocusᶠ₀ W X alpha) : Ctx → Set where

  target-alias-rawᶠ₀ : ∀ {Γᴿ⁺ : TC.TermCtx (suc Δᴿ)}
    → Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ
    → TargetAliasBoundaryᶠ₀ focus
        ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ⁺ ⟩


targetAliasBoundaryᶠ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {X alpha}
    (focus : TargetNameFocusᶠ₀ W X alpha)
  → TargetAliasBoundaryᶠ₀ focus (Cᴿ ,ˢ ＇ alpha)
targetAliasBoundaryᶠ₀ focus = target-alias-rawᶠ₀ refl


aliasBoundarySubᶠ₀ : ∀ {Cᴸ Δᴿ} {Σᴿ : TyStore.TyStore Δᴿ}
    {Γᴿ : TC.TermCtx Δᴿ}
    {W : Cᴸ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩} {X alpha}
    {focus : TargetNameFocusᶠ₀ W X alpha} {Cᴿ⁺}
  → TargetAliasBoundaryᶠ₀ focus Cᴿ⁺
  → TyVar (Δᵉ Cᴿ⁺)
  → Ty Δᴿ
aliasBoundarySubᶠ₀ {alpha = alpha} (target-alias-rawᶠ₀ eq) Fin.zero =
  ＇ alpha
aliasBoundarySubᶠ₀ (target-alias-rawᶠ₀ eq) (Fin.suc Y) = ＇ Y


boundaryTargetTyᶠ₀ : ∀ {Cᴸ Δᴿ} {Σᴿ : TyStore.TyStore Δᴿ}
    {Γᴿ : TC.TermCtx Δᴿ}
    {W : Cᴸ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩} {X alpha}
    {focus : TargetNameFocusᶠ₀ W X alpha} {Cᴿ⁺}
  → (edge : TargetAliasBoundaryᶠ₀ focus Cᴿ⁺)
  → Ty (Δᵉ Cᴿ⁺)
  → Ty (centerᶜ W)
boundaryTargetTyᶠ₀ {focus = focus} edge B =
  focusTargetTyᶠ₀ focus (substᵗ (aliasBoundarySubᶠ₀ edge) B)


BoundaryTypeImprecisionᶠ₀ : ∀ {Cᴸ Δᴿ}
    {Σᴿ : TyStore.TyStore Δᴿ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : Cᴸ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩} {X alpha}
    {focus : TargetNameFocusᶠ₀ W X alpha} {Cᴿ⁺}
  → TargetAliasBoundaryᶠ₀ focus Cᴿ⁺
  → Ty (Δᵉ Cᴸ)
  → Ty (Δᵉ Cᴿ⁺)
  → Set
BoundaryTypeImprecisionᶠ₀ {W = W} edge A B =
  I._⊢_⊑_ (marksᶜ W)
    (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A)
    (boundaryTargetTyᶠ₀ edge B)


-- This indexed datum is the normalized reveal-move rule header.  A term
-- relation can consume a premise at p and return the two revealed terms at q.
-- The conversions mention the direct endpoint entries supplied as variables;
-- equalities connect them to lookup, keeping constructor indices in constructor
-- form.

data AliasRevealMoveIndexᶠ₀ {Cᴸ Δᴿ}
    {Σᴿ : TyStore.TyStore Δᴿ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : Cᴸ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩} {X alpha}
    {focus : TargetNameFocusᶠ₀ W X alpha}
    {Γᴿ⁺ : TC.TermCtx (suc Δᴿ)}
    (edge : TargetAliasBoundaryᶠ₀ focus
      ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ⁺ ⟩) :
    ∀ {A B : Ty (Δᵉ Cᴸ)} {A′ B′ : Ty (suc Δᴿ)}
    → Conv↑ (Δᵉ Cᴸ) A B
    → Conv↑ (suc Δᴿ) A′ B′
    → BoundaryTypeImprecisionᶠ₀ edge A A′
    → BoundaryTypeImprecisionᶠ₀ edge B B′
    → Set where

  alias-reveal-move-indexᶠ₀ : ∀ {Rᴸ : Ty (Δᵉ Cᴸ)}
      {Rᴿ : Ty (suc Δᴿ)}
      {p : BoundaryTypeImprecisionᶠ₀ edge (＇ X) (＇ Fin.zero)}
      {q : BoundaryTypeImprecisionᶠ₀ edge Rᴸ Rᴿ}
    → lookupStore (Σᵉ Cᴸ) X ≡ Rᴸ
    → lookupStore (store-bind Σᴿ (＇ alpha)) Fin.zero ≡ Rᴿ
    → AliasRevealMoveIndexᶠ₀ edge
        (unseal X Rᴸ) (unseal Fin.zero Rᴿ) p q


-- Concrete strict-Lambda geometry.  The stable world has X and alpha in
-- distinct center cells.  Its source direct entry is X and alpha's direct
-- target entry is star.  The only new target edge is beta := alpha.

empty-context : Ctx
empty-context = ⟨ zero , store-empty , [] ⟩

target-alpha-context : Ctx
target-alpha-context = empty-context ,ˢ ★

source-X-context : Ctx
source-X-context = ⇑ᵉᵗ empty-context

target-alpha-world : empty-context ⊑ᶜ target-alpha-context
target-alpha-world = bindRightᶜ emptyᶜ ★ (inj₁ refl)

stable-world : source-X-context ⊑ᶜ target-alpha-context
stable-world = liftLeftᶜ target-alpha-world

source-X : TyVar (Δᵉ source-X-context)
source-X = Fin.zero

target-alpha : TyVar (Δᵉ target-alpha-context)
target-alpha = Fin.zero

stable-invariants : DirectWorldInvariantsᶜ stable-world
stable-invariants = directInvariantsᶜ stable-world

stable-X-alpha-separated :
  toRenameᵗ (ηᴸᶜ stable-world) source-X
    ≢ toRenameᵗ (ηᴿᶜ stable-world) target-alpha
stable-X-alpha-separated ()

stable-X-self : lookupStore (Σᵉ source-X-context) source-X ≡ ＇ source-X
stable-X-self = refl

stable-direct-representations-proof :
  lookupStore (Σᵉ source-X-context) source-X
    ⊑ᵀ⟨ stable-world ⟩
  lookupStore (Σᵉ target-alpha-context) target-alpha
stable-direct-representations-proof = I.X⊑★ refl

strict-lambda-focus :
  TargetNameFocusᶠ₀ stable-world source-X target-alpha
strict-lambda-focus =
  target-name-focusᶠ₀ stable-X-alpha-separated stable-X-self
    stable-direct-representations-proof

target-alpha-beta-context : Ctx
target-alpha-beta-context = target-alpha-context ,ˢ ＇ target-alpha

strict-lambda-boundary :
  TargetAliasBoundaryᶠ₀ strict-lambda-focus target-alpha-beta-context
strict-lambda-boundary = targetAliasBoundaryᶠ₀ strict-lambda-focus

target-beta : TyVar (Δᵉ target-alpha-beta-context)
target-beta = Fin.zero

target-alpha⁺ : TyVar (Δᵉ target-alpha-beta-context)
target-alpha⁺ = Fin.suc target-alpha

target-beta-entry :
  lookupStore (Σᵉ target-alpha-beta-context) target-beta ≡ ＇ target-alpha⁺
target-beta-entry = refl

target-alpha-entry :
  lookupStore (Σᵉ target-alpha-beta-context) target-alpha⁺ ≡ ★
target-alpha-entry = refl

strict-lambda-surface-name :
  BoundaryTypeImprecisionᶠ₀ strict-lambda-boundary
    (＇ source-X) (＇ target-beta)
strict-lambda-surface-name = I.X⊑X

strict-lambda-direct-edge :
  BoundaryTypeImprecisionᶠ₀ strict-lambda-boundary
    (lookupStore (Σᵉ source-X-context) source-X)
    (lookupStore (Σᵉ target-alpha-beta-context) target-beta)
strict-lambda-direct-edge = I.X⊑X

strict-lambda-reveal-move :
  AliasRevealMoveIndexᶠ₀ strict-lambda-boundary
    (unseal source-X (＇ source-X))
    (unseal target-beta (＇ target-alpha⁺))
    strict-lambda-surface-name strict-lambda-direct-edge
strict-lambda-reveal-move = alias-reveal-move-indexᶠ₀ refl refl
