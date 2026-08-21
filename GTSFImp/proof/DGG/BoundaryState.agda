{-# OPTIONS --safe #-}

module proof.DGG.BoundaryState where

-- File Charter:
--   * Defines the canonical boundary state over the two-context world:
--     ordinary base, pending exact target edge, and active focused edge.
--   * Defines functional target-type views for every state and the structural
--     lift and pending-to-active graphs used beneath type binders.
--   * Proves pending fresh-name exclusion and target-view functionality.
--   * Defines no term-imprecision judgment or target conversion action.  Its
--     active validity instead retains ExactTargetBoundary evidence indexed by
--     the direct representation and center view that such a rule must share.
--   * Depends on World, TargetAliasEdge, and TargetBoundary.

open import Data.Empty using (⊥)
open import Data.Fin using (suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans)

open import Types using
  (Ty; TyVar; ★; ＇_; ‵_; _⇒_; `∀; renameᵗ)
open import Consistency using (toRenameᵗ)
import Imprecision
open import CastTerms using (Ctx; Δᵉ; ⇑ᵉᵗ)
open import proof.DGG.World
open import proof.DGG.TargetAliasEdge
open import proof.DGG.TargetBoundary


data BoundaryState {Cᴸ C : Ctx} (W : Cᴸ ⊑ᶜ C) : Ctx → Set where

  base : BoundaryState W C

  pending : ∀ {C⁺ alpha beta alpha⁺}
    → ExactAliasEdge C C⁺ alpha beta alpha⁺
    → BoundaryState W C⁺

  active : ∀ {C⁺ X alpha beta alpha⁺}
      (focus : NameFocus W X alpha)
      (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺)
      (m : Mode edge)
    → ValidMode W focus edge m
    → BoundaryState W C⁺


data PendingTargetVarView : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
  → ExactAliasEdge C C⁺ alpha beta alpha⁺
  → TyVar (Δᵉ C⁺) → TyVar (centerᶜ W) → Set where

  pending-old : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {alpha : TyVar (Δᵉ C)} {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {edge Y Y⁺ Z}
    → edgeEmbed edge Y ≡ Y⁺
    → toRenameᵗ (ηᴿᶜ W) Y ≡ Z
    → PendingTargetVarView {Cᴸ} {C} {C⁺} {W}
        {alpha} {beta} {alpha⁺} edge Y⁺ Z


data StateTargetTypeView : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
  → (state : BoundaryState W C⁺)
  → Ty (Δᵉ C⁺) → Ty (centerᶜ W) → Set where

  base-view : ∀ {Cᴸ C : Ctx} {W : Cᴸ ⊑ᶜ C} {B Bᶜ}
    → renameᵗ (toRenameᵗ (ηᴿᶜ W)) B ≡ Bᶜ
    → StateTargetTypeView {Cᴸ} {C} {C} {W} base B Bᶜ

  pending-view-var : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {alpha : TyVar (Δᵉ C)} {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {edge Y Z}
    → PendingTargetVarView {Cᴸ} {C} {C⁺} {W}
        {alpha} {beta} {alpha⁺} edge Y Z
    → StateTargetTypeView {Cᴸ} {C} {C⁺} {W}
        (pending {alpha = alpha} {beta} {alpha⁺} edge) (＇ Y) (＇ Z)

  pending-view-base : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {alpha : TyVar (Δᵉ C)} {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {edge iota}
    → StateTargetTypeView {Cᴸ} {C} {C⁺} {W}
        (pending {alpha = alpha} {beta} {alpha⁺} edge)
        (‵ iota) (‵ iota)

  pending-view-star : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {alpha : TyVar (Δᵉ C)} {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {edge}
    → StateTargetTypeView {Cᴸ} {C} {C⁺} {W}
        (pending {alpha = alpha} {beta} {alpha⁺} edge) ★ ★

  pending-view-fun : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {alpha : TyVar (Δᵉ C)} {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {edge A B Aᶜ Bᶜ}
    → StateTargetTypeView {Cᴸ} {C} {C⁺} {W}
        (pending {alpha = alpha} {beta} {alpha⁺} edge) A Aᶜ
    → StateTargetTypeView {Cᴸ} {C} {C⁺} {W}
        (pending {alpha = alpha} {beta} {alpha⁺} edge) B Bᶜ
    → StateTargetTypeView {Cᴸ} {C} {C⁺} {W}
        (pending {alpha = alpha} {beta} {alpha⁺} edge)
        (A ⇒ B) (Aᶜ ⇒ Bᶜ)

  pending-view-all : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {alpha : TyVar (Δᵉ C)} {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {edge A B}
    → StateTargetTypeView
        {⇑ᵉᵗ Cᴸ} {⇑ᵉᵗ C} {⇑ᵉᵗ C⁺}
        {liftBothᶜ Imprecision.X⊑X W}
        (pending {alpha = suc alpha} {suc beta} {suc alpha⁺}
          (liftAliasEdge edge)) A B
    → StateTargetTypeView {Cᴸ} {C} {C⁺} {W}
        (pending {alpha = alpha} {beta} {alpha⁺} edge)
        (`∀ A) (`∀ B)

  active-view : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m ok B Bᶜ}
    → TargetTypeView {Cᴸ} {C} {C⁺} {W} {X} {alpha}
        {beta} {alpha⁺} focus edge m B Bᶜ
    → StateTargetTypeView {Cᴸ} {C} {C⁺} {W}
        (active {X = X} {alpha} {beta} {alpha⁺}
          focus edge m ok) B Bᶜ


data BoundaryStateLift : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
  → (state : BoundaryState W C⁺)
  → BoundaryState (liftBothᶜ Imprecision.X⊑X W) (⇑ᵉᵗ C⁺)
  → Set where

  lift-base-state : ∀ {Cᴸ C : Ctx} {W : Cᴸ ⊑ᶜ C}
    → BoundaryStateLift {Cᴸ} {C} {C} {W} base base

  lift-pending-state : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {alpha : TyVar (Δᵉ C)} {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      {edge : ExactAliasEdge C C⁺ alpha beta alpha⁺}
    → BoundaryStateLift {Cᴸ} {C} {C⁺} {W}
        (pending edge) (pending (liftAliasEdge edge))

  lift-active-state : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)} {focus edge m ok}
      {ok⁺ : ValidMode (liftBothᶜ Imprecision.X⊑X W)
        (liftNameFocus focus) (liftAliasEdge edge) (liftMode m)}
    → BoundaryStateLift {Cᴸ} {C} {C⁺} {W}
        (active {X = X} {alpha} {beta} {alpha⁺} focus edge m ok)
        (active {X = suc X} {alpha = suc alpha} {beta = suc beta}
          {alpha⁺ = suc alpha⁺} (liftNameFocus focus)
          (liftAliasEdge edge) (liftMode m) ok⁺)


data BoundaryActivation : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C}
  → BoundaryState W C⁺ → BoundaryState W C⁺ → Set where

  activate-pending : ∀ {Cᴸ C C⁺ : Ctx} {W : Cᴸ ⊑ᶜ C}
      {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar (Δᵉ C)}
      {beta alpha⁺ : TyVar (Δᵉ C⁺)}
      (focus : NameFocus W X alpha)
      (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺)
    → BoundaryActivation
        (pending {alpha = alpha} {beta} {alpha⁺} edge)
        (active {X = X} {alpha} {beta} {alpha⁺}
          focus edge stable stable-valid)


pending-target-var-view-functional : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {edge : ExactAliasEdge C C⁺ alpha beta alpha⁺} {Y Z Z′}
  → PendingTargetVarView {Cᴸ} {C} {C⁺} {W}
      {alpha} {beta} {alpha⁺} edge Y Z
  → PendingTargetVarView {Cᴸ} {C} {C⁺} {W}
      {alpha} {beta} {alpha⁺} edge Y Z′
  → Z ≡ Z′
pending-target-var-view-functional {W = W} {edge = edge}
    (pending-old edge-eq center-eq)
    (pending-old edge-eq′ center-eq′) =
  trans (sym center-eq)
    (trans (cong (toRenameᵗ (ηᴿᶜ W)) old-eq) center-eq′)
  where
  old-eq = edgeEmbed-injective edge (trans edge-eq (sym edge-eq′))


pending-beta-unavailable : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C} {alpha : TyVar (Δᵉ C)}
    {beta alpha⁺ : TyVar (Δᵉ C⁺)}
    {edge : ExactAliasEdge C C⁺ alpha beta alpha⁺} {Z}
  → PendingTargetVarView {Cᴸ} {C} {C⁺} {W}
      {alpha} {beta} {alpha⁺} edge beta Z
  → ⊥
pending-beta-unavailable {edge = edge}
    (pending-old {Y = Y} edge-eq center-eq) =
  edge-beta-fresh edge Y edge-eq


state-target-type-view-functional : ∀ {Cᴸ C C⁺ : Ctx}
    {W : Cᴸ ⊑ᶜ C} {state : BoundaryState W C⁺} {A B B′}
  → StateTargetTypeView state A B
  → StateTargetTypeView state A B′
  → B ≡ B′
state-target-type-view-functional (base-view eq) (base-view eq′) =
  trans (sym eq) eq′
state-target-type-view-functional (pending-view-var view)
    (pending-view-var view′) =
  cong ＇_ (pending-target-var-view-functional view view′)
state-target-type-view-functional pending-view-base pending-view-base = refl
state-target-type-view-functional pending-view-star pending-view-star = refl
state-target-type-view-functional (pending-view-fun view-A view-B)
    (pending-view-fun view-A′ view-B′) =
  cong₂ _⇒_ (state-target-type-view-functional view-A view-A′)
    (state-target-type-view-functional view-B view-B′)
state-target-type-view-functional (pending-view-all view)
    (pending-view-all view′) =
  cong `∀ (state-target-type-view-functional view view′)
state-target-type-view-functional (active-view view)
    (active-view view′) =
  target-type-view-functional view view′
