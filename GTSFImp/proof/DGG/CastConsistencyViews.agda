module proof.DGG.CastConsistencyViews where

-- File Charter:
--   * Provides small syntactic views of consistency casts used by LG-3
--     CTI inversion consumers.
--   * The views expose canonical variable/base tag and projection shapes,
--     closing the hidden inst/gen occurrence alternatives by inversion.
--   * Depends only on the core consistency grammar and type syntax; it does
--     not change the cast-term imprecision relation.

import Data.Fin as Fin

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; idᵍ; _!; ？_;
   inst_; gen_)

------------------------------------------------------------------------
-- Variable tags and projections
------------------------------------------------------------------------

data VarTagCastSyntax {Δ : TyCtx} (ν : Env∼ Δ) (X : TyVar Δ) :
    ν ⊢ ＇ X ∼ ★ → Set where
  var-tag-cast-syntax :
      ∀ {X∼★ : ν ⊢ ＇ X ∼★} {Ans}
    → VarTagCastSyntax ν X
        (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ ⦄
          (id (＇ X)) ⦃ Ans = Ans ⦄)


var-tag-cast-view : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {X : TyVar Δ}
  → (c : ν ⊢ ＇ X ∼ ★)
  → VarTagCastSyntax ν X c
var-tag-cast-view
    (_! ⦃ Gᵍ = ＇ X ⦄ (id (＇ .X))) =
  var-tag-cast-syntax
var-tag-cast-view
    (_! {G = `∀ ★} (gen_ ⦃ z∈B = () ⦄ _ _))


data VarProjectCastSyntax {Δ : TyCtx} (ν : Env∼ Δ) (X : TyVar Δ) :
    ν ⊢ ★ ∼ ＇ X → Set where
  var-project-cast-syntax :
      ∀ {★∼X : ν ⊢★∼ ＇ X} {Bns}
    → VarProjectCastSyntax ν X
        (？_ ⦃ Gᵍ = ＇ X ⦄ ⦃ ★∼G = ★∼X ⦄
          (id (＇ X)) ⦃ Bns = Bns ⦄)


var-project-cast-view : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {X : TyVar Δ}
  → (c : ν ⊢ ★ ∼ ＇ X)
  → VarProjectCastSyntax ν X c
var-project-cast-view
    (？_ ⦃ Gᵍ = ＇ X ⦄ (id (＇ .X))) =
  var-project-cast-syntax
var-project-cast-view
    (？_ {G = `∀ ★} (inst_ ⦃ z∈A = () ⦄ _ _))

------------------------------------------------------------------------
-- Base tags and projections
------------------------------------------------------------------------

data BaseTagCastSyntax {Δ : TyCtx} (ν : Env∼ Δ) (ι : Base) :
    ν ⊢ ‵ ι ∼ ★ → Set where
  base-tag-cast-syntax :
      ∀ {ι∼★ : ν ⊢ ‵ ι ∼★} {Ans}
    → BaseTagCastSyntax ν ι
        (_! ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = ι∼★ ⦄
          (id (‵ ι)) ⦃ Ans = Ans ⦄)


base-tag-cast-view : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {ι : Base}
  → (c : ν ⊢ ‵ ι ∼ ★)
  → BaseTagCastSyntax ν ι c
base-tag-cast-view
    (_! ⦃ Gᵍ = ‵ ι ⦄ (id (‵ .ι))) =
  base-tag-cast-syntax
base-tag-cast-view
    (_! {G = `∀ ★} (gen_ ⦃ z∈B = () ⦄ _ _))


data BaseProjectCastSyntax {Δ : TyCtx} (ν : Env∼ Δ) (ι : Base) :
    ν ⊢ ★ ∼ ‵ ι → Set where
  base-project-cast-syntax :
      ∀ {★∼ι : ν ⊢★∼ ‵ ι} {Bns}
    → BaseProjectCastSyntax ν ι
        (？_ ⦃ Gᵍ = ‵ ι ⦄ ⦃ ★∼G = ★∼ι ⦄
          (id (‵ ι)) ⦃ Bns = Bns ⦄)


base-project-cast-view : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {ι : Base}
  → (c : ν ⊢ ★ ∼ ‵ ι)
  → BaseProjectCastSyntax ν ι c
base-project-cast-view
    (？_ ⦃ Gᵍ = ‵ ι ⦄ (id (‵ .ι))) =
  base-project-cast-syntax
base-project-cast-view
    (？_ {G = `∀ ★} (inst_ ⦃ z∈A = () ⦄ _ _))
