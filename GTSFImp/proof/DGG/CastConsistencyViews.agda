module proof.DGG.CastConsistencyViews where

-- File Charter:
--   * Provides small syntactic views of consistency casts used by LG-3
--     CTI inversion consumers.
--   * The views expose canonical variable/base tag and projection shapes,
--     closing the hidden inst/gen occurrence alternatives by inversion.
--   * Depends only on the core consistency grammar and type syntax; it does
--     not change the cast-term imprecision relation.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; idᵍ; _!; ？_;
   _↦_; ∀ᶜ_; inst_; gen_; bot-elim; bot-intro;
   flipᵐ; extᵐ; instᵐ; genᵐ)

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

------------------------------------------------------------------------
-- Function-ground tags and projections
------------------------------------------------------------------------

data FunTagCastSyntax {Δ : TyCtx} (ν : Env∼ Δ) (A B : Ty Δ) :
    ν ⊢ A ⇒ B ∼ ★ → Set where
  fun-tag-cast-syntax :
      ∀ {★∼A : flipᵐ ν ⊢ ★ ∼ A} {B∼★ : ν ⊢ B ∼ ★}
        {⇒∼★ : ν ⊢ (★ ⇒ ★) ∼★} {Ans}
    → FunTagCastSyntax ν A B
        (_! ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = ⇒∼★ ⦄
          (★∼A ↦ B∼★) ⦃ Ans = Ans ⦄)


fun-tag-cast-view : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {A B : Ty Δ}
  → (c : ν ⊢ A ⇒ B ∼ ★)
  → FunTagCastSyntax ν A B c
fun-tag-cast-view
    (_! ⦃ Gᵍ = ★⇒★ ⦄ (_ ↦ _)) =
  fun-tag-cast-syntax
fun-tag-cast-view
    (_! {G = `∀ ★} (gen_ ⦃ z∈B = () ⦄ _ _))


data FunProjectCastSyntax {Δ : TyCtx} (ν : Env∼ Δ) (A B : Ty Δ) :
    ν ⊢ ★ ∼ A ⇒ B → Set where
  fun-project-cast-syntax :
      ∀ {A∼★ : flipᵐ ν ⊢ A ∼ ★} {★∼B : ν ⊢ ★ ∼ B}
        {★∼⇒ : ν ⊢★∼ (★ ⇒ ★)} {Bns}
    → FunProjectCastSyntax ν A B
        (？_ ⦃ Gᵍ = ★⇒★ ⦄ ⦃ ★∼G = ★∼⇒ ⦄
          (A∼★ ↦ ★∼B) ⦃ Bns = Bns ⦄)


fun-project-cast-view : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {A B : Ty Δ}
  → (c : ν ⊢ ★ ∼ A ⇒ B)
  → FunProjectCastSyntax ν A B c
fun-project-cast-view
    (？_ ⦃ Gᵍ = ★⇒★ ⦄ (_ ↦ _)) =
  fun-project-cast-syntax
fun-project-cast-view
    (？_ {G = `∀ ★} (inst_ ⦃ z∈A = () ⦄ _ _))

------------------------------------------------------------------------
-- Universal-ground tags and projections
------------------------------------------------------------------------

data AllTagCastSyntax {Δ : TyCtx} (ν : Env∼ Δ) :
    (A : Ty (Nat.suc Δ)) → ν ⊢ `∀ A ∼ ★ → Set where
  all-tag-cast-syntax :
      ∀ {A : Ty (Nat.suc Δ)} {A∼★ : extᵐ ν ⊢ A ∼ ★}
        {∀∼★ : ν ⊢ (`∀ ★) ∼★} {Ans}
    → AllTagCastSyntax ν A
        (_! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄
          (∀ᶜ A∼★) ⦃ Ans = Ans ⦄)
  all-tag-inst-syntax :
      ∀ {A : Ty (Nat.suc Δ)}
        {G : Ty Δ} {Gᵍ : Ground G} {G∼★ : ν ⊢ G ∼★}
        {Anv} {z∈A} {A∼G : instᵐ ν ⊢ A ∼ ⇑ᵗ G}
        {G≢★} {Ans}
    → AllTagCastSyntax ν A
        (_! ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
          ((inst_ ⦃ Anv = Anv ⦄ ⦃ z∈A = z∈A ⦄ A∼G) G≢★)
          ⦃ Ans = Ans ⦄)
  all-tag-bot-elim-syntax :
      ∀ {∀∼★ : ν ⊢ (`∀ ★) ∼★} {Ans}
    → AllTagCastSyntax ν (＇ Fin.zero)
        (_! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄
          bot-elim ⦃ Ans = Ans ⦄)


all-tag-cast-view : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
    {A : Ty (Nat.suc Δ)}
  → (c : ν ⊢ `∀ A ∼ ★)
  → AllTagCastSyntax ν A c
all-tag-cast-view
    (_! ⦃ Gᵍ = ∀★ ⦄ (∀ᶜ _)) =
  all-tag-cast-syntax
all-tag-cast-view
    (_! (inst_ _ _)) =
  all-tag-inst-syntax
all-tag-cast-view
    (_! ⦃ Gᵍ = ∀★ ⦄ bot-elim) =
  all-tag-bot-elim-syntax
all-tag-cast-view
    (_! {G = `∀ ★} (gen_ ⦃ z∈B = () ⦄ _ _))
all-tag-cast-view
    (inst_ _ ★≢★) =
  ⊥-elim (★≢★ refl)


data AllProjectCastSyntax {Δ : TyCtx} (ν : Env∼ Δ) :
    (A : Ty (Nat.suc Δ)) → ν ⊢ ★ ∼ `∀ A → Set where
  all-project-cast-syntax :
      ∀ {A : Ty (Nat.suc Δ)} {★∼A : extᵐ ν ⊢ ★ ∼ A}
        {★∼∀ : ν ⊢★∼ (`∀ ★)} {Bns}
    → AllProjectCastSyntax ν A
        (？_ ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄
          (∀ᶜ ★∼A) ⦃ Bns = Bns ⦄)
  all-project-gen-syntax :
      ∀ {A : Ty (Nat.suc Δ)}
        {G : Ty Δ} {Gᵍ : Ground G} {★∼G : ν ⊢★∼ G}
        {Bnv} {z∈A} {G∼A : genᵐ ν ⊢ ⇑ᵗ G ∼ A}
        {G≢★} {Bns}
    → AllProjectCastSyntax ν A
        (？_ ⦃ Gᵍ = Gᵍ ⦄ ⦃ ★∼G = ★∼G ⦄
          ((gen_ ⦃ Bnv = Bnv ⦄ ⦃ z∈B = z∈A ⦄ G∼A) G≢★)
          ⦃ Bns = Bns ⦄)
  all-project-bot-intro-syntax :
      ∀ {★∼∀ : ν ⊢★∼ (`∀ ★)} {Bns}
    → AllProjectCastSyntax ν (＇ Fin.zero)
        (？_ ⦃ Gᵍ = ∀★ ⦄ ⦃ ★∼G = ★∼∀ ⦄
          bot-intro ⦃ Bns = Bns ⦄)


all-project-cast-view : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
    {A : Ty (Nat.suc Δ)}
  → (c : ν ⊢ ★ ∼ `∀ A)
  → AllProjectCastSyntax ν A c
all-project-cast-view
    (？_ ⦃ Gᵍ = ∀★ ⦄ (∀ᶜ _)) =
  all-project-cast-syntax
all-project-cast-view
    (？_ (gen_ _ _)) =
  all-project-gen-syntax
all-project-cast-view
    (？_ ⦃ Gᵍ = ∀★ ⦄ bot-intro) =
  all-project-bot-intro-syntax
all-project-cast-view
    (？_ {G = `∀ ★} (inst_ ⦃ z∈A = () ⦄ _ _))
all-project-cast-view
    (gen_ _ ★≢★) =
  ⊥-elim (★≢★ refl)
