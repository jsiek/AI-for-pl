module ConversionIndexCompatibility where

-- File Charter:
--   * Relates type-imprecision indices before and after hereditary
--     reveal/conceal replacement on the source, target, or both endpoints.
--   * Keeps variable names and stored types explicit, including the different
--     binder schedules for matched `∀ⁱ` and source-only `ν` structure.
--   * Contains no conversion typing, term imprecision, or simulation proof.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc)

open import ImprecisionComposition using (⌊_⌋)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; NonVar
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; id★
  ; idˣ
  ; idι
  ; _↦_
  ; ∀ⁱ_
  ; tag_
  ; tag_⇛_
  ; tagˣ
  ; ν
  )
open import Types using (Base; Ty; TyCtx; TyVar; occurs; ⇑ᵗ)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ)


infix 4 _[_↦_]ᴸ_

data _[_↦_]ᴸ_ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} :
    ∀ {A A′ B} →
    Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
    TyVar →
    Ty →
    Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ →
    Set where

  replace-left-id★ :
    ∀ {α : TyVar} {X : Ty} →
    id★ [ α ↦ X ]ᴸ id★

  replace-left-idˣ :
    ∀ {α Y Z : TyVar} {X : Ty}
      {x∈ x∈′ : (Y ˣ⊑ˣ Z) ∈ Φ}
      {Y<Δᴸ Y<Δᴸ′ : Y < Δᴸ}
      {Z<Δᴿ Z<Δᴿ′ : Z < Δᴿ} →
    idˣ {X = Y} {Y = Z} x∈ Y<Δᴸ Z<Δᴿ
      [ α ↦ X ]ᴸ
    idˣ {X = Y} {Y = Z} x∈′ Y<Δᴸ′ Z<Δᴿ′

  replace-left-variable :
    ∀ {α Y : TyVar} {X : Ty}
      {x∈ : (α ˣ⊑ˣ Y) ∈ Φ}
      {α<Δᴸ : α < Δᴸ} {Y<Δᴿ : Y < Δᴿ}
      (q : Φ ∣ Δᴸ ⊢ X ⊑ Types.＇ Y ⊣ Δᴿ) →
    idˣ x∈ α<Δᴸ Y<Δᴿ [ α ↦ X ]ᴸ q

  replace-left-idι :
    ∀ {α : TyVar} {X : Ty} {ι : Base} →
    idι {ι = ι} [ α ↦ X ]ᴸ idι {ι = ι}

  replace-left-function :
    ∀ {α : TyVar} {X A₁ A₂ A₁′ A₂′ B₁ B₂ : Ty}
      {p₁ : Φ ∣ Δᴸ ⊢ A₁ ⊑ A₁′ ⊣ Δᴿ}
      {p₂ : Φ ∣ Δᴸ ⊢ A₂ ⊑ A₂′ ⊣ Δᴿ}
      {q₁ : Φ ∣ Δᴸ ⊢ B₁ ⊑ A₁′ ⊣ Δᴿ}
      {q₂ : Φ ∣ Δᴸ ⊢ B₂ ⊑ A₂′ ⊣ Δᴿ} →
    p₁ [ α ↦ X ]ᴸ q₁ →
    p₂ [ α ↦ X ]ᴸ q₂ →
    (p₁ ↦ p₂) [ α ↦ X ]ᴸ (q₁ ↦ q₂)

  replace-left-∀ :
    ∀ {α : TyVar} {X A A′ B : Ty}
      {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
      {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ suc Δᴿ} →
    p [ suc α ↦ ⇑ᵗ X ]ᴸ q →
    (∀ⁱ p) [ α ↦ X ]ᴸ (∀ⁱ q)

  replace-left-tag :
    ∀ {α : TyVar} {X : Ty} {ι : Base} →
    tag ι [ α ↦ X ]ᴸ tag ι

  replace-left-function-tag :
    ∀ {α : TyVar} {X A₁ A₂ B₁ B₂ : Ty}
      {p₁ : Φ ∣ Δᴸ ⊢ A₁ ⊑ Types.★ ⊣ Δᴿ}
      {p₂ : Φ ∣ Δᴸ ⊢ A₂ ⊑ Types.★ ⊣ Δᴿ}
      {q₁ : Φ ∣ Δᴸ ⊢ B₁ ⊑ Types.★ ⊣ Δᴿ}
      {q₂ : Φ ∣ Δᴸ ⊢ B₂ ⊑ Types.★ ⊣ Δᴿ} →
    p₁ [ α ↦ X ]ᴸ q₁ →
    p₂ [ α ↦ X ]ᴸ q₂ →
    tag p₁ ⇛ p₂ [ α ↦ X ]ᴸ tag q₁ ⇛ q₂

  replace-left-tagˣ :
    ∀ {α Y : TyVar} {X : Ty}
      {x∈ x∈′ : Y ˣ⊑★ ∈ Φ}
      {Y<Δᴸ Y<Δᴸ′ : Y < Δᴸ} →
    tagˣ {X = Y} x∈ Y<Δᴸ [ α ↦ X ]ᴸ tagˣ x∈′ Y<Δᴸ′

  replace-left-seal :
    ∀ {α : TyVar} {X : Ty}
      {x∈ : α ˣ⊑★ ∈ Φ} {α<Δᴸ : α < Δᴸ}
      (q : Φ ∣ Δᴸ ⊢ X ⊑ Types.★ ⊣ Δᴿ) →
    tagˣ x∈ α<Δᴸ [ α ↦ X ]ᴸ q

  replace-left-ν :
    ∀ {α : TyVar} {X A A′ B : Ty}
      {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ}
      {safe : NonVar A} {safe′ : NonVar B}
      {occ : occurs zero A ≡ true}
      {occ′ : occurs zero B ≡ true} →
    p [ suc α ↦ ⇑ᵗ X ]ᴸ q →
    ν safe occ p [ α ↦ X ]ᴸ ν safe′ occ′ q


infix 4 _[_↦_]ᴿ_

data _[_↦_]ᴿ_ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} :
    ∀ {A A′ B′} →
    Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
    TyVar →
    Ty →
    Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ →
    Set where

  replace-right-id★ :
    ∀ {β : TyVar} {X′ : Ty} →
    id★ [ β ↦ X′ ]ᴿ id★

  replace-right-idˣ :
    ∀ {β Y Z : TyVar} {X′ : Ty}
      {x∈ x∈′ : (Y ˣ⊑ˣ Z) ∈ Φ}
      {Y<Δᴸ Y<Δᴸ′ : Y < Δᴸ}
      {Z<Δᴿ Z<Δᴿ′ : Z < Δᴿ} →
    idˣ {X = Y} {Y = Z} x∈ Y<Δᴸ Z<Δᴿ
      [ β ↦ X′ ]ᴿ
    idˣ {X = Y} {Y = Z} x∈′ Y<Δᴸ′ Z<Δᴿ′

  replace-right-variable :
    ∀ {β Y : TyVar} {X′ : Ty}
      {x∈ : (Y ˣ⊑ˣ β) ∈ Φ}
      {Y<Δᴸ : Y < Δᴸ} {β<Δᴿ : β < Δᴿ}
      (q : Φ ∣ Δᴸ ⊢ Types.＇ Y ⊑ X′ ⊣ Δᴿ) →
    idˣ x∈ Y<Δᴸ β<Δᴿ [ β ↦ X′ ]ᴿ q

  replace-right-idι :
    ∀ {β : TyVar} {X′ : Ty} {ι : Base} →
    idι {ι = ι} [ β ↦ X′ ]ᴿ idι {ι = ι}

  replace-right-function :
    ∀ {β : TyVar} {X′ A₁ A₂ A₁′ A₂′ B₁′ B₂′ : Ty}
      {p₁ : Φ ∣ Δᴸ ⊢ A₁ ⊑ A₁′ ⊣ Δᴿ}
      {p₂ : Φ ∣ Δᴸ ⊢ A₂ ⊑ A₂′ ⊣ Δᴿ}
      {q₁ : Φ ∣ Δᴸ ⊢ A₁ ⊑ B₁′ ⊣ Δᴿ}
      {q₂ : Φ ∣ Δᴸ ⊢ A₂ ⊑ B₂′ ⊣ Δᴿ} →
    p₁ [ β ↦ X′ ]ᴿ q₁ →
    p₂ [ β ↦ X′ ]ᴿ q₂ →
    (p₁ ↦ p₂) [ β ↦ X′ ]ᴿ (q₁ ↦ q₂)

  replace-right-∀ :
    ∀ {β : TyVar} {X′ A A′ B′ : Ty}
      {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
      {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ B′ ⊣ suc Δᴿ} →
    p [ suc β ↦ ⇑ᵗ X′ ]ᴿ q →
    (∀ⁱ p) [ β ↦ X′ ]ᴿ (∀ⁱ q)

  replace-right-tag :
    ∀ {β : TyVar} {X′ : Ty} {ι : Base} →
    tag ι [ β ↦ X′ ]ᴿ tag ι

  replace-right-function-tag :
    ∀ {β : TyVar} {X′ A₁ A₂ : Ty}
      {p₁ q₁ : Φ ∣ Δᴸ ⊢ A₁ ⊑ Types.★ ⊣ Δᴿ}
      {p₂ q₂ : Φ ∣ Δᴸ ⊢ A₂ ⊑ Types.★ ⊣ Δᴿ} →
    p₁ [ β ↦ X′ ]ᴿ q₁ →
    p₂ [ β ↦ X′ ]ᴿ q₂ →
    tag p₁ ⇛ p₂ [ β ↦ X′ ]ᴿ tag q₁ ⇛ q₂

  replace-right-tagˣ :
    ∀ {β Y : TyVar} {X′ : Ty}
      {x∈ x∈′ : Y ˣ⊑★ ∈ Φ}
      {Y<Δᴸ Y<Δᴸ′ : Y < Δᴸ} →
    tagˣ {X = Y} x∈ Y<Δᴸ [ β ↦ X′ ]ᴿ tagˣ x∈′ Y<Δᴸ′

  replace-right-ν :
    ∀ {β : TyVar} {X′ A A′ B′ : Ty}
      {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
      {safe safe′ : NonVar A}
      {occ occ′ : occurs zero A ≡ true} →
    p [ β ↦ X′ ]ᴿ q →
    ν safe occ p [ β ↦ X′ ]ᴿ ν safe′ occ′ q


infix 4 _[_↦_⊑⟨_⟩_↤_]ᴾ_

data _[_↦_⊑⟨_⟩_↤_]ᴾ_
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} :
    ∀ {A A′ B B′ X X′} →
    Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
    (α : TyVar) →
    Ty →
    Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ →
    Ty →
    (β : TyVar) →
    Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
    Set where

  replace-paired-id★ :
    ∀ {α β : TyVar} {X X′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
    id★ [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ id★

  replace-paired-idˣ :
    ∀ {α β Y Z : TyVar} {X X′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {x∈ x∈′ : (Y ˣ⊑ˣ Z) ∈ Φ}
      {Y<Δᴸ Y<Δᴸ′ : Y < Δᴸ}
      {Z<Δᴿ Z<Δᴿ′ : Z < Δᴿ} →
    idˣ {X = Y} {Y = Z} x∈ Y<Δᴸ Z<Δᴿ
      [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ
    idˣ {X = Y} {Y = Z} x∈′ Y<Δᴸ′ Z<Δᴿ′

  replace-paired-variables :
    ∀ {α β : TyVar} {X X′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {x∈ : (α ˣ⊑ˣ β) ∈ Φ}
      {α<Δᴸ : α < Δᴸ} {β<Δᴿ : β < Δᴿ} →
    ⌊ q ⌋ ≡ ⌊ pX ⌋ →
    idˣ x∈ α<Δᴸ β<Δᴿ
      [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ
    q

  replace-paired-idι :
    ∀ {α β : TyVar} {X X′ : Ty} {ι : Base}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
    idι {ι = ι}
      [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ
    idι {ι = ι}

  replace-paired-function :
    ∀ {α β : TyVar}
      {X X′ A₁ A₂ A₁′ A₂′ B₁ B₂ B₁′ B₂′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {p₁ : Φ ∣ Δᴸ ⊢ A₁ ⊑ A₁′ ⊣ Δᴿ}
      {p₂ : Φ ∣ Δᴸ ⊢ A₂ ⊑ A₂′ ⊣ Δᴿ}
      {q₁ : Φ ∣ Δᴸ ⊢ B₁ ⊑ B₁′ ⊣ Δᴿ}
      {q₂ : Φ ∣ Δᴸ ⊢ B₂ ⊑ B₂′ ⊣ Δᴿ} →
    p₁ [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q₁ →
    p₂ [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q₂ →
    (p₁ ↦ p₂)
      [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ
    (q₁ ↦ q₂)

  replace-paired-∀ :
    ∀ {α β : TyVar} {X X′ A A′ B B′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
      {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ} →
    p
      [ suc α ↦ ⇑ᵗ X
      ⊑⟨ ⊑-lift∀ᵢ pX ⟩
      ⇑ᵗ X′ ↤ suc β ]ᴾ
    q →
    (∀ⁱ p) [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ (∀ⁱ q)

  replace-paired-tag :
    ∀ {α β : TyVar} {X X′ : Ty} {ι : Base}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
    tag ι [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ tag ι

  replace-paired-function-tag :
    ∀ {α β : TyVar} {X X′ A₁ A₂ B₁ B₂ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {p₁ : Φ ∣ Δᴸ ⊢ A₁ ⊑ Types.★ ⊣ Δᴿ}
      {p₂ : Φ ∣ Δᴸ ⊢ A₂ ⊑ Types.★ ⊣ Δᴿ}
      {q₁ : Φ ∣ Δᴸ ⊢ B₁ ⊑ Types.★ ⊣ Δᴿ}
      {q₂ : Φ ∣ Δᴸ ⊢ B₂ ⊑ Types.★ ⊣ Δᴿ} →
    p₁ [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q₁ →
    p₂ [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q₂ →
    tag p₁ ⇛ p₂
      [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ
    tag q₁ ⇛ q₂

  replace-paired-tagˣ :
    ∀ {α β Y : TyVar} {X X′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {x∈ x∈′ : Y ˣ⊑★ ∈ Φ}
      {Y<Δᴸ Y<Δᴸ′ : Y < Δᴸ} →
    tagˣ {X = Y} x∈ Y<Δᴸ
      [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ
    tagˣ x∈′ Y<Δᴸ′

  replace-paired-ν :
    ∀ {α β : TyVar} {X X′ A A′ B B′ : Ty}
      {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
      {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {safe : NonVar A} {safe′ : NonVar B}
      {occ : occurs zero A ≡ true}
      {occ′ : occurs zero B ≡ true} →
    p
      [ suc α ↦ ⇑ᵗ X
      ⊑⟨ ⊑-source-liftνᵢ pX ⟩
      X′ ↤ β ]ᴾ
    q →
    ν safe occ p
      [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ
    ν safe′ occ′ q
