module strong.ColorPreservation where

-- Strong System F v7 — public color-preservation statement.

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ; scopeᵗ)
open import strong.Terms using (_∣_⊢_⦂_)
open import strong.Reduction using (_⊢_-→*_)
open import strong.Residual
import strong.proof.ColorPreservation as Proof

ColorPreservation : Set
ColorPreservation = ∀ {C M D N A}
  {rs : [] ⊢ plug C M -→* plug D N}
  → [] ∣ [] ⊢ plug C M ⦂ A
  → Residuals rs C M D N
  → ∀ {Δ₁ Δ₂ : Ctxᵗ}
  → [] ⊢C C ⊣ Δ₁
  → [] ⊢C D ⊣ Δ₂
  → scopeᵗ Δ₁ ≡ scopeᵗ Δ₂

color-preservation : ColorPreservation
color-preservation typing residual source target =
  Proof.color-preservation residual source target
