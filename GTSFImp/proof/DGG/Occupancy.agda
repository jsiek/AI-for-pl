{-# OPTIONS --safe #-}

module proof.DGG.Occupancy where

-- File Charter:
--   * Decides whether a center position, or the image of a source variable,
--     has a target occupant in the canonical complete-context world.
--   * Records the direct fresh-position facts for source-only, target-only,
--     and paired world changes.
--   * Contains no compatibility occupancy predicates or transports through
--     obsolete world reconstructions.

open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
import Data.Fin.Properties as FinP
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Types using (Ty; TyVar)
open import Imprecision using (VarImp)
open import CastTerms using (Ctx; Δᵉ)
open import proof.DGG.World


fin-image? : ∀ {m n}
  → (f : Fin.Fin m → Fin.Fin n)
  → (Z : Fin.Fin n)
  → Dec (Σ[ Y ∈ Fin.Fin m ] f Y ≡ Z)
fin-image? {m = Nat.zero} f Z = no (λ { (() , eq) })
fin-image? {m = Nat.suc m} f Z with FinP._≟_ (f Fin.zero) Z
fin-image? {m = Nat.suc m} f Z | yes eq = yes (Fin.zero , eq)
fin-image? {m = Nat.suc m} f Z | no neq
    with fin-image? (λ Y → f (Fin.suc Y)) Z
fin-image? {m = Nat.suc m} f Z | no neq | yes (Y , eq) =
  yes (Fin.suc Y , eq)
fin-image? {m = Nat.suc m} f Z | no neq | no no-tail =
  no no-image
  where
  no-image : (Σ[ Y ∈ Fin.Fin (Nat.suc m) ] f Y ≡ Z) → ⊥
  no-image (Fin.zero , eq) = neq eq
  no-image (Fin.suc Y , eq) = no-tail (Y , eq)


occupied? : ∀ {Γᴸ Γᴿ : Ctx}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → (Z : TyVar (centerᶜ γ))
  → Dec (Σ[ Y ∈ TyVar (Δᵉ Γᴿ) ]
      toRenameⁱ (ηᴿᶜ γ) Y ≡ Z)
occupied? γ Z = fin-image? (toRenameⁱ (ηᴿᶜ γ)) Z


occupied-at-source? : ∀ {Γᴸ Γᴿ : Ctx}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → (X : TyVar (Δᵉ Γᴸ))
  → Dec (Σ[ Y ∈ TyVar (Δᵉ Γᴿ) ]
      toRenameⁱ (ηᴿᶜ γ) Y ≡ toRenameⁱ (ηᴸᶜ γ) X)
occupied-at-source? γ X = occupied? γ (toRenameⁱ (ηᴸᶜ γ) X)


no-target-at-source? : ∀ {Γᴸ Γᴿ : Ctx}
  → (γ : Γᴸ ⊑ᶜ Γᴿ)
  → (X : TyVar (Δᵉ Γᴸ))
  → Dec (∀ Y → toRenameⁱ (ηᴿᶜ γ) Y ≢ toRenameⁱ (ηᴸᶜ γ) X)
no-target-at-source? γ X with occupied-at-source? γ X
no-target-at-source? γ X | yes (Y , aligned) =
  no (λ no-target → no-target Y aligned)
no-target-at-source? γ X | no no-occupant =
  yes (λ Y aligned → no-occupant (Y , aligned))


------------------------------------------------------------------------
-- Fresh positions introduced by world changes
------------------------------------------------------------------------

liftLeft-fresh-no-target : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
  → ∀ Y → toRenameⁱ (ηᴿᶜ (liftLeftᶜ γ)) Y
      ≢ toRenameⁱ (ηᴸᶜ (liftLeftᶜ γ)) Fin.zero
liftLeft-fresh-no-target Y ()


bindLeft-fresh-no-target : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    (A : Ty (Δᵉ Γᴸ))
  → ∀ Y → toRenameⁱ (ηᴿᶜ (bindLeftᶜ γ A)) Y
      ≢ toRenameⁱ (ηᴸᶜ (bindLeftᶜ γ A)) Fin.zero
bindLeft-fresh-no-target A Y ()


liftBoth-fresh-occupied : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    (v : VarImp)
  → Σ[ Y ∈ TyVar (Nat.suc (Δᵉ Γᴿ)) ]
      toRenameⁱ (ηᴿᶜ (liftBothᶜ v γ)) Y ≡ Fin.zero
liftBoth-fresh-occupied v = Fin.zero , refl


bindRight-fresh-occupied : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    (B : Ty (Δᵉ Γᴿ)) (fresh : RightBindFreshᶜ γ B)
  → Σ[ Y ∈ TyVar (Nat.suc (Δᵉ Γᴿ)) ]
      toRenameⁱ (ηᴿᶜ (bindRightᶜ γ B fresh)) Y ≡ Fin.zero
bindRight-fresh-occupied B fresh = Fin.zero , refl


bindBoth-fresh-occupied : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    (represented : A ⊑ᵀ⟨ γ ⟩ B)
  → Σ[ Y ∈ TyVar (Nat.suc (Δᵉ Γᴿ)) ]
      toRenameⁱ (ηᴿᶜ (bindBothᶜ γ represented)) Y ≡ Fin.zero
bindBoth-fresh-occupied represented = Fin.zero , refl
