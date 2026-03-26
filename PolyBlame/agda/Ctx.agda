module Ctx where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (cong₂; sym; trans)
open import Data.List using ([]; _∷_; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)

open import PolyBlame
open import TypeSubst using
  ( rename-cong
  ; rename-rename-commute
  ; singleSealEnv-suc-cancel
  )

lookup-map-renameᵗ :
  {Γ : Ctx} {x : Var} {A : Ty} {ρ : Renameᵗ} →
  Γ ∋ x ⦂ A →
  map (renameᵗ ρ) Γ ∋ x ⦂ renameᵗ ρ A
lookup-map-renameᵗ Z = Z
lookup-map-renameᵗ (S h) = S (lookup-map-renameᵗ h)

lookup-map-renameˢ :
  {Γ : Ctx} {x : Var} {A : Ty} {ρ : Renameˢ} →
  Γ ∋ x ⦂ A →
  map (renameˢ ρ) Γ ∋ x ⦂ renameˢ ρ A
lookup-map-renameˢ Z = Z
lookup-map-renameˢ (S h) = S (lookup-map-renameˢ h)

lookup-map-inv :
  {Γ : Ctx} {x : Var} {B : Ty} {f : Ty → Ty} →
  map f Γ ∋ x ⦂ B →
  Σ Ty (λ A → (Γ ∋ x ⦂ A) × (B ≡ f A))
lookup-map-inv {Γ = A ∷ Γ} {x = zero} Z = A , (Z , refl)
lookup-map-inv {Γ = A ∷ Γ} {x = suc x} (S h) with lookup-map-inv h
... | A' , (hA' , eq) = A' , (S hA' , eq)

RenameWf : Ctx → Ctx → Rename → Set
RenameWf Γ Γ' ρ = ∀ {x A} → Γ ∋ x ⦂ A → Γ' ∋ ρ x ⦂ A

RenameWf-ext :
  {Γ Γ' : Ctx} {B : Ty} {ρ : Rename} →
  RenameWf Γ Γ' ρ →
  RenameWf (B ∷ Γ) (B ∷ Γ') (ext ρ)
RenameWf-ext hρ Z = Z
RenameWf-ext hρ (S h) = S (hρ h)

map-renameᵗ-⤊ : (ρ : Renameᵗ) (Γ : Ctx) →
  map (renameᵗ (extᵗ ρ)) (⤊ Γ) ≡ ⤊ (map (renameᵗ ρ) Γ)
map-renameᵗ-⤊ ρ [] = refl
map-renameᵗ-⤊ ρ (A ∷ Γ) =
  cong₂ _∷_
    (Eq.trans
      (rename-rename-commute suc (extᵗ ρ) A)
      (Eq.trans
        (rename-cong (λ i → refl) A)
        (Eq.sym (rename-rename-commute ρ suc A))))
    (map-renameᵗ-⤊ ρ Γ)

map-singleSealEnv-suc-cancel :
  (α : Seal) (Γ : Ctx) →
  map (renameˢ (singleSealEnv α)) (⤊ˢ Γ) ≡ Γ
map-singleSealEnv-suc-cancel α [] = refl
map-singleSealEnv-suc-cancel α (A ∷ Γ) =
  cong₂ _∷_
    (singleSealEnv-suc-cancel α A)
    (map-singleSealEnv-suc-cancel α Γ)
