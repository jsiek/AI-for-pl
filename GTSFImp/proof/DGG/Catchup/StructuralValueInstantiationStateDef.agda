module proof.DGG.Catchup.StructuralValueInstantiationStateDef where

-- File Charter:
--   * Defines typed pending frames for structural value instantiation.
--   * Retains name applications, casts, conversions, and type transports.
--   * Applies and transports the spine without semantic recursion.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; trans)

open import Types using (Ty; TyVar; ＇_; `∀; _[_]ᵗ)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import CastTerms using (Term; _⟨_⟩; _⦂∀_[_]; _↑_; _↓_)
open import Reduction using
  (StoreChange; keep; bind; applyTy; applyBody; applyConsistency; applyVar)
open import proof.TypeInTermSubst using (rename-openᵗ)


data InstantiationFrame {Δ} : Ty Δ → Ty Δ → Set where
  type-transport-frame : ∀ {A B}
    → A ≡ B
    → InstantiationFrame A B

  name-type-app-frame : ∀ {A C}
    → (B : Ty (suc Δ))
    → (X : TyVar Δ)
    → A ≡ `∀ B
    → C ≡ B [ ＇ X ]ᵗ
    → InstantiationFrame A C

  cast-frame : ∀ {A B} {μ : Env∼ Δ}
    → μ ⊢ A ∼ B
    → InstantiationFrame A B

  reveal-frame : ∀ {A B}
    → Conv↑ Δ A B
    → InstantiationFrame A B

  conceal-frame : ∀ {A B}
    → Conv↓ Δ A B
    → InstantiationFrame A B


infixr 5 _▻ⁱ_

data InstantiationSpine {Δ} : Ty Δ → Ty Δ → Set where
  []ⁱ : ∀ {A} → InstantiationSpine A A

  _▻ⁱ_ : ∀ {A B C}
    → InstantiationFrame A B
    → InstantiationSpine B C
    → InstantiationSpine A C


applyInstantiationFrame : ∀ {Δ A B}
  → Term Δ
  → InstantiationFrame A B
  → Term Δ
applyInstantiationFrame M (name-type-app-frame B X eqA eqC) =
  M ⦂∀ B [ ＇ X ]
applyInstantiationFrame M (type-transport-frame eq) = M
applyInstantiationFrame M (cast-frame c) = M ⟨ c ⟩
applyInstantiationFrame M (reveal-frame c) = M ↑ c
applyInstantiationFrame M (conceal-frame c) = M ↓ c


applyInstantiationSpine : ∀ {Δ A B}
  → Term Δ
  → InstantiationSpine A B
  → Term Δ
applyInstantiationSpine M []ⁱ = M
applyInstantiationSpine M (frame ▻ⁱ spine) =
  applyInstantiationSpine (applyInstantiationFrame M frame) spine


mapInstantiationFrame : ∀ {Δ Δ′ A B}
  → (χ : StoreChange Δ Δ′)
  → InstantiationFrame A B
  → InstantiationFrame (applyTy χ A) (applyTy χ B)
mapInstantiationFrame χ (type-transport-frame eq) =
  type-transport-frame (cong (applyTy χ) eq)
mapInstantiationFrame keep (name-type-app-frame B X eqA eqC) =
  name-type-app-frame B X eqA eqC
mapInstantiationFrame (bind S) (name-type-app-frame B X eqA eqC) =
  name-type-app-frame (applyBody (bind S) B) (applyVar (bind S) X)
    (trans (cong (applyTy (bind S)) eqA) refl)
    (trans (cong (applyTy (bind S)) eqC)
      (rename-openᵗ _ B (＇ X)))
mapInstantiationFrame keep (cast-frame c) = cast-frame c
mapInstantiationFrame (bind R) (cast-frame c) =
  cast-frame (applyConsistency (bind R) c)
mapInstantiationFrame keep (reveal-frame c) = reveal-frame c
mapInstantiationFrame (bind R) (reveal-frame c) =
  reveal-frame (rename↑ Fin.suc c)
mapInstantiationFrame keep (conceal-frame c) = conceal-frame c
mapInstantiationFrame (bind R) (conceal-frame c) =
  conceal-frame (rename↓ Fin.suc c)

mapInstantiationSpine : ∀ {Δ Δ′ A B}
  → (χ : StoreChange Δ Δ′)
  → InstantiationSpine A B
  → InstantiationSpine (applyTy χ A) (applyTy χ B)
mapInstantiationSpine χ []ⁱ = []ⁱ
mapInstantiationSpine χ (frame ▻ⁱ spine) =
  mapInstantiationFrame χ frame ▻ⁱ mapInstantiationSpine χ spine
