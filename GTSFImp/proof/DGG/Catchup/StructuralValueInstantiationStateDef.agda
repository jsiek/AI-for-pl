module proof.DGG.Catchup.StructuralValueInstantiationStateDef where

-- File Charter:
--   * Defines typed pending frames for structural value instantiation.
--   * Retains casts, reveals, and conceals in their operational order.
--   * Applies and transports the spine without semantic recursion.

import Data.Fin as Fin
open import Types using (Ty)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import CastTerms using (Term; _⟨_⟩; _↑_; _↓_)
open import Reduction using
  (StoreChange; keep; bind; applyTy; applyConsistency)


data InstantiationFrame {Δ} : Ty Δ → Ty Δ → Set where
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
