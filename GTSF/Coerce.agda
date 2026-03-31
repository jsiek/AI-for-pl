module Coerce where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans)

open import Types
open import Consistency
open import Coercions

coerce :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Label →
  Σ ⊢ A ~ B →
  Σ ⊢ A ⇨ B
coerce l X~X = id
coerce l α~α = id
coerce l ι~ι = id
coerce l ★~★ = id
coerce l (★~G g) = 〔 g `? l 〕
coerce l (G~★ g) = 〔 g ! 〕
coerce l (★~⇒ c d) = 〔 ★⇒★ `? l 〕 ⨟ 〔 coerce l c ↦ coerce l d 〕
coerce l (⇒~★ c d) = 〔 coerce l c ↦ coerce l d 〕 ⨟ 〔 ★⇒★ ! 〕
coerce l (A~α h eq)
    with eq
... | refl = 〔 h ⁻ 〕
coerce l (A~α* h c) = coerce l c ⨟ 〔 h ⁻ 〕
coerce l (α~A h eq)
    with eq
... | refl = 〔 h ⁺ 〕
coerce l (α~A* h c) = 〔 h ⁺ 〕 ⨟ coerce l c
coerce l (↦~↦ c d) = 〔 coerce l c ↦ coerce l d 〕
coerce l (∀~∀ c) = 〔 ∀ᶜ (coerce l c) 〕
coerce l (∀~ c) = 〔 ℐ (coerce l c) 〕
coerce l (~∀ c) = 〔 𝒢 (coerce l c) 〕
