module Coerce where

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
coerce l (★~G g) = 〔 g `? l 〕
coerce l (G~★ g) = 〔 g ! 〕
coerce l (★~⇒ c d) = 〔 ★⇒★ `? l 〕 ⨟ 〔 coerce l c ↦ coerce l d 〕
coerce l (⇒~★ c d) = 〔 coerce l c ↦ coerce l d 〕 ⨟ 〔 ★⇒★ ! 〕
coerce l (A~α h) = 〔 h ⁻ 〕
coerce l (α~A h) = 〔 h ⁺ 〕
coerce l (↦~↦ c d) = 〔 coerce l c ↦ coerce l d 〕
coerce l (∀~∀ c) = 〔 ∀ᶜ (coerce l c) 〕
coerce l (∀~ c) = 〔 ℐ (coerce l c) 〕
