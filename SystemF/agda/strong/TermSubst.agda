module strong.TermSubst where

-- Strong System F v7 — term renaming and substitution.
-- Boundary bodies are term-closed, so term operations do not descend into
-- them.  Anchor renaming does descend and uses the separate anchor universe.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (length; []; _∷_)

open import strong.Types using (Ty; ⇑ᵗ)
open import strong.RepresentationTypes using (Renameᴿ; extᴿ)
open import strong.Conversion using (id; renConv)
open import strong.CtxMorph
open import strong.Terms

idᵗ-ren : ℕ → ℕ
idᵗ-ren X = X

renAnchᴹ : Renameᴿ → Term → Term
renAnchᴹ ρ (` x)       = ` x
renAnchᴹ ρ ($ n)       = $ n
renAnchᴹ ρ (# b)       = # b
renAnchᴹ ρ (M ⊕[ p ] N) = renAnchᴹ ρ M ⊕[ p ] renAnchᴹ ρ N
renAnchᴹ ρ (ƛ A ∙ N)   = ƛ A ∙ renAnchᴹ ρ N
renAnchᴹ ρ (L · M)     = renAnchᴹ ρ L · renAnchᴹ ρ M
renAnchᴹ ρ (Λ N)       = Λ (renAnchᴹ (extᴿ ρ) N)
renAnchᴹ ρ (L • B [ A ]) = renAnchᴹ ρ L • B [ A ]
renAnchᴹ ρ (ν Θ , χ [ M ∣ c ]) =
  ν renStore ρ Θ , renBoundaryScope ρ Θ χ
    [ renAnchᴹ (extendAnchor (length Θ) ρ) M
    ∣ renConv idᵗ-ren (extendAnchor (length Θ) ρ) c ]

extⁿ : (ℕ → ℕ) → ℕ → ℕ
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renⁿ : (ℕ → ℕ) → Term → Term
renⁿ ρ (` x)       = ` (ρ x)
renⁿ ρ ($ n)       = $ n
renⁿ ρ (# b)       = # b
renⁿ ρ (M ⊕[ p ] N) = renⁿ ρ M ⊕[ p ] renⁿ ρ N
renⁿ ρ (ƛ A ∙ N)   = ƛ A ∙ renⁿ (extⁿ ρ) N
renⁿ ρ (L · M)     = renⁿ ρ L · renⁿ ρ M
renⁿ ρ (Λ N)       = Λ (renⁿ ρ N)
renⁿ ρ (L • B [ A ]) = renⁿ ρ L • B [ A ]
renⁿ ρ (ν Θ , χ [ M ∣ c ]) = ν Θ , χ [ M ∣ c ]

shiftⁿ : Term → Term
shiftⁿ = renⁿ suc

data Img : Set where
  ivar : ℕ → Img
  ival : Term → Ty → Img

imgTm : Img → Term
imgTm (ivar x)   = ` x
imgTm (ival V A) = V

shiftImgⁿ : Img → Img
shiftImgⁿ (ivar x)   = ivar (suc x)
shiftImgⁿ (ival V A) = ival V A

extImg : (ℕ → Img) → ℕ → Img
extImg σ zero    = ivar zero
extImg σ (suc x) = shiftImgⁿ (σ x)

crossΛ : Term → Ty → Term
crossΛ V A =
  ν [] , conceal zero ∷ []
    [ renAnchᴹ suc V ∣ id (⇑ᵗ A) ]

underΛ : Img → Img
underΛ (ivar x)   = ivar x
underΛ (ival V A) = ival (crossΛ V A) (⇑ᵗ A)

substᵐ : (ℕ → Img) → Term → Term
substᵐ σ (` x)       = imgTm (σ x)
substᵐ σ ($ n)       = $ n
substᵐ σ (# b)       = # b
substᵐ σ (M ⊕[ p ] N) = substᵐ σ M ⊕[ p ] substᵐ σ N
substᵐ σ (ƛ A ∙ N)   = ƛ A ∙ substᵐ (extImg σ) N
substᵐ σ (L · M)     = substᵐ σ L · substᵐ σ M
substᵐ σ (Λ N)       = Λ (substᵐ (λ x → underΛ (σ x)) N)
substᵐ σ (L • B [ A ]) = substᵐ σ L • B [ A ]
substᵐ σ (ν Θ , χ [ M ∣ c ]) = ν Θ , χ [ M ∣ c ]

infix 8 _[_∶_]ᵐ
singleImgEnv : Term → Ty → ℕ → Img
singleImgEnv V A zero    = ival V A
singleImgEnv V A (suc x) = ivar x

_[_∶_]ᵐ : Term → Term → Ty → Term
N [ V ∶ A ]ᵐ = substᵐ (singleImgEnv V A) N
