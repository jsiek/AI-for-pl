module strong.TermSubst where

-- Strong System F v8 — term renaming and substitution.
--
-- Boundary bodies are term-closed, so term-variable operations do not
-- descend into them; ν bodies are open, so they do.  Bound-ADDRESS
-- operations descend everywhere: `Λ` and `ν` bind one address each, a
-- boundary binds none (the v7 store-block arithmetic is gone).  Global
-- levels never shift.
--
-- Substitution wraps the image at each `Λ` crossing — the COLOR WRAP:
-- the value crosses into the name's scope behind an identity conceal of
-- the Λ's own bound address, so its nodes' color does not gain the
-- name.  Crossing the Λ's address binder shifts the image's bound
-- addresses; the wrap's interior excludes the crossing assignment, so
-- the image's type names do not shift, and the boundary's exterior
-- type is the one-name shift `⇑ᵗ A`.

open import Data.Nat using (ℕ; zero; suc)

open import strong.Types using (Ty; ⇑ᵗ)
open import strong.RepresentationTypes
open import strong.Conversion
open import strong.Terms

idᵗ-ren : ℕ → ℕ
idᵗ-ren X = X

------------------------------------------------------------------------
-- Bound-address renaming and substitution over terms
------------------------------------------------------------------------

renAddrᴹ : Renameᵇ → Term → Term
renAddrᴹ ρ (` x)       = ` x
renAddrᴹ ρ ($ n)       = $ n
renAddrᴹ ρ (# b)       = # b
renAddrᴹ ρ (M ⊕[ p ] N) = renAddrᴹ ρ M ⊕[ p ] renAddrᴹ ρ N
renAddrᴹ ρ (ƛ A ∙ N)   = ƛ A ∙ renAddrᴹ ρ N
renAddrᴹ ρ (L · M)     = renAddrᴹ ρ L · renAddrᴹ ρ M
renAddrᴹ ρ (Λ V)       = Λ (renAddrᴹ ρ V)
renAddrᴹ ρ (L • B [ A ]) = renAddrᴹ ρ L • B [ A ]
renAddrᴹ ρ (ν R ∙ M)   = ν renameᴿ ρ R ∙ renAddrᴹ ρ M
renAddrᴹ ρ (M ⟨ c ⟩)   = renAddrᴹ ρ M ⟨ renConv idᵗ-ren ρ c ⟩

-- The BASE renaming of a term.  `Λ` and `ν` are the base's binders, so
-- this is the family that extends under them — and, crucially, it is
-- NOT extended by a conversion's crossings, so a boundary is renamed
-- componentwise and its pops are untouched.
renBseᴹ : Renameᵇ → Term → Term
renBseᴹ ρ (` x)       = ` x
renBseᴹ ρ ($ n)       = $ n
renBseᴹ ρ (# b)       = # b
renBseᴹ ρ (M ⊕[ p ] N) = renBseᴹ ρ M ⊕[ p ] renBseᴹ ρ N
renBseᴹ ρ (ƛ A ∙ N)   = ƛ A ∙ renBseᴹ ρ N
renBseᴹ ρ (L · M)     = renBseᴹ ρ L · renBseᴹ ρ M
renBseᴹ ρ (Λ V)       = Λ (renBseᴹ (extᵇ ρ) V)
renBseᴹ ρ (L • B [ A ]) = renBseᴹ ρ L • B [ A ]
renBseᴹ ρ (ν R ∙ M)   = ν renameᴿᵉ ρ R ∙ renBseᴹ (extᵇ ρ) M
renBseᴹ ρ (M ⟨ c ⟩)   = renBseᴹ ρ M ⟨ renConvᵉ ρ c ⟩

substAddrᴹ : SubstAddr → Term → Term
substAddrᴹ σ (` x)       = ` x
substAddrᴹ σ ($ n)       = $ n
substAddrᴹ σ (# b)       = # b
substAddrᴹ σ (M ⊕[ p ] N) = substAddrᴹ σ M ⊕[ p ] substAddrᴹ σ N
substAddrᴹ σ (ƛ A ∙ N)   = ƛ A ∙ substAddrᴹ σ N
substAddrᴹ σ (L · M)     = substAddrᴹ σ L · substAddrᴹ σ M
substAddrᴹ σ (Λ V)       = Λ (substAddrᴹ (extsᵃᵉ σ) V)
substAddrᴹ σ (L • B [ A ]) = substAddrᴹ σ L • B [ A ]
substAddrᴹ σ (ν R ∙ M)   = ν substᴿᵉ σ R ∙ substAddrᴹ (extsᵃᵉ σ) M
substAddrᴹ σ (M ⟨ c ⟩)   = substAddrᴹ σ M ⟨ substAddrConv σ c ⟩

-- Discharge the innermost address binder to the address β.
_[_]ᵃᴹ : Term → Addr → Term
M [ β ]ᵃᴹ = substAddrᴹ (instᵉ₀ β) M

------------------------------------------------------------------------
-- Term-variable renaming
------------------------------------------------------------------------

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
renⁿ ρ (Λ V)       = Λ (renⁿ ρ V)
renⁿ ρ (L • B [ A ]) = renⁿ ρ L • B [ A ]
renⁿ ρ (ν R ∙ M)   = ν R ∙ renⁿ ρ M
renⁿ ρ (M ⟨ c ⟩)   = M ⟨ c ⟩

shiftⁿ : Term → Term
shiftⁿ = renⁿ suc

------------------------------------------------------------------------
-- Term-variable substitution, with the color wrap at Λ
------------------------------------------------------------------------

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

-- The color wrap: v8's crossΛ.  The image's bound addresses cross the
-- Λ's address binder; its type names do not (the wrap's interior sits
-- below the crossing assignment), and the boundary's exterior type is
-- the crossing's one-name shift.
crossΛ : Term → Ty → Term
crossΛ V A = (renBseᴹ suc V) ⟨ hide zero (bse zero) ∷ᶜ id (⇑ᵗ A) ⟩

underΛ : Img → Img
underΛ (ivar x)   = ivar x
underΛ (ival V A) = ival (crossΛ V A) (⇑ᵗ A)

-- Crossing a ν binder shifts the image's bound addresses only.
underν : Img → Img
underν (ivar x)   = ivar x
underν (ival V A) = ival (renBseᴹ suc V) A

substᵐ : (ℕ → Img) → Term → Term
substᵐ σ (` x)       = imgTm (σ x)
substᵐ σ ($ n)       = $ n
substᵐ σ (# b)       = # b
substᵐ σ (M ⊕[ p ] N) = substᵐ σ M ⊕[ p ] substᵐ σ N
substᵐ σ (ƛ A ∙ N)   = ƛ A ∙ substᵐ (extImg σ) N
substᵐ σ (L · M)     = substᵐ σ L · substᵐ σ M
substᵐ σ (Λ V)       = Λ (substᵐ (λ x → underΛ (σ x)) V)
substᵐ σ (L • B [ A ]) = substᵐ σ L • B [ A ]
substᵐ σ (ν R ∙ M)   = ν R ∙ substᵐ (λ x → underν (σ x)) M
substᵐ σ (M ⟨ c ⟩)   = M ⟨ c ⟩

infix 8 _[_∶_]ᵐ
singleImgEnv : Term → Ty → ℕ → Img
singleImgEnv V A zero    = ival V A
singleImgEnv V A (suc x) = ivar x

_[_∶_]ᵐ : Term → Term → Ty → Term
N [ V ∶ A ]ᵐ = substᵐ (singleImgEnv V A) N
