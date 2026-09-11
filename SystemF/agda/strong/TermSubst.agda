module strong.TermSubst where

-- Strong System F — v3 RENAMING AND SUBSTITUTION.
--
-- Term substitution is ordinary: a SCOPE BOUNDARY ᵇ[M] is TERM-CLOSED, so
-- it is never descended into; a CONVERSION M⟨c⟩ is descended into (its body
-- shares the term context).  §1 gives type-variable renaming of terms
-- (`renᴹ`), §5 gives term-variable renaming (`renⁿ`) and the FRAME-EXACT
-- simultaneous substitution (`substᵐ`, `_[_∶_]ᵐ`), and §6 the typing
-- transports (`⊢rename`, `⊢retag`) and the substitution lemma (`⊢subst`).
--
-- FRAME-EXACT SUBSTITUTION (as in v2).  Crossing a `Λ` shifts an image
-- past the new type binder; a value image is additionally WRAPPED so the
-- new binder is CONCEALED from it — in v3 that wrapper is just a conceal
-- boundary `⟦ conceal (0 ∷ []) ⟧` (no conversion, since v3 keeps scope and
-- conversion separate).  Its frame identity is definitional:
--
--   lockχ (0 ∷ []) (unmasked abst ∷ Δ) ≡ masked abst ∷ Δ

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms

private
  variable
    Δ Δ′ : Ctxᵗ
    ρ : Renameᵗ

------------------------------------------------------------------------
-- 1.  Type-variable renaming of a boundary and of a term
------------------------------------------------------------------------

renBnd : Renameᵗ → Bnd → Bnd
renBnd ρ (intro A)   = intro (renameᵗ ρ A)
renBnd ρ (reveal χ)  = reveal (map ρ χ)
renBnd ρ (conceal χ) = conceal (map ρ χ)

numBindsᵇ-ren : (ρ : Renameᵗ) (b : Bnd) → numBindsᵇ (renBnd ρ b) ≡ numBindsᵇ b
numBindsᵇ-ren ρ (intro A)   = refl
numBindsᵇ-ren ρ (reveal χ)  = refl
numBindsᵇ-ren ρ (conceal χ) = refl

renᴹ : Renameᵗ → Term → Term
renᴹ ρ (` x)          = ` x
renᴹ ρ ($ n)          = $ n
renᴹ ρ (# v)          = # v
renᴹ ρ (M ⊕[ p ] N)   = renᴹ ρ M ⊕[ p ] renᴹ ρ N
renᴹ ρ (ƛ A ∙ N)      = ƛ renameᵗ ρ A ∙ renᴹ ρ N
renᴹ ρ (L · M)        = renᴹ ρ L · renᴹ ρ M
renᴹ ρ (Λ N)          = Λ (renᴹ (extᵗ ρ) N)
renᴹ ρ (L ·[ B , A ]) = renᴹ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renᴹ ρ (M ⟦ b ⟧)      = renᴹ (extN (numBindsᵇ b) ρ) M ⟦ renBnd ρ b ⟧
renᴹ ρ (M ⟨ c ⟩)      = renᴹ ρ M ⟨ renᶜ ρ c ⟩

-- Ordinary de Bruijn weakening (a crossing argument's annotations shift).
wkN : ℕ → Renameᵗ
wkN n X = n + X

wkᴹ : ℕ → Term → Term
wkᴹ n = renᴹ (wkN n)

⇑ᴹ : Term → Term
⇑ᴹ = renᴹ suc

Inj-wkN : (n : ℕ) → Inj (wkN n)
Inj-wkN zero    eq = eq
Inj-wkN (suc n) eq = Inj-wkN n (Inj-suc eq)

------------------------------------------------------------------------
-- 5.  Term-variable renaming and the frame-exact substitution
------------------------------------------------------------------------

extⁿ : (ℕ → ℕ) → (ℕ → ℕ)
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

-- A boundary is TERM-CLOSED (identity here); a conversion descends.
renⁿ : (ℕ → ℕ) → Term → Term
renⁿ ρ (` x)          = ` (ρ x)
renⁿ ρ ($ n)          = $ n
renⁿ ρ (# v)          = # v
renⁿ ρ (M ⊕[ p ] N)   = renⁿ ρ M ⊕[ p ] renⁿ ρ N
renⁿ ρ (ƛ A ∙ N)      = ƛ A ∙ renⁿ (extⁿ ρ) N
renⁿ ρ (L · M)        = renⁿ ρ L · renⁿ ρ M
renⁿ ρ (Λ N)          = Λ (renⁿ ρ N)
renⁿ ρ (L ·[ B , A ]) = renⁿ ρ L ·[ B , A ]
renⁿ ρ (M ⟦ b ⟧)      = M ⟦ b ⟧
renⁿ ρ (M ⟨ c ⟩)      = renⁿ ρ M ⟨ c ⟩

shiftᵐ : Term → Term
shiftᵐ = renⁿ suc

-- The frame-exact image of a substitution: a term variable (`ivar`) or a
-- term-closed value at its type (`ival`).
data Img : Set where
  ivar : ℕ → Img
  ival : Term → Ty → Img

imgTm : Img → Term
imgTm (ivar x)   = ` x
imgTm (ival W A) = W

shiftᴵ : Img → Img
shiftᴵ (ivar x)   = ivar (suc x)
shiftᴵ (ival W A) = ival W A

-- The Λ crossing: the shifted value under a conceal boundary that masks
-- the new binder (v3's dual of a type binder).  No conversion is needed —
-- v3 separates scope from conversion.
crossΛ : Term → Term
crossΛ W = ⇑ᴹ W ⟦ conceal (0 ∷ []) ⟧

⇑ᴵ : Img → Img
⇑ᴵ (ivar x)   = ivar x
⇑ᴵ (ival W A) = ival (crossΛ W) (⇑ᵗ A)

extᴵ : (ℕ → Img) → (ℕ → Img)
extᴵ σ zero    = ivar zero
extᴵ σ (suc x) = shiftᴵ (σ x)

substᵐ : (ℕ → Img) → Term → Term
substᵐ σ (` x)          = imgTm (σ x)
substᵐ σ ($ n)          = $ n
substᵐ σ (# v)          = # v
substᵐ σ (M ⊕[ p ] N)   = substᵐ σ M ⊕[ p ] substᵐ σ N
substᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵐ (extᴵ σ) N
substᵐ σ (L · M)        = substᵐ σ L · substᵐ σ M
substᵐ σ (Λ N)          = Λ (substᵐ (λ x → ⇑ᴵ (σ x)) N)
substᵐ σ (L ·[ B , A ]) = substᵐ σ L ·[ B , A ]
substᵐ σ (M ⟦ b ⟧)      = M ⟦ b ⟧
substᵐ σ (M ⟨ c ⟩)      = substᵐ σ M ⟨ c ⟩

-- Beta's substitution: N[x:=W : A], the ƛ's annotation A carried so the
-- crossed-Λ wrapper's type is available (strong.Reduction, `Beta`).
infix 8 _[_∶_]ᵐ
_[_∶_]ᵐ : Term → Term → Ty → Term
N [ W ∶ A ]ᵐ = substᵐ (λ { zero → ival W A ; (suc x) → ivar x }) N
