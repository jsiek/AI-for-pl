module strong-rep-store.TermSubst where

-- File Charter:
--   * RENAMING AND SUBSTITUTION ON TERMS — THE PUBLIC HALF.  §1 the
--     PAIRED type-level renaming `TyRename = ren² ordinary represent`
--     with `idᵗ`, `renᶠ²`, `renᴮ²` and `underΛ-ren`.  §2 `renᴹ²`, the
--     REPRESENTATION-ONLY traversal `renᴹᴿ`, and the sibling shifts
--     `↑ᴹ[_]`/`↑ᴮ[_]`.  §5 substitution — `Img`, `imgTm`, `shiftᴵ`,
--     `crossΛᴹ`, `⇑ᴵ`, `extᴵ`, `substᵐ`, `betaEnv`, `_[_∶_]ᵐ`.
--   * ONLY WHAT A PUBLIC FILE NEEDS IS HERE; every lemma and every
--     private definition is strong-rep-store.proof.TermSubst, which
--     KEEPS the section numbers its material had here.  Do not
--     renumber either file.  `extN` (strong-rep-store.Ctx §8) and
--     `renᶠᴿ`/`renᴮᴿ` (strong-rep-store.Boundary §2/§3) are one layer
--     DOWN, beside the syntax they act on.
--   * TWO LAWS.  (1) Boundaries are TERM-CLOSED, so `substᵐ` does NOT
--     descend into `_⟪_,_⟫`.  (2) Beta is FRAME-EXACT: a value image
--     crossing a `Λ` is wrapped in that binder's DUAL (`crossΛᴹ`).
-- Commentary: Commentary.md § TermSubst.agda
--
-- Ordinary type variables and representation variables have distinct de
-- Bruijn universes, so a type renaming carries two maps: the ordinary
-- one renames annotations, type arguments, conversion names and change
-- positions; the representation one renames payloads and the
-- representation-variable occurrence carried by every change.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Boundary
open import strong-rep-store.Terms

------------------------------------------------------------------------
-- 1. Paired type-level renaming
------------------------------------------------------------------------

record TyRename : Set where
  constructor ren²
  field
    ordinary : Renameᵗ
    represent : Renameᵗ
open TyRename public

idᵗ : Renameᵗ
idᵗ X = X

underΛ-ren : TyRename → TyRename
underΛ-ren (ren² ρᵗ ρʳ) = ren² (extᵗ ρᵗ) (extᵗ ρʳ)

renᶠ² : Renameᵗ → Renameᵗ → Change → Change
renᶠ² ρᵗ ρʳ (unbind X α)   = unbind (ρᵗ X) (ρʳ α)
renᶠ² ρᵗ ρʳ (bind X α) = bind (ρᵗ X) (ρʳ α)

renᴮ² : TyRename → Boundary → Boundary
renᴮ² (ren² ρᵗ ρʳ) Θ = map (renᶠ² ρᵗ ρʳ) Θ

------------------------------------------------------------------------
-- 2. Renaming terms
------------------------------------------------------------------------

renᴹ² : TyRename → Term → Term
renᴹ² ρ (` x)          = ` x
renᴹ² ρ ($ n)          = $ n
renᴹ² ρ `true           = `true
renᴹ² ρ `false          = `false
renᴹ² ρ (ƛ A ∙ N)      = ƛ renameᵗ (ordinary ρ) A ∙ renᴹ² ρ N
renᴹ² ρ (L · M)        = renᴹ² ρ L · renᴹ² ρ M
renᴹ² ρ (Λ N)          = Λ (renᴹ² (underΛ-ren ρ) N)
renᴹ² ρ (L ·[ B , A ]) =
  renᴹ² ρ L ·[ renameᵗ (extᵗ (ordinary ρ)) B
             , renameᵗ (ordinary ρ) A ]
renᴹ² ρ (M ⟪ Θ , c ⟫) =
  renᴹ² ρ M ⟪ renᴮ² ρ Θ , renᶜ (ordinary ρ) c ⟫

renᴹᴿ : Renameᵗ → Term → Term
renᴹᴿ ρ (` x)          = ` x
renᴹᴿ ρ ($ n)          = $ n
renᴹᴿ ρ `true           = `true
renᴹᴿ ρ `false          = `false
renᴹᴿ ρ (ƛ A ∙ N)      = ƛ A ∙ renᴹᴿ ρ N
renᴹᴿ ρ (L · M)        = renᴹᴿ ρ L · renᴹᴿ ρ M
renᴹᴿ ρ (Λ N)          = Λ (renᴹᴿ (extᵗ ρ) N)
renᴹᴿ ρ (L ·[ B , A ]) = renᴹᴿ ρ L ·[ B , A ]
renᴹᴿ ρ (M ⟪ Θ , c ⟫) = renᴹᴿ ρ M ⟪ renᴮᴿ ρ Θ , c ⟫

-- THE SIBLING SHIFT (experiment 2): `renᴹᴿ suc` when the step
-- allocated a cell, the identity when it did not.
↑ᴹ[_] : Alloc → Term → Term
↑ᴹ[ none  ] M = M
↑ᴹ[ new R ] M = renᴹᴿ suc M

↑ᴮ[_] : Alloc → Boundary → Boundary
↑ᴮ[ none  ] Θ = Θ
↑ᴮ[ new R ] Θ = renᴮᴿ suc Θ

------------------------------------------------------------------------
-- 5. Term substitution
------------------------------------------------------------------------

data Img : Set where
  ivar : Var → Img
  ival : Term → Ty → Img

imgTm : Img → Term
imgTm (ivar x)   = ` x
imgTm (ival W A) = W

shiftᴵ : Img → Img
shiftᴵ (ivar x)   = ivar (suc x)
shiftᴵ (ival W A) = ival W A

-- A value crossing `Λ` is weakened only in the free representation
-- universe and wrapped in the binder's dual.
-- Commentary.md § TermSubst.agda / §5 — crossΛᴹ, ⇑ᴵ
crossΛᴹ : Term → Ty → Term
crossΛᴹ W A =
  renᴹ² (ren² idᵗ suc) W
    ⟪ (unbind 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫

-- Variables cross a type binder unchanged. Closed value images acquire the
-- frame-exact wrapper above, and their ordinary type spelling is weakened.
⇑ᴵ : Img → Img
⇑ᴵ (ivar x)   = ivar x
⇑ᴵ (ival W A) = ival (crossΛᴹ W A) (⇑ᵗ A)

extᴵ : (Var → Img) → Var → Img
extᴵ σ zero    = ivar zero
extᴵ σ (suc x) = shiftᴵ (σ x)

substᵐ : (Var → Img) → Term → Term
substᵐ σ (` x)          = imgTm (σ x)
substᵐ σ ($ n)          = $ n
substᵐ σ `true           = `true
substᵐ σ `false          = `false
substᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵐ (extᴵ σ) N
substᵐ σ (L · M)        = substᵐ σ L · substᵐ σ M
substᵐ σ (Λ N)          = Λ (substᵐ (λ x → ⇑ᴵ (σ x)) N)
substᵐ σ (L ·[ B , A ]) = substᵐ σ L ·[ B , A ]
substᵐ σ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

-- The substitution `Beta` performs.  A NAMED function, not a pattern
-- lambda, so that strong-rep-store.Residual can cite the same one.
betaEnv : Term → Ty → Var → Img
betaEnv W A zero    = ival W A
betaEnv W A (suc x) = ivar x

infix 8 _[_∶_]ᵐ
_[_∶_]ᵐ : Term → Term → Ty → Term
N [ W ∶ A ]ᵐ = substᵐ (betaEnv W A) N
