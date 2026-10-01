module TermSubst where

-- File Charter:
--   * RENAMING AND SUBSTITUTION ON TERMS.  §2 the REPRESENTATION-ONLY
--     traversal `renᴹᴿ` and the sibling shifts `↑ᴹ[_]`/`↑ᴮ[_]`; §5
--     substitution — `Img`,
--     `imgTm`, `shiftᴵ`, `crossΛᴹ`, `⇑ᴵ`, `extᴵ`, `substᵐ`, `betaEnv`,
--     `_[_∶_]ᵐ`.
--   * FORKED FROM strong-rep-nu.TermSubst.  νF's general paired
--     renaming `renᴹ²` (with `TyRename`, `renᶠ²`, `renᴮ²`, `underΛ-ren`)
--     is GONE: its only use was `crossΛᴹ` at an IDENTITY ordinary
--     renaming, where it computes the same term as `renᴹᴿ suc`, and an
--     arbitrary ordinary renaming cannot transport a cast's mode
--     environment.  `crossΛᴹ` is now written with `renᴹᴿ suc`.
--   * CASTS.  `renᴹᴿ` and `substᵐ` pass a cast's mode environment and
--     coercion through untouched (a coercion mentions no representation
--     variable and no term variable).
--   * NO WEAKENING BY AN ORDINARY NAME.  No rule moves a term under a
--     new name: `TyBeta`'s `gen` case puts the value under the binder's
--     dual instead (`crossΛᴹ`), so names never change spelling.
--   * TWO LAWS (νF).  (1) Boundaries are TERM-CLOSED, so `substᵐ` does
--     NOT descend into `_⟪_,_⟫`.  (2) Beta is FRAME-EXACT: a value image
--     crossing a `Λ` is wrapped in that binder's DUAL (`crossΛᴹ`).
-- Commentary (νF): SystemF/agda/strong-rep-nu/Commentary.md § TermSubst.agda

open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Nat.Properties using (_≟_; _<?_)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

open import Types
  using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms

idᵗ : Renameᵗ
idᵗ X = X

------------------------------------------------------------------------
-- 2. Renaming the representation universe
------------------------------------------------------------------------

renᴹᴿ : Renameᵗ → Term → Term
renᴹᴿ ρ (` x)          = ` x
renᴹᴿ ρ ($ n)          = $ n
renᴹᴿ ρ `true           = `true
renᴹᴿ ρ `false          = `false
renᴹᴿ ρ (ƛ A ∙ N)      = ƛ A ∙ renᴹᴿ ρ N
renᴹᴿ ρ (L · M)        = renᴹᴿ ρ L · renᴹᴿ ρ M
renᴹᴿ ρ (Λ N)          = Λ (renᴹᴿ (extᵗ ρ) N)
renᴹᴿ ρ (ν A · L ⟨ c ⟩) = ν A · renᴹᴿ ρ L ⟨ c ⟩
renᴹᴿ ρ (M ⟪ Θ , c ⟫) = renᴹᴿ ρ M ⟪ renᴮᴿ ρ Θ , c ⟫
renᴹᴿ ρ (M ⟨ μ ∣ p ⟩)  = renᴹᴿ ρ M ⟨ μ ∣ p ⟩
renᴹᴿ ρ (blame ℓ)      = blame ℓ

-- THE SIBLING SHIFT (νF experiment 2): `renᴹᴿ suc` when the step
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
-- νF Commentary.md § TermSubst.agda / §5 — crossΛᴹ, ⇑ᴵ
crossΛᴹ : Term → Ty → Term
crossΛᴹ W A =
  renᴹᴿ suc W ⟪ (unbind 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫

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
substᵐ σ (ν A · L ⟨ c ⟩) = ν A · substᵐ σ L ⟨ c ⟩
substᵐ σ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫
substᵐ σ (M ⟨ μ ∣ p ⟩)  = substᵐ σ M ⟨ μ ∣ p ⟩
substᵐ σ (blame ℓ)      = blame ℓ

-- The substitution `Beta` performs.  A NAMED function, not a pattern
-- lambda, so that a residual layer can cite the same one.
betaEnv : Term → Ty → Var → Img
betaEnv W A zero    = ival W A
betaEnv W A (suc x) = ivar x

infix 8 _[_∶_]ᵐ
_[_∶_]ᵐ : Term → Term → Ty → Term
N [ W ∶ A ]ᵐ = substᵐ (betaEnv W A) N
