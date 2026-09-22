module strong-rep-store.TermSubst where

-- File Charter:
--   * RENAMING AND SUBSTITUTION ON TERMS — THE PUBLIC HALF.  §1 is the
--     PAIRED type-level renaming `TyRename = ren² ordinary represent`
--     with `idᵗ`, `renᶠ²`, the scope-level
--     `renᴮ² ρ Θ = map (renᶠ² …) Θ` (a boundary IS its change list,
--     strong-rep-store.Boundary §3) and `underΛ-ren`.  §2 is `renᴹ²` on
--     terms, the REPRESENTATION-ONLY traversal `renᴹᴿ`, and the sibling
--     shifts `↑ᴹ[_]`/`↑ᴮ[_]`.  §5 is substitution — `Img`, `imgTm`,
--     `shiftᴵ`, `crossΛᴹ`, `⇑ᴵ`, `extᴵ`, `substᵐ`, `betaEnv` and
--     `_[_∶_]ᵐ`, the substitution `Beta` performs.
--   * ONLY WHAT A PUBLIC FILE NEEDS IS HERE (2026-09-22, the AGENTS.md
--     public/private mandate).  Every lemma about these operations, and
--     every definition no top-level module mentions — the derived
--     `renᴹ`/`wkN`/`wkᴹ`/`⇑ᴹ`/`id²`/`renᶠ`, the value-preservation and
--     ordinary-identity families, TERM-VARIABLE renaming
--     `extⁿ`/`renⁿ`/`shiftᵐ` with `⊢renⁿ`/`⊢weakenⁿ`, the `⤊`
--     transports, and the typed images `_∣_⊢ⁱ_⦂_` — is
--     strong-rep-store.proof.TermSubst.  That file KEEPS the section
--     numbers its material had here (§1, §2, §3, §4, §5, §6), and the
--     numbers below are unchanged for the same reason: other modules
--     cite them, so do not renumber either file.
--   * WHAT IS DELIBERATELY ONE LAYER DOWN.  `extN` is
--     strong-rep-store.Ctx §8 and the representation-only
--     `renᶠᴿ`/`renᴮᴿ` are strong-rep-store.Boundary §2/§3, beside the
--     syntax they act on, because the representation-renaming metatheory
--     of strong-rep-store.Boundary §3d is stated over them and cannot
--     import this module.  Reduction is strong-rep-store.Reduction; the
--     typing transport for `renᴹᴿ` and `crossΛᴹ` is
--     strong-rep-store.proof.RepWeaken (`rep-weaken-⊢`, `cross-Λ-⊢`).
--   * TWO LAWS A READER MUST KNOW.  (1) Boundaries are TERM-CLOSED
--     (strong-rep-store.Terms `env`), so `substᵐ` does NOT descend into
--     `_⟪_,_⟫`.  (2) Beta is FRAME-EXACT: a closed value image crossing
--     a `Λ` is wrapped in that binder's DUAL with an identity conversion
--     at the argument's type (`crossΛᴹ`, used by `⇑ᴵ`), which is why
--     `_[_∶_]ᵐ` carries the `ƛ`'s own annotation instead of shifting.
--
-- Ordinary type variables and representation variables have distinct de
-- Bruijn universes. Consequently, syntax-level type renaming carries two
-- maps:
--
--   * the ordinary map renames term annotations, type arguments, conversion
--     names, and the positions carried by `lock` and `unlock`;
--   * the representation map renames boundary scope payloads and the
--     representation-variable occurrence carried by every change.

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

-- `extN` (renaming underneath n binders) and the representation-only
-- `renᶠᴿ`/`renᴮᴿ` live one layer down — `extN` in strong-rep-store.Ctx
-- §8 and the two renamings in strong-rep-store.Boundary §2/§3, beside
-- the syntax they act on — because the representation-renaming
-- metatheory of strong-rep-store.Boundary §3d is stated over them and
-- cannot import this module.

underΛ-ren : TyRename → TyRename
underΛ-ren (ren² ρᵗ ρʳ) = ren² (extᵗ ρᵗ) (extᵗ ρʳ)

renᶠ² : Renameᵗ → Renameᵗ → Change → Change
renᶠ² ρᵗ ρʳ (lock X α)   = lock (ρᵗ X) (ρʳ α)
renᶠ² ρᵗ ρʳ (unlock X α) = unlock (ρᵗ X) (ρʳ α)

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

-- THE SIBLING SHIFT (experiment 2).  When a step allocates a cell, every
-- representation variable of the redex's siblings — terms and boundary
-- scopes alike — moves up by one; when it does not, nothing moves.
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
-- universe and wrapped in the binder's dual. The lock removes the fresh
-- ordinary variable, so the surviving ordinary indices retain their old
-- positions; representation occurrences move past the new abstract binder.
crossΛᴹ : Term → Ty → Term
crossΛᴹ W A =
  renᴹ² (ren² idᵗ suc) W
    ⟪ (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫

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

-- The substitution `Beta` performs: the argument, carrying the ƛ's
-- annotation, for variable zero; every other variable steps down.  It is
-- a named function, not a pattern lambda, so that strong-rep-store.Residual
-- can cite the very same substitution when it follows a position through
-- `Beta`.
betaEnv : Term → Ty → Var → Img
betaEnv W A zero    = ival W A
betaEnv W A (suc x) = ivar x

infix 8 _[_∶_]ᵐ
_[_∶_]ᵐ : Term → Term → Ty → Term
N [ W ∶ A ]ᵐ = substᵐ (betaEnv W A) N
