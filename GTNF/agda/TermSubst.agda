module TermSubst where

-- File Charter:
--   * RENAMING AND SUBSTITUTION ON TERMS.  §2 the REPRESENTATION-ONLY
--     traversal `renᴹᴿ` and the sibling shifts `↑ᴹ[_]`/`↑ᴮ[_]`; §3
--     (GTNF) the weakening `⇑ᴹ` by one fresh ORDINARY name, which the
--     `gen` case of `TyBeta`'s `InstX` needs; §5 substitution — `Img`,
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
--     variable and no term variable); `⇑ᴹ` inserts the fresh name's
--     mode `X∼X` into it (GTSFImp `renameEnv∼` at a `skip`).
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
-- 3. (GTNF) Weakening by one fresh ordinary name
------------------------------------------------------------------------

-- `⇑ᴹ k ρʳ M` reads M in a context with ONE MORE ordinary name, at
-- position k, and with its representation variables renamed by ρʳ.
-- `TyBeta`'s `gen` case uses `⇑ᴹ 0 suc`: the value under `genᵖ` moves
-- under the new boundary's name 0 for the newly allocated cell
-- (design.md §6.2, `inst_X(W ⟨gen X. p⟩) = W ⟨p⟩` with X ∉ W;
-- GTSFImp `β-gen`'s `⇑ᵗᵐ V`).  At k = 0 this is νF's `liftᴮ` lifted to
-- terms.  Under a `Λ` the position grows by one, and under a boundary it
-- is TRACKED through the scope's changes, separately for the interior
-- reading (`kᵢ`, still a position) and for the conversion reading (a
-- renaming `ρᶜ`, since that reading skips unbinds and so can disagree
-- with the interior about which side of the fresh name a bind lands).
-- A `bind` of a representation variable an earlier change mentions is a
-- live re-bind in the conversion reading, which inserts nothing.
mentions : RVar → Boundary → Bool
mentions α []               = false
mentions α (bind X β ∷ Θ) with α ≟ β
mentions α (bind X β ∷ Θ) | yes _ = true
mentions α (bind X β ∷ Θ) | no  _ = mentions α Θ
mentions α (unbind X β ∷ Θ) with α ≟ β
mentions α (unbind X β ∷ Θ) | yes _ = true
mentions α (unbind X β ∷ Θ) | no  _ = mentions α Θ

-- the conversion reading's correspondence after inserting the original
-- position X, which lands at X′ in the weakened list
insertRen : ℕ → ℕ → Renameᵗ → Renameᵗ
insertRen X X′ ρ i with i ≟ X
insertRen X X′ ρ i | yes _ = X′
insertRen X X′ ρ i | no  _ with i <? X
insertRen X X′ ρ i | no  _ | yes _ with ρ i <? X′
insertRen X X′ ρ i | no  _ | yes _ | yes _ = ρ i
insertRen X X′ ρ i | no  _ | yes _ | no  _ = suc (ρ i)
insertRen X X′ ρ i | no  _ | no  _ with ρ (pred i) <? X′
insertRen X X′ ρ i | no  _ | no  _ | yes _ = ρ (pred i)
insertRen X X′ ρ i | no  _ | no  _ | no  _ = suc (ρ (pred i))

-- a change at original position X, with the fresh name at kᵢ in the
-- interior reading: its weakened position (ties land after the fresh
-- name, as in `liftᴮ`)
wkPos : ℕ → ℕ → ℕ
wkPos kᵢ X with X <? kᵢ
wkPos kᵢ X | yes _ = X
wkPos kᵢ X | no  _ = suc X

⇑ᴮ : ℕ → Renameᵗ → Boundary → Boundary × ℕ × Renameᵗ
⇑ᴮ k ρʳ [] = [] , k , extN k suc
⇑ᴮ k ρʳ (unbind X α ∷ Θ) with ⇑ᴮ k ρʳ Θ
⇑ᴮ k ρʳ (unbind X α ∷ Θ) | Θ′ , kᵢ , ρᶜ with X <? kᵢ
⇑ᴮ k ρʳ (unbind X α ∷ Θ) | Θ′ , kᵢ , ρᶜ | yes _ =
  unbind X (ρʳ α) ∷ Θ′ , pred kᵢ , ρᶜ
⇑ᴮ k ρʳ (unbind X α ∷ Θ) | Θ′ , kᵢ , ρᶜ | no  _ =
  unbind (suc X) (ρʳ α) ∷ Θ′ , kᵢ , ρᶜ
⇑ᴮ k ρʳ (bind X α ∷ Θ) with ⇑ᴮ k ρʳ Θ
⇑ᴮ k ρʳ (bind X α ∷ Θ) | Θ′ , kᵢ , ρᶜ with X <? kᵢ | mentions α Θ
⇑ᴮ k ρʳ (bind X α ∷ Θ) | Θ′ , kᵢ , ρᶜ | yes _ | true =
  bind X (ρʳ α) ∷ Θ′ , suc kᵢ , ρᶜ
⇑ᴮ k ρʳ (bind X α ∷ Θ) | Θ′ , kᵢ , ρᶜ | yes _ | false =
  bind X (ρʳ α) ∷ Θ′ , suc kᵢ , insertRen X X ρᶜ
⇑ᴮ k ρʳ (bind X α ∷ Θ) | Θ′ , kᵢ , ρᶜ | no  _ | true =
  bind (suc X) (ρʳ α) ∷ Θ′ , kᵢ , ρᶜ
⇑ᴮ k ρʳ (bind X α ∷ Θ) | Θ′ , kᵢ , ρᶜ | no  _ | false =
  bind (suc X) (ρʳ α) ∷ Θ′ , kᵢ , insertRen X (suc X) ρᶜ

⇑ᴹ : ℕ → Renameᵗ → Term → Term
⇑ᴹ k ρʳ (` x)           = ` x
⇑ᴹ k ρʳ ($ n)           = $ n
⇑ᴹ k ρʳ `true           = `true
⇑ᴹ k ρʳ `false          = `false
⇑ᴹ k ρʳ (ƛ A ∙ N)       = ƛ renameᵗ (extN k suc) A ∙ ⇑ᴹ k ρʳ N
⇑ᴹ k ρʳ (L · M)         = ⇑ᴹ k ρʳ L · ⇑ᴹ k ρʳ M
⇑ᴹ k ρʳ (Λ N)           = Λ (⇑ᴹ (suc k) (extᵗ ρʳ) N)
-- `c` is read under the hypothetical name 0 for the cell `ν` allocates
⇑ᴹ k ρʳ (ν A · L ⟨ c ⟩) =
  ν renameᵗ (extN k suc) A · ⇑ᴹ k ρʳ L ⟨ renᶜ (extN (suc k) suc) c ⟩
⇑ᴹ k ρʳ (M ⟪ Θ , c ⟫) with ⇑ᴮ k ρʳ Θ
⇑ᴹ k ρʳ (M ⟪ Θ , c ⟫) | Θ′ , kᵢ , ρᶜ = ⇑ᴹ kᵢ ρʳ M ⟪ Θ′ , renᶜ ρᶜ c ⟫
⇑ᴹ k ρʳ (M ⟨ μ ∣ p ⟩)   =
  ⇑ᴹ k ρʳ M ⟨ insertAt k X∼X μ ∣ renᵖ (extN k suc) p ⟩
⇑ᴹ k ρʳ (blame ℓ)       = blame ℓ

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
