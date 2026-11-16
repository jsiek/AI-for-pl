module nu-cancel-id.TermSubst where

-- File Charter:
--   * RENAMING AND SUBSTITUTION of νF₁ᶜ terms.  §1 representation
--     renaming `renameʳ`, which moves the cells named by boundaries (for
--     allocation).  §2 parallel renaming of term variables.  §3 parallel
--     substitution, §4 its environments, §5 single substitution as a
--     special case.
--   * Boundary bodies are term-closed, so renaming and substitution of
--     term variables stop at a boundary.
--   * A `Λ` binds no term variable, but a value copied under it is
--     wrapped by `crossΛ`, which hides the `Λ`'s cell, so its holes keep
--     their scope map (the hiding boundary of strong-rep-nu's
--     `crossΛᴹ`).  So an environment maps each term variable to a
--     variable or to a closed value (`Sub`), and `liftΛ` crosses only
--     the values.
--   * Beta's `N [ V ]` is `subst (V • idˢ) N`, and `substᵐ j V`, the
--     substitution of V for variable j under j binders, is
--     `subst (extsⁿ j (V • idˢ))`.  The laws are in
--     nu-cancel-id.proof.TermSubst.

open import Data.Nat using (ℕ; zero; suc)

open import nu-cancel-id.Types
open import nu-cancel-id.Terms

------------------------------------------------------------------------
-- 1. Representation renaming.  Annotations are NAMED types and stay
--    put: allocation adds an unnamed cell, so no name position moves.
------------------------------------------------------------------------

renameʳ : Renameᵗ → Term → Term
renameʳ ρ (` x)               = ` x
renameʳ ρ ($ k)               = $ k
renameʳ ρ (ƛ A ∙ N)           = ƛ A ∙ renameʳ ρ N
renameʳ ρ (L · M)             = renameʳ ρ L · renameʳ ρ M
renameʳ ρ (Λ N)               = Λ renameʳ (extᵗ ρ) N
renameʳ ρ (ν A · L ⟨ c ⟩)     = ν A · renameʳ ρ L ⟨ c ⟩
renameʳ ρ ([ s , α ] M ⟨ c ⟩) = [ s , ρ α ] renameʳ ρ M ⟨ c ⟩

-- a copy that crosses a `Λ` hides the `Λ`'s own cell
crossΛ : Term → Term
crossΛ V = [ ⁻ , zero ] renameʳ suc V ⟨ idᶜ ⟩

------------------------------------------------------------------------
-- 2. Renaming of term variables
------------------------------------------------------------------------

Rename : Set
Rename = ℕ → ℕ

ext : Rename → Rename
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

wk : Rename
wk = suc

rename : Rename → Term → Term
rename ρ (` x)               = ` ρ x
rename ρ ($ k)               = $ k
rename ρ (ƛ A ∙ N)           = ƛ A ∙ rename (ext ρ) N
rename ρ (L · M)             = rename ρ L · rename ρ M
rename ρ (Λ N)               = Λ rename ρ N
rename ρ (ν A · L ⟨ c ⟩)     = ν A · rename ρ L ⟨ c ⟩
rename ρ ([ s , α ] M ⟨ c ⟩) = [ s , α ] M ⟨ c ⟩

------------------------------------------------------------------------
-- 3. Parallel substitution
------------------------------------------------------------------------

-- an environment's entry: a variable, or a closed value
data Sub : Set where
  var : ℕ → Sub
  val : Term → Sub

Subst : Set
Subst = ℕ → Sub

-- the term an entry stands for
⌊_⌋ : Sub → Term
⌊ var y ⌋ = ` y
⌊ val V ⌋ = V

-- an entry under a `ƛ`: a variable shifts, a closed value stays
shiftˢ : Sub → Sub
shiftˢ (var y) = var (suc y)
shiftˢ (val V) = val V

-- an entry under a `Λ`: a variable stays, a closed value crosses
crossˢ : Sub → Sub
crossˢ (var y) = var y
crossˢ (val V) = val (crossΛ V)

exts : Subst → Subst
exts σ zero    = var zero
exts σ (suc x) = shiftˢ (σ x)

liftΛ : Subst → Subst
liftΛ σ x = crossˢ (σ x)

subst : Subst → Term → Term
subst σ (` x)               = ⌊ σ x ⌋
subst σ ($ k)               = $ k
subst σ (ƛ A ∙ N)           = ƛ A ∙ subst (exts σ) N
subst σ (L · M)             = subst σ L · subst σ M
subst σ (Λ N)               = Λ subst (liftΛ σ) N
subst σ (ν A · L ⟨ c ⟩)     = ν A · subst σ L ⟨ c ⟩
subst σ ([ s , α ] M ⟨ c ⟩) = [ s , α ] M ⟨ c ⟩

------------------------------------------------------------------------
-- 4. Environments
------------------------------------------------------------------------

idˢ : Subst
idˢ x = var x

ren : Rename → Subst
ren ρ x = var (ρ x)

infixr 6 _•_
_•_ : Term → Subst → Subst
(V • σ) zero    = val V
(V • σ) (suc x) = σ x

-- composition: a variable entry is looked up in τ, and a closed value
-- is left as it is
_⨟ˢ_ : Sub → Subst → Sub
var y ⨟ˢ τ = τ y
val V ⨟ˢ τ = val V

infixr 5 _⨟_
_⨟_ : Subst → Subst → Subst
(σ ⨟ τ) x = σ x ⨟ˢ τ

extsⁿ : ℕ → Subst → Subst
extsⁿ zero    σ = σ
extsⁿ (suc j) σ = exts (extsⁿ j σ)

------------------------------------------------------------------------
-- 5. Single substitution
------------------------------------------------------------------------

-- V for term variable j, under j binders
substᵐ : ℕ → Term → Term → Term
substᵐ j V = subst (extsⁿ j (V • idˢ))

infix 8 _[_]
_[_] : Term → Term → Term
N [ V ] = subst (V • idˢ) N

-- whether term variable x is the substituted j; if not, its index after
data Hit : Set where
  hit  : Hit
  miss : ℕ → Hit

sucHit : Hit → Hit
sucHit hit      = hit
sucHit (miss y) = miss (suc y)

hitVar : ℕ → ℕ → Hit
hitVar zero    zero    = hit
hitVar zero    (suc j) = miss zero
hitVar (suc x) zero    = miss x
hitVar (suc x) (suc j) = sucHit (hitVar x j)

fromHit : Hit → Term → Term
fromHit hit      V = V
fromHit (miss y) V = ` y
