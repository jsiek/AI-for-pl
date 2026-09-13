module strong.notes.probes.V7ConvIntermediateProbe where

-- PROBE (2026-09-13): `conv-cons`'s intermediate context is UNCONSTRAINED.
--
-- `conv-cons : Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₂ ⊢ c ∶ B ⇝ C ⊣ Δ₃ → Δ₁ ⊢ h ∷ᶜ c ∶ A ⇝ C ⊣ Δ₃`
-- ties Δ₂ to nothing.  `conv-unseal` only asks the far side to READ the
-- representation, and a GROUND representation reads in EVERY context — so
-- the empty context serves as the seam of a conversion whose two endpoints
-- both have anchors.  Below is such a derivation, in normal form.
--
-- WHY IT MATTERS.  Anchor weakening — `renAnchᴹ ρ`, which `Beta` (crossΛ),
-- `Wrap`, `TyWrap` and `Merge` all perform — renames the anchor INSIDE each
-- `seal`/`unseal` head.  `conv-seal`'s premises `Δ₂ ∋n X := α` and
-- `Δ₂ ∋r α := R` then have to be re-derived at a weakened Δ₂, and one ρ
-- serves the whole conversion, so every context along the chain must admit
-- the SAME insertion.  A seam with fewer anchors than the endpoints admits
-- no such insertion, so the weakening lemma cannot be stated for
-- conversions as currently typed.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion

-- α:=ℕ with a source name X for it.
Δ₁ : Ctxᵗ
Δ₁ = name zero ∷ bind `ℕᴿ ∷ []

-- `unseal α : X ⇒ ℕ`, leaving Δ₁ for the EMPTY context …
head-out : Δ₁ ⊢̂ unseal zero ∶ ` zero ⇝ `ℕ ⊣ []
head-out = conv-unseal n-here (r-over-name r-here) read-ℕ

-- … and the terminator comes straight back to Δ₁.
tail-in : [] ⊢ id `ℕ ∶ `ℕ ⇝ `ℕ ⊣ Δ₁
tail-in = conv-id same-ℕ

seam-is-empty : Δ₁ ⊢ unseal zero ∷ᶜ id `ℕ ∶ ` zero ⇝ `ℕ ⊣ Δ₁
seam-is-empty = conv-cons head-out tail-in

-- And it is a NORMAL FORM, so a boundary may carry it.
seam-normal : NF (unseal zero ∷ᶜ id `ℕ)
seam-normal = nf-cons nf-unseal nf-id irr-id

------------------------------------------------------------------------
-- What the loose seam ALLOWS
------------------------------------------------------------------------

-- The seam above is not merely inconvenient.  A seam may hand the chain on
-- to a context with a DIFFERENT number of anchors, and `SameTy` matches
-- free variables by anchor LEVEL — a number counted from the bottom of the
-- context.  Two contexts with different anchor counts therefore assign the
-- same level to different anchors, and `id` will identify them.
--
-- Here the left context has one anchor (α:=ℕ, named X) and the right has
-- none.  Under one structural `∀`, the LEFT's outer name X and the RIGHT's
-- freshly bound name Y both sit at anchor level 0 — so

--     id(∀Y.Y) : (∀Y.X)  ⇒  (∀Y.Y)

-- is derivable.  It equates the ambient X with the ∀-bound Y.

Δ-one : Ctxᵗ
Δ-one = name zero ∷ bind `ℕᴿ ∷ []       -- α:=ℕ, X:=α

Δ-none : Ctxᵗ
Δ-none = []                              -- ∅

-- Inside one structural `∀`, with a fresh anchor and name pushed on both.
outer-X : (name zero ∷ abst ∷ Δ-one) ∋n 1 := 1
outer-X = n-over-name (n-over-abst n-here)

bound-Y : (name zero ∷ abst ∷ Δ-none) ∋n 0 := 0
bound-Y = n-here

-- Both are at anchor level 0 — of DIFFERENT contexts.
X-is-Y : SameAnchor (name zero ∷ abst ∷ Δ-one) 1
                    (name zero ∷ abst ∷ Δ-none) 0
X-is-Y = same-anchor (a-over-name (a-over-abst (a-over-name a-here-bind)))
                     (a-over-name a-here-abst)
                     refl

equates-X-with-bound-Y :
  Δ-one ⊢ id (`∀ (` zero)) ∶ `∀ (` 1) ⇝ `∀ (` zero) ⊣ Δ-none
equates-X-with-bound-Y = conv-id (same-∀ (same-free outer-X bound-Y X-is-Y))
