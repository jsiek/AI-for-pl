module strong.notes.probes.V7ConvIntermediateProbe where

-- PROBE (2026-09-13), now a REGRESSION RECORD.
--
-- Before the seam condition, `conv-cons`'s intermediate context was tied to
-- nothing, and `conv-unseal`/`conv-seal` asked the far side only to READ
-- the representation.  A GROUND representation reads in every context, so
-- the seam could be `∅` between two ends carrying anchors.  Both
-- derivations below type-checked; under
--
--     anchorCount Δ₁ ≡ anchorCount Δ₂
--
-- on `conv-id`, `conv-seal` and `conv-unseal` (strong.Conversion), both are
-- REJECTED.  They are kept here, commented, as the record of what the
-- premise buys.  See notes/DECISIONS.md (2026-09-13).

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion

-- α:=ℕ with a source name X for it, and the empty context.
Δ-one : Ctxᵗ
Δ-one = name zero ∷ bind `ℕᴿ ∷ []

Δ-none : Ctxᵗ
Δ-none = []

-- The two disagree on the anchor count, which is what the premise forbids.
counts-differ : anchorCount Δ-one ≡ suc (anchorCount Δ-none)
counts-differ = refl

------------------------------------------------------------------------
-- (1) REJECTED: a normal conversion whose seam is the empty context
------------------------------------------------------------------------

-- `+X ∷ id(ℕ)` is not exotic — it is `+X(X)` with `repr(X) = ℕ`, the right
-- component of §6's own boundary conversion.  Only the SEAM was degenerate.
--
--   head-out : Δ-one ⊢̂ unseal zero ∶ ` zero ⇝ `ℕ ⊣ Δ-none
--   head-out = conv-unseal n-here (r-over-name r-here) read-ℕ
--
--   tail-in : Δ-none ⊢ id `ℕ ∶ `ℕ ⇝ `ℕ ⊣ Δ-one
--   tail-in = conv-id same-ℕ
--
--   seam-is-empty : Δ-one ⊢ unseal zero ∷ᶜ id `ℕ ∶ ` zero ⇝ `ℕ ⊣ Δ-one
--   seam-is-empty = conv-cons head-out tail-in
--
-- `conv-unseal` now also demands `anchorCount Δ-one ≡ anchorCount Δ-none`,
-- i.e. `1 ≡ 0`.

-- The conversion itself is still a normal form; it is the TYPING that is
-- gone, not the syntax.
seam-normal : NF (unseal zero ∷ᶜ id `ℕ)
seam-normal = nf-cons nf-unseal nf-id irr-id

------------------------------------------------------------------------
-- (2) REJECTED: what the loose seam ALLOWED
------------------------------------------------------------------------

-- `SameTy` matches free variables by anchor LEVEL, counted from the bottom
-- of the context.  Two contexts with different anchor counts assign the
-- same level to different anchors, and `id` then identifies them.  Under
-- one structural `∀`, Δ-one's ambient X and Δ-none's freshly bound Y both
-- sit at anchor level 0 — so this was derivable:
--
--   outer-X : (name zero ∷ abst ∷ Δ-one) ∋n 1 := 1
--   outer-X = n-over-name (n-over-abst n-here)
--
--   bound-Y : (name zero ∷ abst ∷ Δ-none) ∋n 0 := 0
--   bound-Y = n-here
--
--   X-is-Y : SameAnchor (name zero ∷ abst ∷ Δ-one) 1
--                       (name zero ∷ abst ∷ Δ-none) 0
--   X-is-Y = same-anchor (a-over-name (a-over-abst (a-over-name a-here-bind)))
--                        (a-over-name a-here-abst)
--                        refl
--
--   equates-X-with-bound-Y :
--     Δ-one ⊢ id (`∀ (` zero)) ∶ `∀ (` 1) ⇝ `∀ (` zero) ⊣ Δ-none
--   equates-X-with-bound-Y = conv-id (same-∀ (same-free outer-X bound-Y X-is-Y))
--
-- That reads `id(∀Y.Y) : (∀Y.X) ⇒ (∀Y.Y)`: it equates an AMBIENT type
-- variable with a ∀-BOUND one.  `conv-id` now also demands `1 ≡ 0`.
--
-- The level coincidence itself is still real, and is the reason the
-- premise is needed rather than merely tidy:
level-coincidence :
    anchorLevel (name zero ∷ abst ∷ Δ-one) 1
  ≡ anchorLevel (name zero ∷ abst ∷ Δ-none) 0
level-coincidence = refl
