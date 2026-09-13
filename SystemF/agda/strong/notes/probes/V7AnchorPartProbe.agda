module strong.notes.probes.V7AnchorPartProbe where

-- PROBE (2026-09-13): is `anchorCount Δ₁ ≡ anchorCount Δ₂` the same as
-- saying the ANCHOR PART of the context is unchanged?  No — it is its
-- shadow.  The anchor part is the subsequence of `abst`/`bind` entries,
-- WITH their representations, in order:

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.CtxMorph

anchorsOf : Ctxᵗ → List AnchorBinding
anchorsOf []           = []
anchorsOf (abst ∷ Δ)   = abstA ∷ anchorsOf Δ
anchorsOf (bind R ∷ Δ) = bindA R ∷ anchorsOf Δ
anchorsOf (name α ∷ Δ) = anchorsOf Δ

-- The count is exactly the length of the anchor part …
anchors-count : ∀ Δ → length (anchorsOf Δ) ≡ anchorCount Δ
anchors-count [] = refl
anchors-count (abst ∷ Δ) = cong suc (anchors-count Δ)
anchors-count (bind R ∷ Δ) = cong suc (anchors-count Δ)
anchors-count (name α ∷ Δ) = anchors-count Δ

-- … and equal counts do NOT determine the anchor part: these two agree on
-- the count and disagree on the part.
counted-same : anchorCount (abst ∷ []) ≡ anchorCount (bind `ℕᴿ ∷ [])
counted-same = refl

parts-differ : anchorsOf (abst ∷ []) ≡ (abstA ∷ [])
parts-differ = refl

parts-differ′ : anchorsOf (bind `ℕᴿ ∷ []) ≡ (bindA `ℕᴿ ∷ [])
parts-differ′ = refl

------------------------------------------------------------------------
-- The STRONG statement holds of everything a boundary does
------------------------------------------------------------------------

-- A scope change only ADDS and REMOVES `name` entries.  It never touches
-- an anchor — so the anchor part really is invariant along `χ`, and the
-- interior and the exterior of a boundary really do bind the same anchors.

pop-anchors : ∀ {Δ Δ′ α} → Δ ▷ α ↘ Δ′ → anchorsOf Δ ≡ anchorsOf Δ′
pop-anchors pop-here = refl
pop-anchors (pop-abst p) = cong (abstA ∷_) (pop-anchors p)
pop-anchors (pop-bind {R = R} p) = cong (bindA R ∷_) (pop-anchors p)

change-anchors : ∀ {Δ Δ′ δ} → Δ ⊢δ δ ⇒ Δ′ → anchorsOf Δ ≡ anchorsOf Δ′
change-anchors (step-reveal a u) = refl
change-anchors (step-conceal p) = pop-anchors p

scope-anchors : ∀ {Δ Δ′ χ} → Δ ⊢χ χ ⇒ Δ′ → anchorsOf Δ ≡ anchorsOf Δ′
scope-anchors scope[] = refl
scope-anchors (scope∷ d s) = trans (change-anchors d) (scope-anchors s)
