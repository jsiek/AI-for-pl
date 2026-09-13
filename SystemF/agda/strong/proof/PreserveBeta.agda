module strong.proof.PreserveBeta where

-- Strong System F v7 — preservation for `Beta`.
--
-- Substitution is ordinary except at a type abstraction: `(Λ N)[x:=V:A]`
-- may not simply push `V` inside, because the `Λ` binds a type variable `V`
-- does not know about.  `crossΛ` sends it across a BOUNDARY instead,
--
--     crossΛ V A  =  ν ∅ , (-X:=α) [ renAnchᴹ suc V | id (⇑ᵗ A) ]
--
-- concealing the freshly bound name.  Typing it needs two things: the value
-- moves under one new ANCHOR (`wk-⊢`, anchor weakening), and the boundary's
-- `id` compares `A` at the interior with `⇑ᵗ A` at the exterior across one
-- new NAME — which is what `crossSame` establishes.

open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.proof.CtxProperties using (name-of-tv; named-anchor; ok-Λ)
open import strong.proof.TypeWf using (abst-weaken-wf)
open import strong.proof.AnchorWeaken using
  (Wk; wk-base; Block; blk[]; blk-abst; wk-⊢)
open import strong.proof.TermSubstitution using
  (typePrefix; liftInsert; module WithCross)

------------------------------------------------------------------------
-- Inserting one source NAME (and no anchor)
------------------------------------------------------------------------

insName-n : ∀ d {Δ Y β}
  → typePrefix d (abst ∷ Δ) ∋n Y := β
  → typePrefix d (name zero ∷ abst ∷ Δ) ∋n liftInsert d Y := β
insName-n zero (n-over-abst t) = n-over-name (n-over-abst t)
insName-n (suc d) n-here = n-here
insName-n (suc d) (n-over-name (n-over-abst t)) =
  n-over-name (n-over-abst (insName-n d t))

insName-a : ∀ d {Δ β}
  → typePrefix d (abst ∷ Δ) ∋a β
  → typePrefix d (name zero ∷ abst ∷ Δ) ∋a β
insName-a zero t = a-over-name t
insName-a (suc d) (a-over-name a-here-abst) = a-over-name a-here-abst
insName-a (suc d) (a-over-name (a-over-abst t)) =
  a-over-name (a-over-abst (insName-a d t))

-- A name is not an anchor, so the two contexts count anchors alike.
insName-count : ∀ d Δ
  → anchorCount (typePrefix d (abst ∷ Δ))
  ≡ anchorCount (typePrefix d (name zero ∷ abst ∷ Δ))
insName-count zero Δ = refl
insName-count (suc d) Δ = cong suc (insName-count d Δ)

------------------------------------------------------------------------
-- The boundary's `id` compares A with ⇑ᵗ A
------------------------------------------------------------------------

crossSame : ∀ d {Δ A k}
  → typePrefix d (abst ∷ Δ) ok
  → typePrefix d (abst ∷ Δ) ⊢ᵗ A
  → SameTy k (typePrefix d (abst ∷ Δ)) A
             (typePrefix d (name zero ∷ abst ∷ Δ)) (renameᵗ (liftInsert d) A)
crossSame d {Δ = Δ} ctx-ok (wf-var x) with name-of-tv x
crossSame d {Δ = Δ} ctx-ok (wf-var x) | β , n =
  same-free n (insName-n d n)
    (same-anchor a (insName-a d a)
      (cong (λ c → c ∸ suc β) (insName-count d Δ)))
  where
  a = named-anchor ctx-ok n
crossSame d ctx-ok wf-ℕ = same-ℕ
crossSame d ctx-ok wf-𝔹 = same-𝔹
crossSame d ctx-ok (wf-⇒ a b) =
  same-⇒ (crossSame d ctx-ok a) (crossSame d ctx-ok b)
crossSame d ctx-ok (wf-∀ a) = same-∀ (crossSame (suc d) (ok-Λ ctx-ok) a)

------------------------------------------------------------------------
-- Crossing a type abstraction
------------------------------------------------------------------------

cross-typing : ∀ {Δ V A}
  → Δ ok
  → Δ ⊢ᵗ A
  → Δ ∣ [] ⊢ V ⦂ A
  → (name zero ∷ abst ∷ Δ) ∣ [] ⊢ crossΛ V A ⦂ ⇑ᵗ A
cross-typing {Δ = Δ} ctx-ok wfA typing =
  ⊢ν store[] (scope∷ (step-conceal pop-here) scope[]) nf-id
     (wk-⊢ one typing)
     (conv-id (crossSame zero (ok-abst ctx-ok) (abst-weaken-wf wfA)) refl)
  where
  -- One fresh abstract anchor, inserted at the base: `shiftAnchor 1` is
  -- `suc`, which is the renaming `crossΛ` applies.
  one : Wk 1 (anchorCount Δ) (shiftAnchor 1) Δ (abst ∷ Δ)
  one = wk-base (blk-abst blk[])

open WithCross cross-typing public using (subst-typing; preserve-Beta)
