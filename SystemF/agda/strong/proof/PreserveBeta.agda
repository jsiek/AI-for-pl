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
  (Wk; wk-base; Hidden; hid[]; hid-∷; wk-⊢)
open import strong.proof.TermSubstitution using
  (typePrefix; liftInsert; module WithCross)

------------------------------------------------------------------------
-- Inserting one source NAME (and no anchor)
------------------------------------------------------------------------

-- Revealing an anchor does not move it: the source variable that appears
-- names the SAME anchor index, and every older one keeps its own.  That is
-- the whole content of `crossΛ`'s `id`.
insName-n : ∀ d {Δ Y β b}
  → typePrefix d (anch concealed b ∷ Δ) ∋n Y := β
  → typePrefix d (anch revealed b ∷ Δ) ∋n liftInsert d Y := β
insName-n zero (n-concealed t) = n-revealed t
insName-n (suc d) n-here = n-here
insName-n (suc d) (n-revealed t) = n-revealed (insName-n d t)

insName-a : ∀ d {Δ β b}
  → typePrefix d (anch concealed b ∷ Δ) ∋a β
  → typePrefix d (anch revealed b ∷ Δ) ∋a β
insName-a zero a-here = a-here
insName-a zero (a-there t) = a-there t
insName-a (suc d) a-here = a-here
insName-a (suc d) (a-there t) = a-there (insName-a d t)

------------------------------------------------------------------------
-- The boundary's `id` compares A with ⇑ᵗ A
------------------------------------------------------------------------

crossSame : ∀ d {Δ A k b}
  → typePrefix d (anch concealed b ∷ Δ) ⊢ᵗ A
  → SameTy k (typePrefix d (anch concealed b ∷ Δ)) A
             (typePrefix d (anch revealed b ∷ Δ)) (renameᵗ (liftInsert d) A)
crossSame d (wf-var x) with name-of-tv x
crossSame d (wf-var x) | β , n =
  same-free n (insName-n d n)
    (same-anchor (named-anchor n) (insName-a d (named-anchor n)) refl)
crossSame d wf-ℕ = same-ℕ
crossSame d wf-𝔹 = same-𝔹
crossSame d (wf-⇒ a b) = same-⇒ (crossSame d a) (crossSame d b)
crossSame d (wf-∀ a) = same-∀ (crossSame (suc d) a)

------------------------------------------------------------------------
-- Crossing a type abstraction
------------------------------------------------------------------------

cross-typing : ∀ {Δ V A}
  → Δ ok
  → Δ ⊢ᵗ A
  → Δ ∣ [] ⊢ V ⦂ A
  → (anch revealed abstA ∷ Δ) ∣ [] ⊢ crossΛ V A ⦂ ⇑ᵗ A
cross-typing {Δ = Δ} ctx-ok wfA typing =
  ⊢ν store[] (scope∷ con-here scope[]) nf-id
     (wk-⊢ one typing)
     (conv-id (crossSame zero (abst-weaken-wf wfA)) (sb-∷ sb-refl))
  where
  -- One fresh abstract anchor at the base: `shiftAnchor 1` is `suc`, the
  -- renaming `crossΛ` applies.
  one : Wk (anch concealed abstA ∷ []) zero Δ (anch concealed abstA ∷ Δ)
  one = wk-base (hid-∷ hid[])

open WithCross cross-typing public using (subst-typing; preserve-Beta)
