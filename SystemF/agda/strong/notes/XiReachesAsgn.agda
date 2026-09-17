module strong.notes.XiReachesAsgn where

-- Jeremy: substitution is only used by `Beta`, which requires the
-- argument to be a VALUE — so the colour wraps substitution mints never
-- sit around a redex, and `Wrap` is the UNIQUE minter of a boundary
-- that needs `ξ-⟨⟩`.  That is right (TyBeta, TyWrap and Merge all wrap
-- values too).
--
-- It does not bound the interiors ξ-⟨⟩ reaches, though, because `arr`
-- passes a crossing into BOTH halves:
--
--   arr⁻ (show X α) = just (hide X α ∷ [])
--   arr⁺ (show X α) = just (show X α ∷ [])
--
-- and `show` is inward-INTRODUCING (`proof.Flat.push-flat`).  So a
-- `Wrap`-minted boundary can hand its body a context with an assignment
-- on the stack.  Here is a CLOSED, well-typed `Wrap` redex at [] ∥ []
-- that does exactly that.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.Reduction

Sg : Store
Sg = `ℕᴿ ∷ []

-- the boundary's conversion: ONE inward-introducing crossing
cc : Conv
cc = show zero (lvl zero) ∷ᶜ id (`ℕ ⇒ `ℕ)

-- its interior has an assignment on the stack; the exterior is empty
Δᵢ : Ctxᵗ
Δᵢ = asgn (lvl zero) ∷ [] ∥ []

⊢cc : Sg ∣ Δᵢ ⊢ cc ∶ (`ℕ ⇒ `ℕ) ⇝ (`ℕ ⇒ `ℕ) ⊣ ([] ∥ [])
⊢cc = conv-cons (conv-show (a-lvl l-here) (wf-⇒ wf-ℕ wf-ℕ) pop-here
                  (λ ())) (conv-id (wf-⇒ wf-ℕ wf-ℕ))

Vf : Term
Vf = (ƛ `ℕ ∙ (` zero)) ⟨ cc ⟩

⊢Vf : Sg ∣ ([] ∥ []) ∣ [] ⊢ Vf ⦂ (`ℕ ⇒ `ℕ)
⊢Vf = ⊢⟨⟩ (nf-cons nf-show nf-id irr-id) (⊢ƛ wf-ℕ (⊢` here)) ⊢cc

redex : Sg ∣ ([] ∥ []) ∣ [] ⊢ Vf · ($ 1) ⦂ `ℕ
redex = ⊢· ⊢Vf ⊢$

-- it IS a Wrap redex …
split : arr `ℕ cc ≡ just (hide zero (lvl zero) ∷ᶜ id `ℕ
                         , show zero (lvl zero) ∷ᶜ id `ℕ)
split = refl

vf : Value Vf
vf = V⟨⟩ Sƛ (nf-cons nf-show nf-id irr-id) (inert-arr `ℕ split)

wrapped : Sg ∣ ([] ∥ []) ⊢ Vf · ($ 1)
        —→ ((ƛ `ℕ ∙ (` zero)) · (($ 1) ⟨ hide zero (lvl zero) ∷ᶜ id `ℕ ⟩))
             ⟨ show zero (lvl zero) ∷ᶜ id `ℕ ⟩ ⊣ Sg
wrapped = Wrap vf (Vs S$) split

-- … and the boundary it mints hands its body a NON-EMPTY stack.
reached : interior (show zero (lvl zero) ∷ᶜ id `ℕ) ([] ∥ [])
        ≡ just (asgn (lvl zero) ∷ [] ∥ [])
reached = refl
