module strong.notes.AppBndExample where

-- WHAT AppBnd DOES TO THE COLOURS, on one complete run  (2026-09-11).
--
--     (λg:ℕ→ℕ. ΛX. g · 5) · (λz:ℕ. z)
--
-- Beta substitutes the identity for g ACROSS the Λ, so the crossΛ wrapper
-- mints a conceal boundary; the next step is then an AppBnd whose operator
-- is that boundary.  Everything below is machine-checked.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

------------------------------------------------------------------------
-- 1.  The program
------------------------------------------------------------------------

Δ₀ : Ctxᵗ                      -- outside:  nothing in scope
Δ₀ = []

Δ₁ : Ctxᵗ                      -- under the Λ:  X in scope
Δ₁ = unmasked abst ∷ []

idℕ : Term                     -- λz:ℕ. z            colours ∅
idℕ = ƛ `ℕ ∙ (` 0 ⟪ [] ⟫) ⟪ [] ⟫

-- ΛX. g · 5   —  the application node and the `g` node both see X = {0}
bodyΛ : Term
bodyΛ = Λ ((` 0 ⟪ 0 ∷ [] ⟫) · ($ 5) ⟪ 0 ∷ [] ⟫) ⟪ [] ⟫

prog : Term
prog = (ƛ (`ℕ ⇒ `ℕ) ∙ bodyΛ ⟪ [] ⟫) · idℕ ⟪ [] ⟫

------------------------------------------------------------------------
-- 2.  STEP 1 — Beta.  The image crosses the Λ, so cross\Λ wraps it.
------------------------------------------------------------------------

-- The substituted image: the identity under a CONCEAL of the new binder.
crossed : Term
crossed = ν conceal (0 ∷ []) [ idℕ ]

crossΛ-is : crossΛ idℕ ≡ crossed
crossΛ-is = refl

after₁ : Term
after₁ = Λ (crossed · ($ 5) ⟪ 0 ∷ [] ⟫) ⟪ [] ⟫

step₁ : Δ₀ ⊢ prog -→ after₁
step₁ = Beta (simple→value Sƛ)

-- COLOUR CHECK.  idℕ's own annotations are ∅, and its new frame inside the
-- conceal is `masked abst ∷ []`, whose colour set is also ∅.  Exact.
idℕ-frame : scopeᵗ (lockχ (0 ∷ []) Δ₁) ≡ []
idℕ-frame = refl

-- and the application node still sees X, as it did in the source.
app-before : scopeᵗ Δ₁ ≡ 0 ∷ []
app-before = refl

------------------------------------------------------------------------
-- 3.  STEP 2 — AppBnd.  THE ONE NODE THAT MOVES.
------------------------------------------------------------------------

-- The argument enters under the DUAL tag — conceal {0} ↦ reveal {0} — and
-- is NOT shifted, because a conceal binds nothing.
dual-is : dualᵇ (conceal (0 ∷ [])) ≡ reveal (0 ∷ [])
dual-is = refl

shiftIn-is : shiftIn (conceal (0 ∷ [])) ($ 5) ≡ $ 5
shiftIn-is = refl

after₂ : Term
after₂ = Λ (ν conceal (0 ∷ [])
              [ idℕ · (ν reveal (0 ∷ []) [ $ 5 ]) ⟪ [] ⟫ ]) ⟪ [] ⟫

step₂ : Δ₀ ⊢ after₁ -→ after₂
step₂ = ξ-Λ (AppBnd (neg→value (Nc ne Sƛ)) (Vk const-$))

-- THE COLOUR THAT CHANGED.  The application node was written under ΛX, so
-- it was born seeing {X} = {0}.  It now sits inside the conceal, where X is
-- hidden, so its colour set is ∅.  Nothing was renamed — a colour was
-- REMOVED.
app-after : scopeᵗ (lockχ (0 ∷ []) Δ₁) ≡ []
app-after = refl

app-colour-changed : scopeᵇ (conceal (0 ∷ [])) (scopeᵗ Δ₁) ≡ []
app-colour-changed = refl

-- THE ARGUMENT, BY CONTRAST, IS EXACT.  The reveal undoes the conceal, so
-- `$ 5` is typed back at Δ₁ — every annotation it carried is still right.
arg-frame : unlockχ (0 ∷ []) (lockχ (0 ∷ []) Δ₁) ≡ Δ₁
arg-frame = unlock-lock (tvs∷ (unmasked abst , ez , nameable) tvs[])

------------------------------------------------------------------------
-- 4.  THE REST OF THE RUN, for completeness
------------------------------------------------------------------------

after₃ : Term                                  -- DropConst on the reveal
after₃ = Λ (ν conceal (0 ∷ []) [ idℕ · ($ 5) ⟪ [] ⟫ ]) ⟪ [] ⟫

step₃ : Δ₀ ⊢ after₂ -→ after₃
step₃ = ξ-Λ (ξ-ν (ξ-·-r (simple→value Sƛ) (DropConst const-$)))

after₄ : Term                                  -- Beta inside the boundary
after₄ = Λ (ν conceal (0 ∷ []) [ $ 5 ]) ⟪ [] ⟫

step₄ : Δ₀ ⊢ after₃ -→ after₄
step₄ = ξ-Λ (ξ-ν (Beta (Vk const-$)))

after₅ : Term                                  -- DropConst on the conceal
after₅ = Λ ($ 5) ⟪ [] ⟫

step₅ : Δ₀ ⊢ after₄ -→ after₅
step₅ = ξ-Λ (DropConst const-$)

run : Δ₀ ⊢ prog -→* after₅
run = step₁ then step₂ then step₃ then step₄ then step₅ then done

------------------------------------------------------------------------
-- 5.  THE cross\Λ WRAPPER, NESTED — one conceal per Λ crossed
------------------------------------------------------------------------

-- v2's crossΛ was `⇑ᴹ W ⟪ morph [] (lock 0 ∷ []) , mkId (⇑ᵗ A) ⟫`; v3's is
-- `ν conceal (0 ∷ []) [ ⇑ᴹ W ]`.  Same mechanism, same insertion point
-- (`⇑ᴵ`, applied by substᵐ's Λ clause).  The only thing v3 dropped is the
-- identity conversion, because a v3 SCOPE boundary carries no conversion:
-- ⊢conceal gives the body the same type as the exterior, so there is
-- nothing for one to mediate.

Δ₂ : Ctxᵗ                      -- Y at slot 0, X at slot 1
Δ₂ = unmasked abst ∷ unmasked abst ∷ []

-- Crossing TWO Λs wraps twice, each conceal naming its own slot.
crossΛ-twice : ⇑ᴵ (⇑ᴵ (ival idℕ (`ℕ ⇒ `ℕ)))
  ≡ ival (ν conceal (0 ∷ []) [ ν conceal (1 ∷ []) [ idℕ ] ]) (`ℕ ⇒ `ℕ)
crossΛ-twice = refl

-- The innermost frame masks BOTH binders, so the colour set there is ∅ —
-- exactly what `renᴹ suc` twice does to idℕ's (empty) annotations.
nested-frame : lockχ (1 ∷ []) (lockχ (0 ∷ []) Δ₂)
  ≡ masked abst ∷ masked abst ∷ []
nested-frame = refl

nested-colours : scopeᵗ (lockχ (1 ∷ []) (lockχ (0 ∷ []) Δ₂)) ≡ []
nested-colours = refl

-- CAUTION FOR THE PROOF PHASE.  The nest is NOT a value — `Nc` demands a
-- SIMPLE body — so "substituting a value into a value yields a value" is
-- FALSE in v3.  The image is an ADMINISTRATIVE REDEX, cleared here by
-- MergeConceal (and in general by PushConv / PushIntro / Commute /
-- DropConst, one per shape `W` can have).
nested-merges : Δ₂ ⊢ ν conceal (0 ∷ []) [ ν conceal (1 ∷ []) [ idℕ ] ]
  -→ ν conceal ((0 ∷ []) ∪ (1 ∷ [])) [ idℕ ]
nested-merges = MergeConceal Sƛ ne ne

merged-is-value : Value (ν conceal (0 ∷ 1 ∷ []) [ idℕ ])
merged-is-value = neg→value (Nc ne Sƛ)
