module strong.notes.ShowHide where

-- Strong System F v8 — A SOURCE PROGRAM THAT REDUCES TO A `show`/`hide`
-- PAIR AT DIFFERENT ADDRESSES (2026-09-16).
--
-- Asked whether the configuration that forces `hide`/`show` to carry an
-- address is reachable from a program, or merely well-formed.  It is
-- reachable, and the mechanism is TWO SEPARATE INSTANTIATIONS:
--
--     id = Λ (λ x:ℕ. x)          : ∀X. ℕ→ℕ          -- X unused
--     W  = id [𝔹]                : ℕ→ℕ              -- FIRST  ∀
--     k  = λ f:ℕ→ℕ. Λ (λ y:ℕ. f) : (ℕ→ℕ) → ∀X. ℕ→ℕ→ℕ
--     ---------------------------------------------------------------
--     (k W) [𝔹]                                     -- SECOND ∀
--
-- `X` is unused in both, which is what makes `revTy` take its MISS
-- branch and emit an identity crossing rather than a seal.
--
--   * instantiating `id` seals the result at the first ∀'s address,
--     which `Alloc` discharges to `lvl 0`, so `W` is a value behind
--     `show 0 (lvl 0)`;
--   * applying `k` substitutes `W` UNDER the second `Λ`, so `crossΛ`
--     wraps it in `hide 0 (bse 0)` — the SECOND binder's address;
--   * the two boundaries are adjacent, `Merge` fires, and the seam
--     survives normalization because `fuse` compares the address;
--   * instantiating again discharges the second binder to `lvl 1`,
--     leaving `show 0 (lvl 0) ∷ᶜ hide 0 (lvl 1)` — one name, two
--     distinct store levels.
--
-- Every step below is a checked `—→` of the actual reduction relation.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

-- ∀X. ℕ→ℕ   — the bound X is UNUSED, so instantiating takes `revTy`'s
-- MISS branch and emits a `show`
idΛ : Term
idΛ = Λ (ƛ `ℕ ∙ ` 0)

-- step 1: the FIRST instantiation
W₀ : Term
W₀ = idΛ • (`ℕ ⇒ `ℕ) [ `𝔹 ]

step₁ : [] ∣ ([] ∥ []) ⊢ W₀
      —→ ν `𝔹ᴿ ∙ ((ƛ `ℕ ∙ ` 0) ⟨ revTy zero (bse zero) `𝔹 (`ℕ ⇒ `ℕ) ⟩) ⊣ []
step₁ = TyBeta (Vs Sƛ) quote-𝔹

-- and the builder really is a bare `show`
builder : revTy zero (bse zero) `𝔹 (`ℕ ⇒ `ℕ)
        ≡ show 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ)
builder = refl

-- step 2: discharge.  The ν's address becomes the store's level 0.
W : Term
W = (ƛ `ℕ ∙ ` 0) ⟨ show 0 (lvl 0) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩

step₂ : [] ∣ ([] ∥ [])
      ⊢ ν `𝔹ᴿ ∙ ((ƛ `ℕ ∙ ` 0) ⟨ show 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩)
      —→ W ⊣ (`𝔹ᴿ ∷ [])
step₂ = Alloc

-- W is a value: a λ behind an INERT conversion (its target is an
-- arrow, so `arr` splits it)
W-value : Value W
W-value = V⟨⟩ Sƛ (nf-cons nf-show nf-id irr-id) (inert-arr `ℕ refl)

-- step 3: W is substituted UNDER A Λ, so `crossΛ` wraps it — and the
-- wrap's `hide` names the SECOND binder, not the one W was sealed by
prog : Term
prog = (ƛ (`ℕ ⇒ `ℕ) ∙ Λ (ƛ `ℕ ∙ ` 1)) · W

step₃ : (`𝔹ᴿ ∷ []) ∣ ([] ∥ [])
      ⊢ prog —→ (Λ (ƛ `ℕ ∙ ` 1)) [ W ∶ `ℕ ⇒ `ℕ ]ᵐ ⊣ (`𝔹ᴿ ∷ [])
step₃ = Beta W-value

-- and that substitution really does produce the two adjacent
-- boundaries, at DIFFERENT addresses: `lvl 0` inside, `bse 0` outside
after₃ : (Λ (ƛ `ℕ ∙ ` 1)) [ W ∶ `ℕ ⇒ `ℕ ]ᵐ
       ≡ Λ (ƛ `ℕ ∙ (W ⟨ hide 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩))
after₃ = refl

-- THE CONFIGURATION.  Merging the two boundaries puts a `show` and a
-- `hide` at the SAME NAME and DIFFERENT ADDRESSES next to each other,
-- and normalization cannot remove them: `fuse` compares the address.
merged : Conv
merged = (show 0 (lvl 0) ∷ᶜ id (`ℕ ⇒ `ℕ)) ⨟ (hide 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ))

step₄ : (`𝔹ᴿ ∷ []) ∣ (asgn (bse zero) ∷ [] ∥ addr ∷ [])
      ⊢ W ⟨ hide 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩
      —→ (ƛ `ℕ ∙ ` 0) ⟨ merged ⟩ ⊣ (`𝔹ᴿ ∷ [])
step₄ = Merge W-value

seam : merged ≡ show 0 (lvl 0) ∷ᶜ hide 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ)
seam = refl

survives : fuse (show 0 (lvl 0)) (hide 0 (bse 0)) ≡ nothing
survives = refl

------------------------------------------------------------------------
-- The two addresses are two SEPARATE INSTANTIATIONS
------------------------------------------------------------------------
-- Instantiate the result of step 3 in its turn.  Its `ν` discharges to
-- the store's NEXT level, and that substitution reaches the wrap's
-- `bse 0` too — so the seam becomes two distinct store levels.

V₃ : Term
V₃ = Λ (ƛ `ℕ ∙ (W ⟨ hide 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩))

step₅ : (`𝔹ᴿ ∷ []) ∣ ([] ∥ [])
      ⊢ V₃ • (`ℕ ⇒ `ℕ ⇒ `ℕ) [ `𝔹 ]
      —→ ν `𝔹ᴿ ∙ ((ƛ `ℕ ∙ (W ⟨ hide 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩))
                    ⟨ revTy zero (bse zero) `𝔹 (`ℕ ⇒ `ℕ ⇒ `ℕ) ⟩)
      ⊣ (`𝔹ᴿ ∷ [])
step₅ = TyBeta (Vs Sƛ) quote-𝔹

step₆ : (`𝔹ᴿ ∷ []) ∣ ([] ∥ [])
      ⊢ ν `𝔹ᴿ ∙ ((ƛ `ℕ ∙ (W ⟨ hide 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩))
                   ⟨ show 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ ⇒ `ℕ) ⟩)
      —→ (ƛ `ℕ ∙ (W ⟨ hide 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩))
            ⟨ show 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ ⇒ `ℕ) ⟩
      ⊣ (`𝔹ᴿ ∷ `𝔹ᴿ ∷ [])
step₆ = Alloc

-- and NOW the inner seam is two distinct store levels
merged′ : (show 0 (lvl 0) ∷ᶜ id (`ℕ ⇒ `ℕ)) ⨟ (hide 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ))
        ≡ show 0 (lvl 0) ∷ᶜ hide 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ)
merged′ = refl

------------------------------------------------------------------------
-- THE WHOLE TRACE, as one —↠
------------------------------------------------------------------------
-- Applying the result to a numeral is what brings the merge into
-- evaluation position: nothing reduces under a `Λ` or a `λ`.

k : Term
k = ƛ (`ℕ ⇒ `ℕ) ∙ Λ (ƛ `ℕ ∙ ` 1)

main : Term
main = ((k · W₀) • (`ℕ ⇒ `ℕ ⇒ `ℕ) [ `𝔹 ]) · $ 7

t₁ t₂ t₃ t₄ t₅ : Term
t₁ = ((k · (ν `𝔹ᴿ ∙ ((ƛ `ℕ ∙ ` 0)
              ⟨ show 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩)))
        • (`ℕ ⇒ `ℕ ⇒ `ℕ) [ `𝔹 ]) · $ 7
t₂ = ((k · W) • (`ℕ ⇒ `ℕ ⇒ `ℕ) [ `𝔹 ]) · $ 7
t₃ = (V₃ • (`ℕ ⇒ `ℕ ⇒ `ℕ) [ `𝔹 ]) · $ 7
t₄ = (ν `𝔹ᴿ ∙ ((ƛ `ℕ ∙ (W ⟨ hide 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩))
                 ⟨ show 0 (bse 0) ∷ᶜ id (`ℕ ⇒ `ℕ ⇒ `ℕ) ⟩)) · $ 7
t₅ = ((ƛ `ℕ ∙ (W ⟨ hide 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩))
        ⟨ show 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ ⇒ `ℕ) ⟩) · $ 7

s₁ : [] ∣ ([] ∥ []) ⊢ main —→ t₁ ⊣ []
s₁ = ξ-·-l (ξ-•[] (ξ-·-r (Vs Sƛ) (TyBeta (Vs Sƛ) quote-𝔹)))

s₂ : [] ∣ ([] ∥ []) ⊢ t₁ —→ t₂ ⊣ (`𝔹ᴿ ∷ [])
s₂ = ξ-·-l (ξ-•[] (ξ-·-r (Vs Sƛ) Alloc))

s₃ : (`𝔹ᴿ ∷ []) ∣ ([] ∥ []) ⊢ t₂ —→ t₃ ⊣ (`𝔹ᴿ ∷ [])
s₃ = ξ-·-l (ξ-•[] (Beta W-value))

s₄ : (`𝔹ᴿ ∷ []) ∣ ([] ∥ []) ⊢ t₃ —→ t₄ ⊣ (`𝔹ᴿ ∷ [])
s₄ = ξ-·-l (TyBeta (Vs Sƛ) quote-𝔹)

s₅ : (`𝔹ᴿ ∷ []) ∣ ([] ∥ []) ⊢ t₄ —→ t₅ ⊣ (`𝔹ᴿ ∷ `𝔹ᴿ ∷ [])
s₅ = ξ-·-l Alloc

t₆ t₇ t₈ t₉ : Term
t₆ = ((ƛ `ℕ ∙ (W ⟨ hide 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩))
        · ($ 7 ⟨ hide 0 (lvl 1) ∷ᶜ id `ℕ ⟩))
       ⟨ show 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩
t₇ = ((ƛ `ℕ ∙ (W ⟨ hide 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩)) · $ 7)
       ⟨ show 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩
t₈ = (W ⟨ hide 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩)
       ⟨ show 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩
t₉ = ((ƛ `ℕ ∙ ` 0) ⟨ show 0 (lvl 0) ∷ᶜ hide 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩)
       ⟨ show 0 (lvl 1) ∷ᶜ id (`ℕ ⇒ `ℕ) ⟩

Σ₂ : Store
Σ₂ = `𝔹ᴿ ∷ `𝔹ᴿ ∷ []

s₆ : Σ₂ ∣ ([] ∥ []) ⊢ t₅ —→ t₆ ⊣ Σ₂
s₆ = Wrap (V⟨⟩ Sƛ (nf-cons nf-show nf-id irr-id) (inert-arr `ℕ refl))
          (Vs S$) refl

s₇ : Σ₂ ∣ ([] ∥ []) ⊢ t₆ —→ t₇ ⊣ Σ₂
s₇ = ξ-⟨⟩ refl (ξ-·-r (Vs Sƛ) (Const literal-$ refl))

s₈ : Σ₂ ∣ ([] ∥ []) ⊢ t₇ —→ t₈ ⊣ Σ₂
s₈ = ξ-⟨⟩ refl (Beta (Vs S$))

-- THE STEP.  Merging the two boundaries leaves a `show` and a `hide`
-- at the same name and two DIFFERENT store levels, side by side.
s₉ : Σ₂ ∣ ([] ∥ []) ⊢ t₈ —→ t₉ ⊣ Σ₂
s₉ = ξ-⟨⟩ refl (Merge W-value)

trace : [] ∣ ([] ∥ []) ⊢ main —↠ t₉ ⊣ Σ₂
trace = s₁ then s₂ then s₃ then s₄ then s₅ then s₆ then s₇ then s₈
          then s₉ then done
