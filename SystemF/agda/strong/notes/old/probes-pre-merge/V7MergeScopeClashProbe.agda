module strong.notes.probes.V7MergeScopeClashProbe where

-- PROBE (2026-09-13): `preserve-Merge` is FALSE under the spine
-- discipline as the rules stand.
--
-- The configuration: the inner boundary's scope RE-REVEALS an anchor
-- that the outer boundary conceals and seals.  In notes-v7 notation,
-- with one represented anchor γ ≔ ℕ→ℕ, revealed in the outer context Δ:
--
--   ν ∅, conceal γ [ ν ∅, reveal γ [ λx:ℕ. x ∣ id (ℕ→ℕ) ] ∣ seal γ; id X ]
--
-- The outer boundary conceals γ, so its conversion legitimately crosses
-- that flip with `seal γ` (off at the interior, on at the exterior).
-- The inner boundary flips γ back ON and bridges the flip with a bare
-- `id (ℕ→ℕ)` — `conv-id` allows it, because ℕ→ℕ never mentions γ's name.
--
-- `Merge` concatenates the scopes and appends the conversions:
--
--   ν ∅, (conceal γ ; reveal γ) [ λx:ℕ. x ∣ seal γ; id X ]
--
-- The merged scope's flips CANCEL: the interior context is Δ itself,
-- with γ REVEALED.  But the `seal γ` head survives the append verbatim,
-- and `conv-seal` demands `FlipAt γ Δᵢ Δₛ` — the interior must have γ
-- CONCEALED.  It does not.  The contractum has NO typing derivation:
-- the bare `id` bridged a flip for free on the way in, and the appended
-- conversion now performs one flip fewer than the merged scope requires.
--
-- Everything below is closed and machine-checked: `redex-typed`,
-- `redex-steps` (by `Merge`), and `contractum-untyped`.

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.Reduction

-- One anchor γ (index zero), REVEALED, represented by ℕ→ℕ.
Δ₀ : Ctxᵗ
Δ₀ = anch revealed (bindA (`ℕᴿ ⇒ᴿ `ℕᴿ)) ∷ []

-- γ concealed: the outer boundary's interior, the inner's exterior.
Δc : Ctxᵗ
Δc = anch concealed (bindA (`ℕᴿ ⇒ᴿ `ℕᴿ)) ∷ []

inner : Term
inner = ν [] , (reveal zero ∷ []) [ ƛ `ℕ ∙ ` zero ∣ id (`ℕ ⇒ `ℕ) ]

redex : Term
redex = ν [] , (conceal zero ∷ [])
          [ inner ∣ seal zero ∷ᶜ id (` zero) ]

contractum : Term
contractum = ν [] , (conceal zero ∷ reveal zero ∷ [])
               [ ƛ `ℕ ∙ ` zero ∣ seal zero ∷ᶜ id (` zero) ]

----------------------------------------------------------------------
-- The redex is well-typed.
----------------------------------------------------------------------

⊢λ : Δ₀ ∣ [] ⊢ ƛ `ℕ ∙ ` zero ⦂ `ℕ ⇒ `ℕ
⊢λ = ⊢ƛ wf-ℕ (⊢` here)

-- The bare id bridges the reveal-γ flip: ℕ→ℕ mentions no names, so
-- `SameTy` is purely structural, and `SameBindings` ignores visibility.
inner-conv : Δ₀ ⊢ id (`ℕ ⇒ `ℕ) ∶ `ℕ ⇒ `ℕ ⇝ `ℕ ⇒ `ℕ ⊣ Δc
inner-conv = conv-id (same-⇒ same-ℕ same-ℕ) (sb-∷ sb[])

⊢inner : Δc ∣ [] ⊢ inner ⦂ `ℕ ⇒ `ℕ
⊢inner = ⊢ν store[] (scope∷ rev-here scope[]) nf-id ⊢λ inner-conv

-- The outer conversion seals γ across the outer conceal: FlipAt γ Δc Δ₀.
outer-conv : Δc ⊢ seal zero ∷ᶜ id (` zero) ∶ `ℕ ⇒ `ℕ ⇝ ` zero ⊣ Δ₀
outer-conv =
  conv-cons
    (conv-seal n-here r-here (read-⇒ read-ℕ read-ℕ) flip-here)
    (tail-id (wf-var tv-here))

redex-typed : Δ₀ ∣ [] ⊢ redex ⦂ ` zero
redex-typed =
  ⊢ν store[] (scope∷ con-here scope[])
     (nf-cons nf-seal nf-id irr-id)
     ⊢inner outer-conv

----------------------------------------------------------------------
-- The redex steps to the contractum, by Merge.
----------------------------------------------------------------------

inner-value : Value inner
inner-value = Vν Sƛ nf-id (applies-arr `ℕ refl)

redex-steps : Δ₀ ⊢ redex -→ contractum
redex-steps = Merge inner-value

----------------------------------------------------------------------
-- The contractum has NO typing derivation, at any type.
----------------------------------------------------------------------

-- `FlipAt zero` requires the head entry CONCEALED on the off side.
flip-revealed : ∀ {Δ Δ₂ b} → FlipAt zero (anch revealed b ∷ Δ) Δ₂ → ⊥
flip-revealed ()

contractum-untyped : ∀ {B} → Δ₀ ∣ [] ⊢ contractum ⦂ B → ⊥
contractum-untyped
  (⊢ν store[]
      (scope∷ con-here (scope∷ rev-here scope[]))
      nf body (conv-cons (conv-seal x r rd flip) tl)) =
  flip-revealed flip

----------------------------------------------------------------------
-- CLASS 2: the drift needs no seal-at-revealed corner.
----------------------------------------------------------------------
--
-- Two anchors: β (index 0, revealed, ≔ ℕ→ℕ) and δ (index 1, concealed,
-- ≔ ℕ).  The outer boundary conceals β and seals it; the inner boundary
-- reveals the UNRELATED δ and bridges that flip with a bare id.
--
--   ν ∅, conceal β [ ν ∅, reveal δ [ λx:ℕ. x ∣ id (ℕ→ℕ) ] ∣ seal β; id X ]
--
-- After Merge the scope's net effect is: β stays on, δ comes ON.  The
-- appended conversion still performs exactly one flip — β's — so its
-- reflexive terminator lands at a context with δ ON, while `⊢ν` demands
-- the store context, where δ is OFF.  No head touches δ; nothing can
-- absorb the drift.  This class survives ANY loosening of seal/unseal
-- alone: the mismatch is net-flip arithmetic, not a rule corner.

Δ² : Ctxᵗ
Δ² = anch revealed (bindA (`ℕᴿ ⇒ᴿ `ℕᴿ)) ∷ anch concealed (bindA `ℕᴿ) ∷ []

-- β concealed (the outer interior); then δ also revealed (inner interior).
Δ²c : Ctxᵗ
Δ²c = anch concealed (bindA (`ℕᴿ ⇒ᴿ `ℕᴿ)) ∷ anch concealed (bindA `ℕᴿ) ∷ []

inner² : Term
inner² = ν [] , (reveal (suc zero) ∷ []) [ ƛ `ℕ ∙ ` zero ∣ id (`ℕ ⇒ `ℕ) ]

redex² : Term
redex² = ν [] , (conceal zero ∷ [])
           [ inner² ∣ seal zero ∷ᶜ id (` zero) ]

contractum² : Term
contractum² = ν [] , (conceal zero ∷ reveal (suc zero) ∷ [])
                [ ƛ `ℕ ∙ ` zero ∣ seal zero ∷ᶜ id (` zero) ]

redex²-typed : Δ² ∣ [] ⊢ redex² ⦂ ` zero
redex²-typed =
  ⊢ν store[] (scope∷ con-here scope[])
     (nf-cons nf-seal nf-id irr-id)
     (⊢ν store[] (scope∷ (rev-under rev-here) scope[]) nf-id
         (⊢ƛ wf-ℕ (⊢` here))
         (conv-id (same-⇒ same-ℕ same-ℕ) (sb-∷ (sb-∷ sb[]))))
     (conv-cons
       (conv-seal n-here r-here (read-⇒ read-ℕ read-ℕ) flip-here)
       (tail-id (wf-var tv-here)))

redex²-steps : Δ² ⊢ redex² -→ contractum²
redex²-steps = Merge (Vν Sƛ nf-id (applies-arr `ℕ refl))

-- The seal β head flips β; the terminator then sits at a context with δ
-- ON, but `⊢ν` pins it to Δ², where δ is OFF.  `tail-id` is reflexive,
-- so the derivation dies at the terminator.
contractum²-untyped : ∀ {B} → Δ² ∣ [] ⊢ contractum² ⦂ B → ⊥
contractum²-untyped
  (⊢ν store[]
      (scope∷ con-here (scope∷ (rev-under rev-here) scope[]))
      nf body
      (conv-cons (conv-seal x r rd flip-here) ()))
