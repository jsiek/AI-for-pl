module strong.notes.PeelPremise where

-- PROTOTYPE, not installed: what the premise `Peel` would need looks
-- like, and whether it is satisfiable.  Nothing here is imported by the
-- rule set; `strong.Reduction` is unchanged.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.TypeCheck

private
  variable
    η η′ : TyCtx
    X : ℕ
    α : RVar
    A B R : Ty
    s t s′ t′ r u : Conv

------------------------------------------------------------------------
-- 1. Reading a conversion in the representation universe
------------------------------------------------------------------------

-- Exactly `_⊢_~_`, one universe up: the ordinary NAMES a conversion
-- carries are translated through the name map, and everything else is
-- structural.  `id` carries a type, so it defers to `_⊢_~_`.
infix 4 _⊩_~_
data _⊩_~_ (η : TyCtx) : Conv → Conv → Set where
  sameᶜ-id     : η ⊢ A ~ R → η ⊩ id A ~ id R
  sameᶜ-seal   : η ∋ˡ X := α → η ⊩ seal X ~ seal α
  sameᶜ-unseal : η ∋ˡ X := α → η ⊩ unseal X ~ unseal α
  sameᶜ-fun    : η ⊩ s ~ r → η ⊩ t ~ u → η ⊩ s ↦ t ~ r ↦ u
  sameᶜ-all    : (zero ∷ shiftNames η) ⊩ s ~ r → η ⊩ `∀ s ~ `∀ r

-- Two ordinary spellings of ONE representation-universe conversion.
SameConv : Ctxᵗ → Conv → Ctxᵗ → Conv → Set
SameConv Γ s Γ′ s′ = ∃[ r ] ((names Γ ⊩ s ~ r) × (names Γ′ ⊩ s′ ~ r))

------------------------------------------------------------------------
-- 2. It determines the spelling, so a rule carrying it stays a function
------------------------------------------------------------------------

sameᶜ-rep-unique : η ⊩ s ~ r → η ⊩ s ~ u → r ≡ u
sameᶜ-rep-unique (sameᶜ-id a) (sameᶜ-id a′) =
  cong id (same-rep-unique a a′)
sameᶜ-rep-unique (sameᶜ-seal d) (sameᶜ-seal d′) =
  cong seal (∋ˡ-det d d′)
sameᶜ-rep-unique (sameᶜ-unseal d) (sameᶜ-unseal d′) =
  cong unseal (∋ˡ-det d d′)
sameᶜ-rep-unique (sameᶜ-fun a b) (sameᶜ-fun a′ b′) =
  cong₂ _↦_ (sameᶜ-rep-unique a a′) (sameᶜ-rep-unique b b′)
sameᶜ-rep-unique (sameᶜ-all a) (sameᶜ-all a′) =
  cong `∀ (sameᶜ-rep-unique a a′)

sameᶜ-target-unique : Unique η → η ⊩ s ~ r → η ⊩ s′ ~ r → s ≡ s′
sameᶜ-target-unique uq (sameᶜ-id a) (sameᶜ-id a′) =
  cong id (same-target-unique uq a a′)
sameᶜ-target-unique uq (sameᶜ-seal d) (sameᶜ-seal d′) =
  cong seal (unique-lookup uq d d′)
sameᶜ-target-unique uq (sameᶜ-unseal d) (sameᶜ-unseal d′) =
  cong unseal (unique-lookup uq d d′)
sameᶜ-target-unique uq (sameᶜ-fun a b) (sameᶜ-fun a′ b′) =
  cong₂ _↦_ (sameᶜ-target-unique uq a a′)
            (sameᶜ-target-unique uq b b′)
sameᶜ-target-unique uq (sameᶜ-all a) (sameᶜ-all a′) =
  cong `∀ (sameᶜ-target-unique
             (unique∷ fresh-zero-shift (unique-shift uq)) a a′)

sameConv-src-unique : Unique η
  → ∃[ r ] ((η ⊩ s ~ r) × (η′ ⊩ t ~ r))
  → ∃[ r ] ((η ⊩ s′ ~ r) × (η′ ⊩ t ~ r))
  → s ≡ s′
sameConv-src-unique uq (r , p , q) (r′ , p′ , q′)
  with sameᶜ-rep-unique q q′
... | refl = sameᶜ-target-unique uq p p′

------------------------------------------------------------------------
-- 3. It is SATISFIABLE exactly where (P) fails
------------------------------------------------------------------------

-- A premise that blocked the rule whenever (P) failed would be no repair
-- at all — it would trade unsoundness for a stuck term.  What makes this
-- one a re-spelling rather than a restriction is that the two contexts
-- hold THE SAME REPRESENTATION VARIABLES.  Both are Δ with the unlocked
-- names inserted: the conversion reading skips the locks, and the dual's
-- reading puts the locked names back.  Only the ORDER differs.
--
-- On §5's mixed frame — `lock 0 0` then `unlock 0 2` over Δ₃ — that is
-- visible directly.  (Values recomputed here rather than cited.)
reps₃ : RepCtx
reps₃ = bindR `ℕ ∷ bindR `𝔹 ∷ bindR `ℕ ∷ []

Δ₃ : Ctxᵗ
Δ₃ = reps₃ ∣ (0 ∷ 1 ∷ [])

Mixed : CtxMorph
Mixed = morph [] (unlock 0 2 ∷ lock 0 0 ∷ [])

nmC : Ctxᵗ → CtxMorph → Maybe TyCtx
nmC Γ Θ with conversion? Γ Θ
nmC Γ Θ | just (Γᶜ , _) = just (names Γᶜ)
nmC Γ Θ | nothing = nothing

Δᶜ Δᵈ : Ctxᵗ
Δᶜ = reps₃ ∣ (2 ∷ 0 ∷ 1 ∷ [])
Δᵈ = reps₃ ∣ (0 ∷ 2 ∷ 1 ∷ [])

-- where `s` is read
is-Δᶜ : nmC Δ₃ Mixed ≡ just (names Δᶜ)
is-Δᶜ = refl

-- where `s` would be used — a PERMUTATION of it, not a smaller context
is-Δᵈ : nmC (reps₃ ∣ (2 ∷ 1 ∷ [])) (dualMorph Mixed) ≡ just (names Δᵈ)
is-Δᵈ = refl

-- so the conversion that `Peel` carries has a spelling on both sides:
-- representation variable 2 sits at ordinary index 0 in one and 1 in the
-- other, and the premise is exactly that renaming.
respelled : SameConv Δᵈ (unseal 1) Δᶜ (unseal 0)
respelled = unseal 2 , sameᶜ-unseal (there here) , sameᶜ-unseal here

------------------------------------------------------------------------
-- 4. The rule, and what installing it would still owe
------------------------------------------------------------------------

-- `Peel` would read, in the shape the other three repairs already have —
-- name the target spelling, carry a `Same…` relating it to the source,
-- and a `Unique` to keep the rule a function:
--
--   Peel : ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t} → Value V → Value W
--     → Δ ⊢ᶜ Θ ⇒ Δᶜ                     -- where `s` is read
--     → Δ ⊢ⁱ Θ ⇒ Δᵢ
--     → Δᵢ ⊢ᶜ dualMorph Θ ⇒ Δᵈ           -- where `s′` is used
--     → Unique (names Δᵈ)
--     → SameConv Δᵈ s′ Δᶜ s
--     → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
--         -→ (V · (renᴹ² (ren² idᵗ (wkN (numBinds Θ))) W
--                     ⟪ dualMorph Θ , s′ ⟫)) ⟪ Θ , t ⟫
--
-- `det` closes with `conversion-functional`, `interior-functional` and
-- `sameConv-src-unique`, as the other three do.  `t` needs no premise:
-- it stays on the same boundary, at Δᶜ, where it was read.
--
-- THE OPEN OBLIGATION is §3 in general, not on one frame:
--
--   (Q)  conv(dualMorph Θ, int(Θ, Δ)) is a PERMUTATION of conv(Θ, Δ)
--
-- both being Δ with the unlocked names inserted.  (P) is the special case
-- where that permutation is the identity, and the point of the premise is
-- to stop needing it.  But without (Q) the premise can be UNSATISFIABLE,
-- and then `Peel` is stuck rather than unsound — progress, not
-- preservation, is what would fail.  So (Q) is what the port of progress
-- would have to prove, and it is a claim about name maps alone, with no
-- conversion, no type and no term in it.  That is the trade: (P) was
-- false and (Q) is weaker, but nothing here shows (Q) is true.
