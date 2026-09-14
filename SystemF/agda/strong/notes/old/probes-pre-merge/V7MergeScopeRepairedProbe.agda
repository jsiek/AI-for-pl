module strong.notes.probes.V7MergeScopeRepairedProbe where

-- PROBE (2026-09-13): the spine-only conversion rules repair `Merge`.
--
-- Under the earlier `FlipAt` discipline the two `Merge` configurations of
-- `notes/old/probes-pre-merge/V7MergeScopeClashProbe.agda` stepped from
-- well-typed redexes to UNTYPABLE contracta.  The repair, per Jeremy's
-- observation: a conversion only talks about the reveals/conceals
-- involved in the types it converts, so `conv-seal`/`conv-unseal`
-- constrain their contexts by `SameBindings` alone, and visibility is
-- constrained only where a lookup (`_∋n_:=_`, `_⊢_⇓_`) forces it.
--
-- This file re-runs both configurations and types the CONTRACTA.

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.Reduction

----------------------------------------------------------------------
-- Class 1: the inner scope re-reveals the anchor the outer seals.
----------------------------------------------------------------------

Δ₀ : Ctxᵗ
Δ₀ = anch revealed (bindA (`ℕᴿ ⇒ᴿ `ℕᴿ)) ∷ []

redex : Term
redex = ν [] , (conceal zero ∷ [])
          [ ν [] , (reveal zero ∷ []) [ ƛ `ℕ ∙ ` zero ∣ id (`ℕ ⇒ `ℕ) ]
          ∣ seal zero ∷ᶜ id (` zero) ]

contractum : Term
contractum = ν [] , (conceal zero ∷ reveal zero ∷ [])
               [ ƛ `ℕ ∙ ` zero ∣ seal zero ∷ᶜ id (` zero) ]

redex-steps : Δ₀ ⊢ redex -→ contractum
redex-steps = Merge (Vν Sƛ nf-id (applies-arr `ℕ refl))

-- The merged scope's flips cancel, so the interior is Δ₀ itself, with γ
-- REVEALED — and the seal types THERE: `SameBindings Δ₀ Δ₀` holds, the
-- name and the read-back are looked up where they live.
contractum-typed : Δ₀ ∣ [] ⊢ contractum ⦂ ` zero
contractum-typed =
  ⊢ν store[] (scope∷ con-here (scope∷ rev-here scope[]))
     (nf-cons nf-seal nf-id irr-id)
     (⊢ƛ wf-ℕ (⊢` here))
     (conv-cons
       (conv-seal n-here r-here (read-⇒ read-ℕ read-ℕ) sb-refl)
       (tail-id (wf-var tv-here)))

----------------------------------------------------------------------
-- Class 2: the inner scope reveals an anchor the conversion never
-- touches.
----------------------------------------------------------------------

Δ² : Ctxᵗ
Δ² = anch revealed (bindA (`ℕᴿ ⇒ᴿ `ℕᴿ)) ∷ anch concealed (bindA `ℕᴿ) ∷ []

redex² : Term
redex² = ν [] , (conceal zero ∷ [])
           [ ν [] , (reveal (suc zero) ∷ []) [ ƛ `ℕ ∙ ` zero ∣ id (`ℕ ⇒ `ℕ) ]
           ∣ seal zero ∷ᶜ id (` zero) ]

contractum² : Term
contractum² = ν [] , (conceal zero ∷ reveal (suc zero) ∷ [])
                [ ƛ `ℕ ∙ ` zero ∣ seal zero ∷ᶜ id (` zero) ]

redex²-steps : Δ² ⊢ redex² -→ contractum²
redex²-steps = Merge (Vν Sƛ nf-id (applies-arr `ℕ refl))

-- The interior has β off and δ on; the seal's target context is chosen
-- to be Δ² directly — the δ drift the bare id used to bridge is absorbed
-- by the head's loose target side, and the terminator sits reflexively
-- at Δ², as `⊢ν` demands.
contractum²-typed : Δ² ∣ [] ⊢ contractum² ⦂ ` zero
contractum²-typed =
  ⊢ν store[] (scope∷ con-here (scope∷ (rev-under rev-here) scope[]))
     (nf-cons nf-seal nf-id irr-id)
     (⊢ƛ wf-ℕ (⊢` here))
     (conv-cons
       (conv-seal n-here r-here (read-⇒ read-ℕ read-ℕ)
         (sb-∷ (sb-∷ sb[])))
       (tail-id (wf-var tv-here)))
