module strong.ScratchGamma where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context
open import strong.Unfold using (≡→≈)
open import strong.Boundary

-- A boundary whose conceal rep MENTIONS the revealed variable — the evidence
-- for PLAN.md §2's first finding (γᵇ must NOT shift a conceal rep past the
-- reveal block, because a conceal rep lives over the WHOLE interior).
--
--   Γ₉ = [X(0):=ℕ]          Θ₉ = [ ↓X(0):=(` 0) , ↑Z:=ℕ ]
--   revs = 1, cmax = 1, interior Ψ = [Z(0):=ℕ]
--
-- Updated 2026-09-04: the exterior must now KNOW X — the reversal-form (bwf-↓)
-- licenses a conceal only against the exterior's own knowledge — and the reveal
-- puts that knowledge into the interior.  The finding itself is unchanged.
Γ₉ : TCtx
Γ₉ = rvld `ℕ ∷ []

Θ₉ : BCtx
Θ₉ = cnc 0 (` 0) ∷ rvl `ℕ ∷ []

-- the interior has the reveal var Z at index 0, carrying its knowledge
_ : intOf Γ₉ Θ₉ ≡ rvld `ℕ ∷ []
_ = refl

-- bwf↓ ACCEPTS the conceal rep (` 0) as living over the interior Ψ = [Z:=ℕ];
-- its read-back through the boundary is ℕ, which is exactly Γ₉'s knowledge
_ : outRead Θ₉ (` 0) ≡ `ℕ
_ = refl

_ : Γ₉ ∣ intOf Γ₉ Θ₉ ⊢ᵇ Θ₉
_ = bwf↓ here (≡→≈ refl) (wf-var here-rvld) (bwf↑ wf-ℕ bwf[])

-- The concealed Γ-var 0 sits at bframe index revs+0 = 1.  Its INTERNAL face:
-- the conceal resolves to its rep (` 0) = the reveal var Z(0).  The FIXED γᵇ
-- no longer
-- shifts the rep, so it correctly gives (` 0):
_ : substᵗ (γᵇ Θ₉) (` 1) ≡ ` 0
_ = refl

-- and the reveal var itself (bframe idx 0) still passes through to Z(0):
_ : substᵗ (γᵇ Θ₉) (` 0) ≡ ` 0
_ = refl
