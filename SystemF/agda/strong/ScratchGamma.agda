module strong.ScratchGamma where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context
open import strong.Boundary

-- A boundary whose conceal rep MENTIONS the revealed variable.
--   Γ₉ = [X(0) abstract]     Θ₉ = [ ↓X(0):=(` 0) , ↑Z:=(` 0) ]
-- revs = 1, cmax = 1, interior Ψ = prepAbst 1 (dropN 1 Γ₉) = [Z(0) abst].
Γ₉ : TCtx
Γ₉ = abst ∷ []

Θ₉ : BCtx
Θ₉ = cnc 0 (` 0) ∷ rvl (` 0) ∷ []

-- interior has the reveal var Z at index 0.
_ : intOf Γ₉ Θ₉ ≡ abst ∷ []
_ = refl

-- bwf↓ ACCEPTS the conceal rep (` 0) as living over the interior Ψ = [Z(0)]:
_ : Γ₉ ∣ intOf Γ₉ Θ₉ ⊢ᵇ Θ₉
_ = bwf↓ here-abst (wf-var here-abst) (bwf↑ (wf-var here-abst) bwf[])

-- The concealed Γ-var 0 sits at bframe index revs+0 = 1.  Its INTERNAL face:
-- the conceal resolves to its rep (` 0) = the reveal var Z(0).  FIXED γᵇ no longer
-- shifts the rep, so it correctly gives (` 0):
_ : substᵗ (γᵇ Θ₉) (` 1) ≡ ` 0
_ = refl

-- and the reveal var itself (bframe idx 0) still passes through to Z(0):
_ : substᵗ (γᵇ Θ₉) (` 0) ≡ ` 0
_ = refl
