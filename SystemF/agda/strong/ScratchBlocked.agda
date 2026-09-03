module strong.ScratchBlocked where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context
open import strong.Boundary

-- Non-contiguous conceal set {0,2} over CC = [V0,V1,V2,V3].
--   cmax = 3, so interior = dropN 3 CC = [V3] (V3 is the one KEPT var, slot 0).
--   index 1 is BLOCKED: shallower than cmax but not itself concealed.
CC : TCtx
CC = rvld `ℕ ∷ rvld `ℕ ∷ rvld `ℕ ∷ rvld `ℕ ∷ []

Θ : BCtx
Θ = cnc 2 `ℕ ∷ cnc 0 `ℕ ∷ []

_ : intOf CC Θ ≡ rvld `ℕ ∷ []        -- interior = [V3]
_ = refl

-- The KEPT var V3 (index 3) correctly maps to interior slot 0:
_ : substᵗ (γᵇ Θ) (` 3) ≡ ` 0
_ = refl

-- The BLOCKED var V1 (index 1) ALSO maps to interior slot 0 — it is silently
-- ALIASED onto the kept var V3.  So B₀ = ` 1 and B₀ = ` 3 get the SAME internal
-- face, even though V1 should be inaccessible under tight control.  This aliasing
-- is permitted by the current (env) rule (nothing forbids B₀ from naming V1), and
-- it is exactly what breaks the renaming commutation γcnc-comm at blocked indices.
_ : substᵗ (γᵇ Θ) (` 1) ≡ ` 0
_ = refl
