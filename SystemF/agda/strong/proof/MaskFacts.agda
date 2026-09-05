module strong.proof.MaskFacts where

-- NO BOUNDARY OPERATION CAN TAKE AN OWNER AWAY.
--
-- Masking RETAINS the owner's entry, and an alias RECOVERS it.  In the
-- previous design this is exactly what failed: `entᴳ` wrote `rvl⋆` at the
-- slot (demote-x-always, demote-count-break/n1b/n4), the rebuild carried
-- `abst`, and the crossing value's licence died (¬⊢W-rebuild).
--
-- Also here: the witness for Cancel's residue defect (repair 3a).

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms

mask-retains : ∀ {Δ X Y A} → Δ ∋ X := A
  → (mask Y Δ ∋ X := A) ⊎ (mask Y Δ ∋e X , blk (own A))
mask-retains {X = X} {Y = Y} d with Y ≟ℕ X
... | yes refl = inj₂ (upd-hit blk blk-comm d)
... | no ne    = inj₁ (upd-miss blk blk-comm ne d)

ali-recovers : ∀ {Δ X A} → Δ ∋e X , blk (own A) → unmask X Δ ∋ X := A
ali-recovers d = upd-hit unblk unblk-comm d

-- The round trip is the identity on the spine: a program that hides from
-- itself and then looks again is harmless and typeable.
cnc-then-ali : intC (ali 0 ∷ []) (intC (cnc 0 ∷ []) (own `ℕ ∷ []))
             ≡ own `ℕ ∷ []
cnc-then-ali = refl

------------------------------------------------------------------------
-- Cancel's residue defect (repair 3a), as a refutation
------------------------------------------------------------------------

-- The mini-core's Cancel appended `maskOwns (nrev Θ₂)` to the residue.
-- `scp` applies those masks to Δ, not to the boundary's own owners, so on
-- the mini-core's OWN cancel example the residue is not well formed.  This
-- is why strong.Reduction's CancelR drops it.
¬Bwf-cancel-residue : ¬ Bwf [] (own `ℕ ∷ cnc 0 ∷ [])
¬Bwf-cancel-residue (bw-o _ (bw-c (_ , () , _) _))
