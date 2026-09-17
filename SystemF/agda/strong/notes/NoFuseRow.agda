module strong.notes.NoFuseRow where

-- COULD `hide X α ∷ unseal X α` FUSE?  No — there is nothing for it to
-- fuse TO, and the reason is structural.
--
--   hide X α    Γ₁ → Γ₂        A ⇝ A          (Γ₂ = Γ₁ with X:=α)
--   unseal X α  Γ₂ → Γ₁        ` X′ ⇝ B       (B the read-back of α)
--
-- so the pair is a NET-ZERO context move carrying a REAL type change,
-- `` ` X′ ⇝ B ``.  `fuse` returns a `List ConvElt`, and:
--
--   * `[]` would force the type unchanged — but the target is the
--     read-back, not the variable;
--   * every atomic element MOVES the context by one assignment, so no
--     one of them is net-zero;
--   * `↦` and `all` delegate, and their components would have to carry
--     the same mismatch;
--   * the terminator `id B` is not a `ConvElt` at all, so `fuse` cannot
--     produce it.
--
-- The one thing with the right shape — "change the type, move nothing"
-- — is exactly what the calculus has no element for, and adding one is
-- the change we were trying to avoid.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.RepresentationTypes using (Addr; lvl)
open import strong.Conversion

-- where it stands today
no-row : ∀ X α → fuse (hide X α) (unseal X α) ≡ nothing
no-row X α = refl

-- and the dual order, for the record
no-row′ : ∀ X α → fuse (seal X α) (show X α) ≡ nothing
no-row′ X α = refl
