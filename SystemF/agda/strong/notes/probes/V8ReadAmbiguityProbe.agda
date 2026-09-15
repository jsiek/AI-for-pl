module strong.notes.probes.V8ReadAmbiguityProbe where

-- PROBE (2026-09-15): the read-back relation is AMBIGUOUS on a context
-- that assigns two names to one address.  This is why
-- `preserve-step`'s cancelling case needs a context well-formedness
-- invariant: a `seal` and the `unseal` that cancels it read the SAME
-- representation at the SAME context, and their types agree only if
-- that read is single-valued.  The notes' `ok` already forbids such a
-- context (`Γ ∌ _:=α` on `Γ,X:=α`); the open question is where v8
-- should enforce it.
open import Data.Nat using (zero; suc)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx

-- Two names for ONE address: the context the notes' `ok` forbids.
Γbad : Ctxᵗ
Γbad = asgn (lvl 0) ∷ asgn (lvl 0) ∷ []

n₀ : Γbad ∋n 0 := lvl 0
n₀ = n-here-asgn

n₁ : Γbad ∋n 1 := lvl 0
n₁ = n-skip-asgn n-here-asgn

-- so the SAME representation reads back two ways
read₀ : [] ∣ Γbad ⊢ `ᵃ (lvl 0) ⇓ ` 0
read₀ = read-var n₀

read₁ : [] ∣ Γbad ⊢ `ᵃ (lvl 0) ⇓ ` 1
read₁ = read-var n₁
