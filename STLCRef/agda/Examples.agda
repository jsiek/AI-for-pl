module Examples where

-- File Charter:
--   * Closed STLCRef examples inspired by TAPL Chapter 13 (References).
--   * Each example includes a typing derivation and a checked evaluation outcome.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (∃; ∃-syntax; _,_)

open import STLCRef
open import Eval using (eval)

------------------------------------------------------------------------
-- Shared helpers
------------------------------------------------------------------------

gas : ℕ
gas = 120

final-config :
  ∀ {c : Config} ->
  Maybe (∃[ c′ ] (c —↠ c′)) ->
  Maybe Config
final-config (just (c′ , c—↠c′)) = just c′
final-config nothing = nothing

numeral : ℕ -> Term
numeral zeroℕ = `zero
numeral (sucℕ n) = `suc (numeral n)

⊢numeral :
  ∀ {Γ Σ} (n : ℕ) ->
  Γ ∣ Σ ⊢ numeral n ⦂ nat
⊢numeral zeroℕ = ⊢zero
⊢numeral (sucℕ n) = ⊢suc (⊢numeral n)

fiveℕ : ℕ
fiveℕ = sucℕ (sucℕ (sucℕ (sucℕ (sucℕ zeroℕ))))

sevenℕ : ℕ
sevenℕ = sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ (sucℕ zeroℕ))))))

five : Term
five = numeral fiveℕ

six : Term
six = `suc five

seven : Term
seven = numeral sevenℕ

------------------------------------------------------------------------
-- TAPL Chapter 13 examples
------------------------------------------------------------------------

-- TAPL §13.1 Basics: `r = ref 5`.
tapl-ref5 : Term
tapl-ref5 = ref five

tapl-ref5-⊢ : [] ∣ [] ⊢ tapl-ref5 ⦂ ref nat
tapl-ref5-⊢ = ⊢ref (⊢numeral fiveℕ)

tapl-ref5-eval :
  final-config (eval gas (tapl-ref5 , [])) ≡ just (`loc zeroℕ , five ∷ [])
tapl-ref5-eval = refl

-- TAPL §13.1 Basics: `!r` after allocating `r = ref 5`.
tapl-read5 : Term
tapl-read5 = (ƛ ref nat ⇒ ! (` 0)) · (ref five)

tapl-read5-⊢ : [] ∣ [] ⊢ tapl-read5 ⦂ nat
tapl-read5-⊢ = ⊢· (⊢ƛ (⊢! (⊢` Z))) (⊢ref (⊢numeral fiveℕ))

tapl-read5-eval :
  final-config (eval gas (tapl-read5 , [])) ≡ just (five , five ∷ [])
tapl-read5-eval = refl

-- TAPL §13.1 Basics + sequencing: `r := 7; !r`.
tapl-assign7-then-read : Term
tapl-assign7-then-read =
  (ƛ ref nat ⇒ ((ƛ unit ⇒ ! (` 1)) · (` 0 := seven))) · (ref five)

tapl-assign7-then-read-⊢ : [] ∣ [] ⊢ tapl-assign7-then-read ⦂ nat
tapl-assign7-then-read-⊢ =
  ⊢·
    (⊢ƛ
      (⊢·
        (⊢ƛ (⊢! (⊢` (S Z))))
        (⊢:= (⊢` Z) (⊢numeral sevenℕ))))
    (⊢ref (⊢numeral fiveℕ))

tapl-assign7-then-read-eval :
  final-config (eval gas (tapl-assign7-then-read , [])) ≡ just (seven , seven ∷ [])
tapl-assign7-then-read-eval = refl

-- TAPL §13.1 Side effects: `(r:=succ(!r); !r)` encoded via sequencing.
tapl-inc-then-read : Term
tapl-inc-then-read =
  (ƛ ref nat ⇒ ((ƛ unit ⇒ ! (` 1)) · (` 0 := `suc (! (` 0))))) · (ref five)

tapl-inc-then-read-⊢ : [] ∣ [] ⊢ tapl-inc-then-read ⦂ nat
tapl-inc-then-read-⊢ =
  ⊢·
    (⊢ƛ
      (⊢·
        (⊢ƛ (⊢! (⊢` (S Z))))
        (⊢:= (⊢` Z) (⊢suc (⊢! (⊢` Z))))))
    (⊢ref (⊢numeral fiveℕ))

tapl-inc-then-read-eval :
  final-config (eval gas (tapl-inc-then-read , [])) ≡ just (six , six ∷ [])
tapl-inc-then-read-eval = refl
