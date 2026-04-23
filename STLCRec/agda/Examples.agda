module Examples where

-- File Charter:
--   * Representative typed/reduction examples for STLCRec.
--   * Includes a minimal recursive function example using `μ`.

open import STLCRec
open import Agda.Builtin.List using ([])

idNat : Term
idNat = ƛ nat ⇒ ` 0

idNat-⊢ : [] ⊢ idNat ⦂ (nat ⇒ nat)
idNat-⊢ = ⊢ƛ (⊢` Z)

idRec : Term
idRec = μ (nat ⇒ nat) ⇒ (ƛ nat ⇒ ` 0)

idRec-⊢ : [] ⊢ idRec ⦂ (nat ⇒ nat)
idRec-⊢ = ⊢μ (ƛ nat ⇒ ` 0) (⊢ƛ (⊢` Z))

idRec-zero : Term
idRec-zero = idRec · `zero

idRec-zero-⊢ : [] ⊢ idRec-zero ⦂ nat
idRec-zero-⊢ = ⊢· idRec-⊢ ⊢zero

idRec-zero-↠ : idRec-zero —↠ `zero
idRec-zero-↠ =
  (idRec · `zero)
    —→⟨ β-μ `zero ⟩
  ((ƛ nat ⇒ ` 0) · `zero)
    —→⟨ β-ƛ `zero ⟩
  `zero
    ∎
