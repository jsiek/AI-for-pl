module strong-rep-nu.Compile where

-- File Charter:
--   * THE ELABORATION of the source language (strong-rep-nu.Source)
--     into the run-time language: `compile` is structural except at
--     type application, which becomes `ν`, carrying the conversion
--     `reveal 0 C` that `TyBeta` used to mint at run time.
--   * `compile` is defined on TYPING DERIVATIONS, because `reveal`
--     needs the body `C` of the operator's type `∀ C`.

open import Data.Nat using (ℕ)
open import Data.List using ([])

open import strong-rep-nu.Types
open import strong-rep-nu.Conversion using (reveal)
open import strong-rep-nu.Terms
open import strong-rep-nu.Source

compile : ∀ {n Γ M A} → n ∣ Γ ⊢ˢ M ⦂ A → Term
compile (⊢ˢ` {x = x} _)        = ` x
compile (⊢ˢ$ {k = k})          = $ k
compile ⊢ˢtrue                 = `true
compile ⊢ˢfalse                = `false
compile (⊢ˢƛ {A = A} _ d)      = ƛ A ∙ compile d
compile (⊢ˢ· d e)              = compile d · compile e
compile (⊢ˢΛ _ d)              = Λ compile d
compile (⊢ˢ[] {A = A} {C = C} d _) = ν A · compile d ⟨ reveal 0 C ⟩

-- source values compile to run-time values
compile-value : ∀ {n Γ M A} (d : n ∣ Γ ⊢ˢ M ⦂ A)
  → SValue M → Value (compile d)
compile-value ⊢ˢ$ SV-$ = V-simple S-$
compile-value ⊢ˢtrue SV-true = V-simple S-true
compile-value ⊢ˢfalse SV-false = V-simple S-false
compile-value (⊢ˢƛ _ d) SV-ƛ = V-simple S-ƛ
compile-value (⊢ˢΛ _ d) (SV-Λ v) = V-simple (S-Λ (compile-value d v))
