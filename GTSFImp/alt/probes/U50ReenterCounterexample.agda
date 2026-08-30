module alt.probes.U50ReenterCounterexample where

-- File Charter:
--   * Refutes the unchanged-term form of U50's requested re-entry transport.
--   * A term binder born while Y is live is removed by truncateForEnd, but the
--     de Bruijn variable in the transported term is not adjusted.

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.Maybe using (just)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_)
import Data.Vec.Base as Vec

open import Types
open import Consistency
open import alt.ThetaTerms
open import alt.ThetaTyping

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

no-live-empty : ∀ {Θ} {a : TyVar Θ} → a ∉ᵛ Vec.[]
no-live-empty ()

base : TyEnv zero zero Vec.[]
base = ∅

anchor : TyEnv 1 zero Vec.[]
anchor = base ,:= ℕᵗ

live : TyEnv 1 1 (Vec.[ just zero ])
live = anchor ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

closed : TyEnv 1 zero Vec.[]
closed = live ,end[ zero ]

reentered : TyEnv 1 1 (Vec.[ just zero ])
reentered = closed ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

sourceCtx : TermCtx live
sourceCtx = (ℕᵗ at currentScope live) ∷ []

source-typed : live ∣ sourceCtx ⊢ ` zero ⦂ ℕᵗ
source-typed = ⊢` Z

empty-variable-impossible : ∀ {A}
  → reentered ∣ [] ⊢ ` zero ⦂ A
  → ⊥
empty-variable-impossible (⊢` ())

reenter-unchanged-term-refuted :
  (live ∣ sourceCtx ⊢ ` zero ⦂ ℕᵗ)
  × (reentered ∣ beginCtx (truncateForEnd sourceCtx zero)
      ⊢ ` zero ⦂ ℕᵗ
    → ⊥)
reenter-unchanged-term-refuted =
  source-typed , empty-variable-impossible
