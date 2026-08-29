module alt.probes.U49PocketStrengthensCounterexample where

-- File Charter:
--   * Checks the U49 `pocket-strengthens` statement at a concealed live
--     crossing.  The young ν representation repoints through the ended
--     crossing to its older anchor, so a typed pocket term can still mention
--     the young anchor and is not a `shiftᶿ` image.

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Nat using (zero)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst using (rep?-bracket; rep?-here)

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

ℕ⇒ℕ : ∀ {Δ} → Ty Δ
ℕ⇒ℕ = ℕᵗ ⇒ ℕᵗ

no-live-anchor : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-anchor ()

baseEnv : TyEnv 1 zero Vec.[]
baseEnv = ∅ ,:= ℕ⇒ℕ

crossedEnv : TyEnv 1 1 (just zero Vec.∷ Vec.[])
crossedEnv = baseEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

pocketEnv : TyEnv 2 zero Vec.[]
pocketEnv = crossedEnv ,:= ＇ zero ,end[ zero ]

young-rep-survives : rep? pocketEnv zero ≡ just ℕ⇒ℕ
young-rep-survives = refl

pocketBody : Term 2 1
pocketBody = ƛ ℕᵗ ˙ ` zero

pocketTerm : Term 2 zero
pocketTerm = pocketBody ↑[ zero ≔ zero ] δ↑ (ℕ⇒ℕ {Δ = 1})

pocketBody-typed :
  pocketEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩
    ∣ [] ⊢ pocketBody ⦂ ℕ⇒ℕ
pocketBody-typed = ⊢ƛ (⊢` Z)

pocketTerm-typed : pocketEnv ∣ [] ⊢ pocketTerm ⦂ ℕ⇒ℕ
pocketTerm-typed =
  ⊢reveal young-rep-survives
    (delimiter-typed↑ zero (ℕ⇒ℕ {Δ = 1}) (ℕ⇒ℕ {Δ = 1}))
    pocketBody-typed

pocketTerm-not-shifted : ∀ (W₀ : Term 1 zero)
  → pocketTerm ≢ shiftᶿ W₀
pocketTerm-not-shifted (` x) ()
pocketTerm-not-shifted (ƛ A ˙ M) ()
pocketTerm-not-shifted (L · M) ()
pocketTerm-not-shifted (Λ M) ()
pocketTerm-not-shifted (L ⦂∀ C [ A ]) ()
pocketTerm-not-shifted ($ κ) ()
pocketTerm-not-shifted (L ⊕[ op ] M) ()
pocketTerm-not-shifted (M ⟨ c ⟩) ()
pocketTerm-not-shifted (M ↑[ X ≔ α ] c) ()
pocketTerm-not-shifted (ν[ A ] M) ()
pocketTerm-not-shifted blame ()

pocket-strengthens-refuted :
  ((zero {n = 0}) ∈ᵗ (＇ (zero {n = 0})) →
   crossedEnv ,:= ＇ zero ,end[ zero ] ∣ []
     ⊢ pocketTerm ⦂ ℕ⇒ℕ →
   Σ[ W₀ ∈ Term 1 zero ] pocketTerm ≡ shiftᶿ W₀)
  → ⊥
pocket-strengthens-refuted proposed
    with proposed var-∈ pocketTerm-typed
pocket-strengthens-refuted proposed | W₀ , term-eq =
  pocketTerm-not-shifted W₀ term-eq
