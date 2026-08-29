module alt.probes.RepExchangeReopenCounterexample where

-- File Charter:
--   * Checks the missing geometry in the proposed general `rep?-exchange`:
--     an outer begin reopens the old anchor whose crossing was just ended.
--   * All concealment and lookup premises hold, but the left young ν follows
--     the reopened live alias while the right concealed representation stays
--     at the resolved type.
--   * The unequal lookup results are checked by normalization; this refutes
--     exchange over unrestricted telescope extensions.

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Data.Vec.Base as Vec

open import Types
open import alt.ThetaTyping
open import alt.ThetaRepExchange

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

no-live-empty : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-empty ()

base : TyEnv 1 zero Vec.[]
base = ∅ ,:= ℕᵗ

crossed-map : Vec.Vec (Maybe (TyVar 1)) 1
crossed-map = just zero Vec.∷ Vec.[]

crossed : TyEnv 1 1 crossed-map
crossed = base ,begin[ zero ≔ zero ]⟨ no-live-empty ⟩

lookup-premise :
  Vec.lookup crossed-map (zero {n = 0}) ≡ just (zero {n = 0})
lookup-premise = refl

representation-premise : rep? (crossed ,end[ zero ]) zero ≡ just ℕᵗ
representation-premise = refl

concealment-premise :
  concealRep? (zero {n = 0}) (ℕᵗ {Δ = 0}) (＇ (zero {n = 0}))
  ≡ just ℕᵗ
concealment-premise = refl

swapped-left : TyEnv 2 zero Vec.[]
swapped-left = (crossed ,:= ＇ zero) ,end[ zero ]

swapped-right : TyEnv 2 zero Vec.[]
swapped-right = (crossed ,end[ zero ]) ,:= ℕᵗ

-- The ended anchor `zero` of `crossed` is `suc zero` after the new ν.
reopened-left : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
reopened-left =
  swapped-left ,begin[ zero ≔ suc zero ]⟨ no-live-empty ⟩

reopened-right : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
reopened-right =
  swapped-right ,begin[ zero ≔ suc zero ]⟨ no-live-empty ⟩

left-young-result : rep? reopened-left zero ≡ just (＇ zero)
left-young-result = refl

right-young-result : rep? reopened-right zero ≡ just ℕᵗ
right-young-result = refl

reopened-breaks-exchange : rep? reopened-left zero ≢ rep? reopened-right zero
reopened-breaks-exchange ()
