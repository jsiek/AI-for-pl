module LR-narrow.Context.TypedEndpointsFuture where

-- File Charter:
--   * Weakens one typed, closed endpoint pair to a future interpretation.
--   * Reuses only unary closure and semantic-typing weakening.
--   * Contains exactly one exported theorem.

open import Agda.Builtin.Equality using (refl)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter using (Value)
open import LR-narrow.Context.ClosedValueFuture
open import LR-narrow.LogicalRelation using
  (TypedClosedEndpoints; typed-closed-endpoints)
open import LR-narrow.World
import proof.InterpreterSemanticTypingProperties as TypingProof
open import Types using (Ty; TyCtx)

typed-endpoints-future : ∀
    {Φ Δᴸ Δᴿ A A′} {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {current future : World}
    {I : Interpretation {Φ} {Δᴸ} {Δᴿ} current}
    {J : Interpretation {Φ} {Δᴸ} {Δᴿ} future}
    {V V′ : Value}
  → J ⊒ⁱ I
  → TypedClosedEndpoints p I V V′
  → TypedClosedEndpoints p J V V′
typed-endpoints-future {future = future}
    (future-interpretation growth refl refl atoms-eq)
    (typed-closed-endpoints left-closed right-closed
      left-typed right-typed) =
  typed-closed-endpoints
    (closed-value-future (left-future growth) left-closed)
    (closed-value-future (right-future growth) right-closed)
    (TypingProof.value-weaken
      (left-future growth) (left-world-typed future) left-typed)
    (TypingProof.value-weaken
      (right-future growth) (right-world-typed future) right-typed)
