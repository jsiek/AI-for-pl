module proof.InterpreterFramedNameInstantiationProof where

-- File Charter:
--   * Lifts abstract-name substitution to exact runtime-framed values.
--   * Changes only the source type environment from the abstract head to the
--     allocated seal head and preserves the target environment.
--   * Contains no interpreter call, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (framed-value-operational)
open import Runtime.InterpreterOperationalNameInstantiation
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing using (TypedValueNarrowing)
open import Narrowing.InterpreterWorldNarrowing using (Allocated)
import NuTermImprecision as NTI
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds


left-name-instantiated-framed :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′ X α V V′ L}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {abstract-runtime :
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ
        (abstract-name X ∷ θ) θ′}
    {seal-runtime :
      RuntimeNarrowing S Φ Δᴸ Δᴿ ρ
        (seal-name α ∷ θ) θ′} →
  TypedValueNarrowing
    ⟦ A ⟧[ seal-name α ∷ θ ]
    ⟦ A′ ⟧[ θ′ ] S L V′ →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  Allocated U α →
  substituteName X α V ≡ L →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p}
    abstract-runtime V V′ →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p}
    seal-runtime L V′
left-name-instantiated-framed typed R≤S α-ok result-eq value =
  left-name-instantiated-value
    typed operational R≤S α-ok result-eq value
  where
  operational =
    left-name-instantiated-operational
      typed R≤S α-ok result-eq
      (framed-value-operational value)
