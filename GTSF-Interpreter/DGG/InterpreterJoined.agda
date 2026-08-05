module DGG.InterpreterJoined where

-- File Charter:
--   * Defines the final joined-world/value certificate for the interpreter.
--   * Exports semantic value narrowing while hiding the concrete world
--     relation witness existentially.
--   * Shows that joined values are scoped by their related final worlds.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)

open import Interpreter
import Narrowing.InterpreterEnvironmentNarrowing as EnvironmentProperties
open import Runtime.InterpreterValueSubstitutionShape using
  (substitute-name-sealed-source)
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties
open import Types

module Joined
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  module Environments =
    EnvironmentProperties.EnvironmentNarrowing leaves

  module WorldProof =
    WorldProperties.WorldNarrowingProperties (TypeNarrowing leaves)

  SemanticValueNarrowing :
    World → Value → World → Value → Set₁
  SemanticValueNarrowing W V W′ V′ =
    Σ[ R ∈ WorldRelation W W′ ] ValueNarrowing R V V′

  record Joined
      (W : World) (V : Value)
      (W′ : World) (V′ : Value) : Set₁ where
    constructor joined
    field
      semantic-values-narrow :
        SemanticValueNarrowing W V W′ V′

  open Joined public

  joined-values-scoped :
    ∀ {W V W′ V′} →
    Joined W V W′ V′ →
    ValueScoped W V × ValueScoped W′ V′
  joined-values-scoped (joined (R , V~V′)) =
    Environments.value-narrowing-scoped V~V′

  value-seals-linked :
    ∀ {W W′ α α′ V V′} {R : WorldRelation W W′} →
    ValueNarrowing R (sealed α V) (sealed α′ V′) →
    SealLink R α α′
  value-seals-linked (sealed⊑ α~α′ V~V′) =
    α~α′
  value-seals-linked
      (left-dynamic-sealed⊑ dynamic () V~V′)
  value-seals-linked
      (quotient-value-frame⊑
        frame left-scoped right-scoped base-narrowing) =
    QuotientValueFrameSealLink leaves frame
  value-seals-linked {α = source}
      (left-name-instantiated⊑
        {X = X} {α = fresh} {V = V}
        R≤S α-ok result-eq base-narrowing)
      with substitute-name-sealed-source X fresh V result-eq
  value-seals-linked {α = source}
      (left-name-instantiated⊑
        {X = X} {α = fresh} {V = .(sealed source Q)}
        R≤S α-ok result-eq base-narrowing)
      | Q , refl =
    WorldProof.seal-link-weaken R≤S
      (value-seals-linked base-narrowing)

  joined-seals-linked :
    ∀ {W W′ α α′ V V′} →
    Joined W (sealed α V) W′ (sealed α′ V′) →
    Σ[ R ∈ WorldRelation W W′ ] SealLink R α α′
  joined-seals-linked (joined (R , V~V′)) =
    R , value-seals-linked V~V′

  joined-seals-respect-allocations :
    ∀ {W W′ α α′ V V′} →
    Joined W (sealed α V) W′ (sealed α′ V′) →
    Σ[ R ∈ WorldRelation W W′ ]
    Σ[ A ∈ Ty ]
    Σ[ θ ∈ TypeEnvironment ]
    Σ[ A′ ∈ Ty ]
    Σ[ θ′ ∈ TypeEnvironment ]
      allocation α A θ ∈ allocations W ×
      allocation α′ A′ θ′ ∈ allocations W′ ×
      TypeNarrowing leaves A A′ ×
      TypeEnvironmentNarrowing R θ θ′
  joined-seals-respect-allocations
      (joined (R , V~V′))
      with WorldProof.seal-link-respects-allocations
        (value-seals-linked V~V′)
  joined-seals-respect-allocations
      (joined (R , V~V′))
      | A , θ , A′ , θ′ , α∈W , α′∈W′ , A~A′ , θ~θ′ =
    R , A , θ , A′ , θ′ ,
    α∈W , α′∈W′ , A~A′ , θ~θ′
