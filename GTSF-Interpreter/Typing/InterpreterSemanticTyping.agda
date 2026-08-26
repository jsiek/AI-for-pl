module Typing.InterpreterSemanticTyping where

-- File Charter:
--   * Public semantic-typing interface for the direct interpreter.
--   * Re-exports the semantic judgments and states their lookup,
--     allocation, and world-weakening theorems explicitly.
--   * Delegates proofs to small reduction-free proof modules.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (n≮n)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)

open import Interpreter
open import Runtime.InterpreterClosedValue using (ClosedValue)
open import Typing.InterpreterSemanticTypingCore public
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import Narrowing.InterpreterWorldNarrowing using
  (Allocated; TypeEnvironmentScoped; allocated)
open import Narrowing.InterpreterValueNarrowing using (ValueScoped)
import NuTerms as N
open import Types
import proof.InterpreterCloseValueTyping as CloseProof
import proof.InterpreterSemanticTypingProperties as Proof

type-environment-lookup :
  ∀ {Δ θ X} →
  TypeEnvironmentLength Δ θ →
  X < Δ →
  ∃[ name ] lookup θ X ≡ just name
type-environment-lookup =
  Proof.type-lookup-sound

semantic-type-name-lookup :
  ∀ {θ X name} →
  lookup θ X ≡ just name →
  semanticLookup (semanticEnvironment θ) X ≡ nominal-type name
semantic-type-name-lookup {θ} {X} {name} =
  Proof.semantic-name-lookup {θ = θ} {X = X} {name = name}

term-environment-lookup :
  ∀ {W θ γ Γ x A} →
  EnvironmentTyping W θ γ Γ →
  Γ ∋ x ⦂ A →
  ∃[ V ] (lookup γ x ≡ just V) ×
    ValueTyping W V ⟦ A ⟧[ θ ]
term-environment-lookup =
  Proof.environment-lookup-sound

store-environment-lookup :
  ∀ {W θ Σ X A} →
  StoreTyping W θ Σ →
  (X , A) ∈ Σ →
  ∃[ α ] (lookup θ X ≡ just (seal-name α)) ×
    AllocationRepresentation W α ⟦ A ⟧[ θ ]
store-environment-lookup =
  Proof.store-lookup-sound

allocation-preserves-world-typing :
  ∀ {W Δ Σ θ A} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ →
  WfTy Δ A →
  WorldTyping (allocate W A θ)
allocation-preserves-world-typing =
  allocate-world-typed

fresh-seal-is-unallocated : ∀ {W}
  → WorldTyping W
  → Allocated W (freshSealName W)
  → ⊥
fresh-seal-is-unallocated {W} W⊢ (allocated present) =
  n≮n (next-name W) (Proof.allocation-bound W⊢ present)

fresh-seal-is-allocated : ∀ {W A θ}
  → Allocated (allocate W A θ) (freshSealName W)
fresh-seal-is-allocated =
  Proof.allocated-here

allocation-representation-world-weaken : ∀ {W U α A}
  → WorldExtension W U
  → AllocationRepresentation W α A
  → AllocationRepresentation U α A
allocation-representation-world-weaken =
  Proof.representation-weaken

type-environment-scope-world-weaken : ∀ {W U θ}
  → WorldExtension W U
  → TypeEnvironmentScoped W θ
  → TypeEnvironmentScoped U θ
type-environment-scope-world-weaken =
  Proof.scope-weaken

semantic-value-world-weaken :
  ∀ {W U V A} →
  WorldExtension W U →
  WorldTyping U →
  ValueTyping W V A →
  ValueTyping U V A
semantic-value-world-weaken =
  Proof.value-weaken

semantic-value-scoped :
  ∀ {W V A} →
  ValueTyping W V A →
  ValueScoped W V
semantic-value-scoped =
  Proof.value-typing-scoped

closeValue-preserves-semantic-typing :
  ∀ {W Δ Σ Γ θ γ P A} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ →
  RuntimeTypeEnvironment θ →
  EnvironmentTyping W θ γ Γ →
  InterpreterTerm P →
  (vP : N.Value P) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ P A →
  ∃[ U ] (closeValue vP γ θ ≡ just U) ×
    ValueTyping W U ⟦ A ⟧[ θ ]
closeValue-preserves-semantic-typing =
  CloseProof.closeValue-preserves-semantic-typing

substituteName-closedValue-typing :
  ∀ {W Δ Σ Γ θ θ′ γ P U A X α}
    {vP : N.Value P} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ′ →
  RuntimeTypeEnvironment θ′ →
  EnvironmentTyping W θ′ γ Γ →
  InterpreterTerm P →
  N._∣_∣_⊢_⦂_ Δ Σ Γ P A →
  abstract-name X ∈ θ →
  replaceName X α θ ≡ θ′ →
  ClosedValue γ θ vP U →
  ValueTyping W (substituteName X α U) ⟦ A ⟧[ θ′ ]
substituteName-closedValue-typing =
  CloseProof.substituteName-closedValue-typing
