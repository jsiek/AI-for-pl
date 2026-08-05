module InterpreterAdequacy.TraceAgreement where

-- File Charter:
--   * Relates interpreter worlds, environments, and semantic values to
--     small-step store traces and syntactic values.
--   * Makes the two closing operations explicit: type environments induce
--     type-variable renamings, while value environments induce term
--     substitutions.
--   * Defines relations only.  Adequacy theorems and their proofs belong in
--     subsequent modules in `InterpreterAdequacy`.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)

open import Coercions
  using (renameᶜ)
  renaming
    ( _! to _!ᴬ
    ; seal to sealᴬ
    ; _↦_ to _↦ᴬ_
    ; `∀ to ∀ᴬ
    ; gen to genᴬ
    )
open import Interpreter
  using
    ( Name
    ; SealName
    ; TypeName
    ; abstract-name
    ; seal-name
    ; TypeEnvironment
    ; Value
    ; closure
    ; constant
    ; tagged
    ; sealed
    ; function-proxy
    ; type-abstraction
    ; forall-proxy
    ; generalized
    ; Environment
    ; Allocation
    ; allocation
    ; World
    ; world
    ; allocations
    ; seal-name-id
    ; lookup
    )
open import NuReduction using (StoreChanges; keep; bind)
open import Runtime.InterpreterClosedValue using (ClosedValue)
import NuTerms as N
open import Types using (Renameᵗ; TyVar; renameᵗ)

------------------------------------------------------------------------
-- The final de Bruijn type context represented by an interpreter world
------------------------------------------------------------------------

-- The allocation list and the small-step store use the same order: the most
-- recently allocated seal is de Bruijn index zero.
allocationTypeNames : List Allocation → List TypeName
allocationTypeNames [] = []
allocationTypeNames (allocation α A θ ∷ cells) =
  seal-name α ∷ allocationTypeNames cells

-- `Ξ` is the stack of abstract names introduced by enclosing syntactic
-- type abstractions.  Its head is likewise de Bruijn index zero.
visibleTypeNames : List Name → World → List TypeName
visibleTypeNames Ξ W =
  map abstract-name Ξ ++ allocationTypeNames (allocations W)

-- This internal relation is useful while a trace is still being constructed.
-- It says exactly what a type renaming must do on the entries captured by a
-- semantic value; its behaviour outside the captured environment is
-- intentionally unconstrained.
record TypeEnvironmentWorldAgreement
  (Ξ : List Name)
  (W : World)
  (θ : TypeEnvironment)
  (τ : Renameᵗ)
  : Set where
  constructor type-environment-world-agreement
  field
    type-lookup-agrees :
      ∀ {X : TyVar} {a : TypeName} →
      lookup θ X ≡ just a →
      lookup (visibleTypeNames Ξ W) (τ X) ≡ just a

------------------------------------------------------------------------
-- Interpreter allocation worlds versus small-step store traces
------------------------------------------------------------------------

-- A `keep` step leaves the allocation world unchanged.  A `bind B` step
-- corresponds to the interpreter allocating the next nominal seal.  The
-- equality records that the lexical type `A` stored by the interpreter is
-- seen as the de Bruijn type `B` by small-step reduction.
--
-- The indices below are deliberately in constructor form rather than using
-- `Interpreter.allocate`; this keeps Agda's unifier predictable.
data WorldTracePath : World → StoreChanges → World → Set₁ where
  world-trace-done :
    ∀ {W} →
    WorldTracePath W [] W

  world-trace-keep :
    ∀ {W U χs} →
    WorldTracePath W χs U →
    WorldTracePath W (keep ∷ χs) U

  world-trace-bind :
    ∀ {next cells U χs A B θ τ} →
    TypeEnvironmentWorldAgreement [] (world next cells) θ τ →
    renameᵗ τ A ≡ B →
    WorldTracePath
      (world (suc next)
        (allocation (seal-name-id next) A θ ∷ cells))
      χs U →
    WorldTracePath (world next cells) (bind B ∷ χs) U

record WorldTraceAgreement (W : World) (χs : StoreChanges) : Set₁ where
  constructor world-trace-agreement
  field
    trace-path : WorldTracePath (world zero []) χs W

-- Once the complete trace is known, captured type environments are related to
-- its final world.  Keeping the trace proof as an index prevents a value from
-- silently being compared under an unrelated allocation history.
record TypeEnvironmentTraceAgreement
  {W : World}
  {χs : StoreChanges}
  (world-agreement : WorldTraceAgreement W χs)
  (Ξ : List Name)
  (θ : TypeEnvironment)
  (τ : Renameᵗ)
  : Set where
  constructor type-environment-trace-agreement
  field
    type-trace-lookup-agrees :
      ∀ {X : TyVar} {a : TypeName} →
      lookup θ X ≡ just a →
      lookup (visibleTypeNames Ξ W) (τ X) ≡ just a

------------------------------------------------------------------------
-- Captured term environments as explicit parallel substitutions
------------------------------------------------------------------------

-- A reified environment is ordered like an interpreter environment: its head
-- supplies de Bruijn variable zero.  Variables beyond the environment remain
-- free, with the consumed environment prefix removed from their indices.
environmentSubstitution : List N.Term → N.Substˣ
environmentSubstitution [] x = N.` x
environmentSubstitution (v ∷ vs) zero = v
environmentSubstitution (v ∷ vs) (suc x) =
  environmentSubstitution vs x

-- Semantic values and environments versus final syntactic values
------------------------------------------------------------------------

mutual
  data ValueTraceAgreement
    {W : World}
    {χs : StoreChanges}
    (world-agreement : WorldTraceAgreement W χs)
    (Ξ : List Name)
    : Value → N.Term → Set₁ where

    closure-trace-agrees :
      ∀ {M M′ γ θ τ vs} →
      TypeEnvironmentTraceAgreement world-agreement Ξ θ τ →
      EnvironmentTraceAgreement world-agreement Ξ γ vs →
      N.No• M →
      M′ ≡
        N.substˣᵐ (N.extˢˣ (environmentSubstitution vs))
          (N.renameᵗᵐ τ M) →
      N.No• M′ →
      ValueTraceAgreement world-agreement Ξ
        (closure M γ θ) (N.ƛ M′)

    constant-trace-agrees :
      ∀ {κ} →
      ValueTraceAgreement world-agreement Ξ (constant κ) (N.$ κ)

    tagged-trace-agrees :
      ∀ {G gG θ τ V v} →
      TypeEnvironmentTraceAgreement world-agreement Ξ θ τ →
      ValueTraceAgreement world-agreement Ξ V v →
      ValueTraceAgreement world-agreement Ξ
        (tagged {G} gG θ V) (v N.⟨ renameᶜ τ (G !ᴬ) ⟩)

    sealed-trace-agrees :
      ∀ {α A X V v} →
      lookup (visibleTypeNames Ξ W) X ≡ just (seal-name α) →
      ValueTraceAgreement world-agreement Ξ V v →
      ValueTraceAgreement world-agreement Ξ
        (sealed α V) (v N.⟨ sealᴬ A X ⟩)

    function-proxy-trace-agrees :
      ∀ {p q θ τ V v} →
      TypeEnvironmentTraceAgreement world-agreement Ξ θ τ →
      ValueTraceAgreement world-agreement Ξ V v →
      ValueTraceAgreement world-agreement Ξ
        (function-proxy p q θ V) (v N.⟨ renameᶜ τ (p ↦ᴬ q) ⟩)

    type-abstraction-trace-agrees :
      ∀ {X V P raw γ θ τ vs}
        {vRaw : N.Value raw} →
      abstract-name X ∉ θ →
      ClosedValue γ (abstract-name X ∷ θ) vRaw V →
      TypeEnvironmentTraceAgreement world-agreement Ξ θ τ →
      EnvironmentTraceAgreement world-agreement Ξ γ vs →
      N.No• raw →
      P ≡
        N.substˣᵐ (environmentSubstitution vs)
          (N.renameᵗᵐ τ (N.Λ raw)) →
      N.Value P →
      N.No• P →
      ValueTraceAgreement world-agreement Ξ
        (type-abstraction X V) P

    forall-proxy-trace-agrees :
      ∀ {c θ τ V v} →
      TypeEnvironmentTraceAgreement world-agreement Ξ θ τ →
      ValueTraceAgreement world-agreement Ξ V v →
      ValueTraceAgreement world-agreement Ξ
        (forall-proxy c θ V) (v N.⟨ renameᶜ τ (∀ᴬ c) ⟩)

    generalized-trace-agrees :
      ∀ {A c θ τ V v} →
      TypeEnvironmentTraceAgreement world-agreement Ξ θ τ →
      ValueTraceAgreement world-agreement Ξ V v →
      ValueTraceAgreement world-agreement Ξ
        (generalized A c θ V) (v N.⟨ renameᶜ τ (genᴬ A c) ⟩)

  -- The list `vs` is not an opaque representation artifact: it is precisely
  -- the list consumed by `environmentSubstitution` in the closure clause.
  data EnvironmentTraceAgreement
    {W : World}
    {χs : StoreChanges}
    (world-agreement : WorldTraceAgreement W χs)
    (Ξ : List Name)
    : Environment → List N.Term → Set₁ where

    environment-empty-trace-agrees :
      EnvironmentTraceAgreement world-agreement Ξ [] []

    environment-cons-trace-agrees :
      ∀ {V v γ vs} →
      ValueTraceAgreement world-agreement Ξ V v →
      EnvironmentTraceAgreement world-agreement Ξ γ vs →
      EnvironmentTraceAgreement world-agreement Ξ
        (V ∷ γ) (v ∷ vs)

------------------------------------------------------------------------
-- Interpreter calls versus explicitly reified small-step terms
------------------------------------------------------------------------

-- The direct interpreter keeps a raw body and captured environments, whereas
-- small-step reduction materializes both environments in the term.  The
-- equation is therefore the central entry invariant for both adequacy
-- directions, not an observation derived after evaluation.
record TermTraceAgreement
  {W : World}
  {χs : StoreChanges}
  (world-agreement : WorldTraceAgreement W χs)
  (Ξ : List Name)
  (γ : Environment)
  (θ : TypeEnvironment)
  (M P : N.Term)
  : Set₁ where
  constructor term-trace-agreement
  field
    type-renaming : Renameᵗ
    reified-environment : List N.Term
    type-environment-agrees :
      TypeEnvironmentTraceAgreement
        world-agreement Ξ θ type-renaming
    term-environment-agrees :
      EnvironmentTraceAgreement
        world-agreement Ξ γ reified-environment
    term-reification :
      P ≡
        N.substˣᵐ (environmentSubstitution reified-environment)
          (N.renameᵗᵐ type-renaming M)
