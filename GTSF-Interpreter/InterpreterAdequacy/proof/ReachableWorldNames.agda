module InterpreterAdequacy.proof.ReachableWorldNames where

-- File Charter:
--   * Proves that worlds represented by an adequacy trace contain each seal
--     name at a unique de Bruijn position.
--   * Derives the invariant solely from the allocation shape of
--     `WorldTracePath`, independently of typing and reduction metatheory.
--   * Supplies the injectivity fact needed by successful untag and unseal.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (_≤_; zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Relation.Binary.PropositionalEquality using (cong)

open import Interpreter using
  ( Allocation
  ; SealName
  ; TypeName
  ; allocation
  ; lookup
  ; seal-name
  ; seal-name-id
  ; world
  )
open import InterpreterAdequacy.TraceAgreement

data ReachableWorld : Interpreter.World → Set₁ where
  reachable-empty : ReachableWorld (world zero [])
  reachable-allocate :
    ∀ {next cells A θ} →
    ReachableWorld (world next cells) →
    ReachableWorld
      (world (suc next) (allocation (seal-name-id next) A θ ∷ cells))

reachable-world-path :
  ∀ {W U χs} →
  ReachableWorld W →
  WorldTracePath W χs U →
  ReachableWorld U
reachable-world-path reachable world-trace-done = reachable
reachable-world-path reachable (world-trace-keep path) =
  reachable-world-path reachable path
reachable-world-path reachable
    (world-trace-bind θ-agrees type-eq path) =
  reachable-world-path (reachable-allocate reachable) path

world-trace-reachable :
  ∀ {W χs} →
  WorldTraceAgreement W χs →
  ReachableWorld W
world-trace-reachable (world-trace-agreement path) =
  reachable-world-path reachable-empty path

lookup-name-index :
  ∀ {cells i α} →
  lookup (allocationTypeNames cells) i ≡ just (seal-name α) →
  lookup (Data.List.map Interpreter.Allocation.name cells) i ≡ just α
lookup-name-index {cells = []} ()
lookup-name-index {cells = allocation α A θ ∷ cells} {i = zero} refl = refl
lookup-name-index {cells = allocation β A θ ∷ cells} {i = suc i} eq =
  lookup-name-index {cells = cells} eq

reachable-name-below :
  ∀ {next cells i k} →
  ReachableWorld (world next cells) →
  lookup (allocationTypeNames cells) i ≡
    just (seal-name (seal-name-id k)) →
  suc k ≤ next
reachable-name-below reachable-empty ()
reachable-name-below {i = zero} (reachable-allocate reachable) refl =
  ≤-refl
reachable-name-below {i = suc i} (reachable-allocate reachable) eq =
  ≤-trans (reachable-name-below reachable eq) (n≤1+n _)

lookup-allocation-names-injective :
  ∀ {next cells i j a} →
  ReachableWorld (world next cells) →
  lookup (allocationTypeNames cells) i ≡ just a →
  lookup (allocationTypeNames cells) j ≡ just a →
  i ≡ j
lookup-allocation-names-injective reachable-empty () lookup-j
lookup-allocation-names-injective
    {i = zero} {j = zero}
    (reachable-allocate {next = next} reachable) lookup-i lookup-j =
  refl
lookup-allocation-names-injective
    {i = zero} {j = suc j}
    (reachable-allocate {next = next} reachable) refl lookup-j =
  ⊥-elim
    (Data.Nat.Properties.≤⇒≯
      (reachable-name-below reachable lookup-j)
      (Data.Nat.Properties.n<1+n next))
lookup-allocation-names-injective
    {i = suc i} {j = zero}
    (reachable-allocate {next = next} reachable) lookup-i refl =
  ⊥-elim
    (Data.Nat.Properties.≤⇒≯
      (reachable-name-below reachable lookup-i)
      (Data.Nat.Properties.n<1+n next))
lookup-allocation-names-injective
    {i = suc i} {j = suc j}
    (reachable-allocate reachable) lookup-i lookup-j =
  cong suc
    (lookup-allocation-names-injective reachable lookup-i lookup-j)

visible-empty-lookup-injective :
  ∀ {W χs i j a} →
  (world-agreement : WorldTraceAgreement W χs) →
  lookup (visibleTypeNames [] W) i ≡ just a →
  lookup (visibleTypeNames [] W) j ≡ just a →
  i ≡ j
visible-empty-lookup-injective {W = world next cells}
    world-agreement lookup-i lookup-j =
  lookup-allocation-names-injective
    (world-trace-reachable world-agreement) lookup-i lookup-j
