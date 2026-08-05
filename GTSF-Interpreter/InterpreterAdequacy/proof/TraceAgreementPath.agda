module InterpreterAdequacy.proof.TraceAgreementPath where

-- File Charter:
--   * Reindexes trace agreements across arbitrary `keep`/`bind` paths.
--   * Separates proof re-basing from the syntactic renaming caused by fresh
--     seals, then lifts the operation to terms, values, and environments.
--   * Contains no interpreter recursion and constructs no reduction step.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import Interpreter using
  (Environment; Name; Value; allocation; world)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.TraceAgreementBind
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (world-trace-agreement-++)
open import NuReduction using
  (StoreChanges; keep; bind; applyTerms)
import NuTerms as N
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-compose; renameᵗᵐ-preserves-No•)
open import proof.Substitution.Term.TermSubstitutionSyntax using
  (substˣᵐ-renameᵗᵐ)

------------------------------------------------------------------------
-- The action of a trace below enclosing syntactic type abstractions
------------------------------------------------------------------------

apply-value-changes : List Name → StoreChanges → N.Term → N.Term
apply-value-changes Ξ [] v = v
apply-value-changes Ξ (keep ∷ χs) v =
  apply-value-changes Ξ χs v
apply-value-changes Ξ (bind A ∷ χs) v =
  apply-value-changes Ξ χs (N.renameᵗᵐ (insert-seal-renaming Ξ) v)

apply-environment-changes :
  List Name → StoreChanges → List N.Term → List N.Term
apply-environment-changes Ξ [] vs = vs
apply-environment-changes Ξ (keep ∷ χs) vs =
  apply-environment-changes Ξ χs vs
apply-environment-changes Ξ (bind A ∷ χs) vs =
  apply-environment-changes Ξ χs
    (rename-environment (insert-seal-renaming Ξ) vs)

apply-value-changes-empty :
  ∀ χs M → apply-value-changes [] χs M ≡ applyTerms χs M
apply-value-changes-empty [] M = refl
apply-value-changes-empty (keep ∷ χs) M =
  apply-value-changes-empty χs M
apply-value-changes-empty (bind A ∷ χs) M =
  apply-value-changes-empty χs (N.renameᵗᵐ suc M)

------------------------------------------------------------------------
-- Agreement proof irrelevance with respect to the trace witness
------------------------------------------------------------------------

type-environment-trace-rebase :
  ∀ {W χs χs′}
    {old-agreement : WorldTraceAgreement W χs}
    {new-agreement : WorldTraceAgreement W χs′}
    {Ξ θ τ} →
  TypeEnvironmentTraceAgreement old-agreement Ξ θ τ →
  TypeEnvironmentTraceAgreement new-agreement Ξ θ τ
type-environment-trace-rebase
    (type-environment-trace-agreement lookup-agrees) =
  type-environment-trace-agreement lookup-agrees

mutual
  value-trace-rebase :
    ∀ {W χs χs′}
      {old-agreement : WorldTraceAgreement W χs}
      {new-agreement : WorldTraceAgreement W χs′}
      {Ξ V v} →
    ValueTraceAgreement old-agreement Ξ V v →
    ValueTraceAgreement new-agreement Ξ V v
  value-trace-rebase
      (closure-trace-agrees
        θ-agrees γ-agrees no-raw reification no-body-bullet) =
    closure-trace-agrees
      (type-environment-trace-rebase θ-agrees)
      (environment-trace-rebase γ-agrees)
      no-raw reification no-body-bullet
  value-trace-rebase constant-trace-agrees =
    constant-trace-agrees
  value-trace-rebase (tagged-trace-agrees θ-agrees V-agrees) =
    tagged-trace-agrees
      (type-environment-trace-rebase θ-agrees)
      (value-trace-rebase V-agrees)
  value-trace-rebase (sealed-trace-agrees name-eq V-agrees) =
    sealed-trace-agrees name-eq (value-trace-rebase V-agrees)
  value-trace-rebase
      (function-proxy-trace-agrees θ-agrees V-agrees) =
    function-proxy-trace-agrees
      (type-environment-trace-rebase θ-agrees)
      (value-trace-rebase V-agrees)
  value-trace-rebase
      (type-abstraction-trace-agrees
        fresh graph θ-agrees γ-agrees no-raw reification vP no-P) =
    type-abstraction-trace-agrees fresh graph
      (type-environment-trace-rebase θ-agrees)
      (environment-trace-rebase γ-agrees)
      no-raw reification vP no-P
  value-trace-rebase (forall-proxy-trace-agrees θ-agrees V-agrees) =
    forall-proxy-trace-agrees
      (type-environment-trace-rebase θ-agrees)
      (value-trace-rebase V-agrees)
  value-trace-rebase (generalized-trace-agrees θ-agrees V-agrees) =
    generalized-trace-agrees
      (type-environment-trace-rebase θ-agrees)
      (value-trace-rebase V-agrees)

  environment-trace-rebase :
    ∀ {W χs χs′}
      {old-agreement : WorldTraceAgreement W χs}
      {new-agreement : WorldTraceAgreement W χs′}
      {Ξ γ vs} →
    EnvironmentTraceAgreement old-agreement Ξ γ vs →
    EnvironmentTraceAgreement new-agreement Ξ γ vs
  environment-trace-rebase environment-empty-trace-agrees =
    environment-empty-trace-agrees
  environment-trace-rebase
      (environment-cons-trace-agrees V-agrees γ-agrees) =
    environment-cons-trace-agrees
      (value-trace-rebase V-agrees)
      (environment-trace-rebase γ-agrees)

term-trace-rebase :
  ∀ {W χs χs′}
    {old-agreement : WorldTraceAgreement W χs}
    {new-agreement : WorldTraceAgreement W χs′}
    {Ξ γ θ M P} →
  TermTraceAgreement old-agreement Ξ γ θ M P →
  TermTraceAgreement new-agreement Ξ γ θ M P
term-trace-rebase
    (term-trace-agreement τ vs θ-agrees γ-agrees reification) =
  term-trace-agreement τ vs
    (type-environment-trace-rebase θ-agrees)
    (environment-trace-rebase γ-agrees)
    reification

------------------------------------------------------------------------
-- One binding and an arbitrary path
------------------------------------------------------------------------

term-trace-bind :
  ∀ {next cells χs A B allocation-θ}
    {old-agreement : WorldTraceAgreement (world next cells) χs}
    {new-agreement :
      WorldTraceAgreement
        (world (Data.Nat.suc next)
          (allocation (Interpreter.seal-name-id next) A
            allocation-θ ∷ cells))
        (χs ++ bind B ∷ [])}
    {Ξ γ θ M P} →
  TermTraceAgreement old-agreement Ξ γ θ M P →
  TermTraceAgreement new-agreement Ξ γ θ M
    (N.renameᵗᵐ (insert-seal-renaming Ξ) P)
term-trace-bind {Ξ = Ξ} {M = M}
    (term-trace-agreement τ vs θ-agrees γ-agrees reification) =
  term-trace-agreement
    (λ X → insert-seal-renaming Ξ (τ X))
    (rename-environment (insert-seal-renaming Ξ) vs)
    (type-environment-trace-bind θ-agrees)
    (environment-trace-bind γ-agrees)
    (trans
      (cong (N.renameᵗᵐ (insert-seal-renaming Ξ)) reification)
      (trans
        (sym
          (substˣᵐ-renameᵗᵐ
            (insert-seal-renaming Ξ)
            (environmentSubstitution
              (rename-environment (insert-seal-renaming Ξ) vs))
            (environmentSubstitution vs)
            (N.renameᵗᵐ τ M)
            (environment-substitution-rename
              (insert-seal-renaming Ξ) vs)))
        (cong
          (N.substˣᵐ
            (environmentSubstitution
              (rename-environment (insert-seal-renaming Ξ) vs)))
          (renameᵗᵐ-compose τ (insert-seal-renaming Ξ) M))))

mutual
  value-trace-path :
    ∀ {W U χs χs′}
      (old-agreement : WorldTraceAgreement W χs)
      (path : WorldTracePath W χs′ U)
      {Ξ V v} →
    ValueTraceAgreement old-agreement Ξ V v →
    ValueTraceAgreement (world-trace-agreement-++ old-agreement path) Ξ V
      (apply-value-changes Ξ χs′ v)
  value-trace-path old-agreement world-trace-done V-agrees =
    value-trace-rebase V-agrees
  value-trace-path old-agreement (world-trace-keep path) V-agrees =
    value-trace-rebase
      (value-trace-path old-agreement path V-agrees)
  value-trace-path old-agreement
      (world-trace-bind
        {next = next} {cells = cells} {A = A} {B = B} {θ = θ}
        θ-agrees type-eq path)
      V-agrees =
    value-trace-rebase
      (value-trace-path bind-agreement path
        (value-trace-bind {new-agreement = bind-agreement} V-agrees))
    where
    bind-path :
      WorldTracePath
        (world next cells) (bind B ∷ [])
        (world (Data.Nat.suc next)
          (allocation (Interpreter.seal-name-id next) A θ ∷ cells))
    bind-path =
      world-trace-bind θ-agrees type-eq world-trace-done

    bind-agreement :
      WorldTraceAgreement
        (world (Data.Nat.suc next)
          (allocation (Interpreter.seal-name-id next) A θ ∷ cells))
        (_ ++ bind B ∷ [])
    bind-agreement = world-trace-agreement-++ old-agreement bind-path

  environment-trace-path :
    ∀ {W U χs χs′}
      (old-agreement : WorldTraceAgreement W χs)
      (path : WorldTracePath W χs′ U)
      {Ξ γ vs} →
    EnvironmentTraceAgreement old-agreement Ξ γ vs →
    EnvironmentTraceAgreement
      (world-trace-agreement-++ old-agreement path) Ξ γ
      (apply-environment-changes Ξ χs′ vs)
  environment-trace-path old-agreement world-trace-done γ-agrees =
    environment-trace-rebase γ-agrees
  environment-trace-path old-agreement (world-trace-keep path) γ-agrees =
    environment-trace-rebase
      (environment-trace-path old-agreement path γ-agrees)
  environment-trace-path old-agreement
      (world-trace-bind
        {next = next} {cells = cells} {A = A} {B = B} {θ = θ}
        θ-agrees type-eq path)
      γ-agrees =
    environment-trace-rebase
      (environment-trace-path bind-agreement path
        (environment-trace-bind
          {new-agreement = bind-agreement} γ-agrees))
    where
    bind-path :
      WorldTracePath
        (world next cells) (bind B ∷ [])
        (world (Data.Nat.suc next)
          (allocation (Interpreter.seal-name-id next) A θ ∷ cells))
    bind-path =
      world-trace-bind θ-agrees type-eq world-trace-done

    bind-agreement :
      WorldTraceAgreement
        (world (Data.Nat.suc next)
          (allocation (Interpreter.seal-name-id next) A θ ∷ cells))
        (_ ++ bind B ∷ [])
    bind-agreement = world-trace-agreement-++ old-agreement bind-path

term-trace-path :
  ∀ {W U χs χs′}
    (old-agreement : WorldTraceAgreement W χs)
    (path : WorldTracePath W χs′ U)
    {Ξ γ θ M P} →
  TermTraceAgreement old-agreement Ξ γ θ M P →
  TermTraceAgreement (world-trace-agreement-++ old-agreement path)
    Ξ γ θ M (apply-value-changes Ξ χs′ P)
term-trace-path old-agreement world-trace-done M-agrees =
  term-trace-rebase M-agrees
term-trace-path old-agreement (world-trace-keep path) M-agrees =
  term-trace-rebase (term-trace-path old-agreement path M-agrees)
term-trace-path old-agreement
    (world-trace-bind
      {next = next} {cells = cells} {A = A} {B = B} {θ = θ}
      θ-agrees type-eq path)
    M-agrees =
  term-trace-rebase
    (term-trace-path bind-agreement path
      (term-trace-bind {new-agreement = bind-agreement} M-agrees))
  where
  bind-path :
    WorldTracePath
      (world next cells) (bind B ∷ [])
      (world (Data.Nat.suc next)
        (allocation (Interpreter.seal-name-id next) A θ ∷ cells))
  bind-path =
    world-trace-bind θ-agrees type-eq world-trace-done

  bind-agreement :
    WorldTraceAgreement
      (world (Data.Nat.suc next)
        (allocation (Interpreter.seal-name-id next) A θ ∷ cells))
      (_ ++ bind B ∷ [])
  bind-agreement = world-trace-agreement-++ old-agreement bind-path

value-trace-path-empty :
  ∀ {W U χs χs′}
    (old-agreement : WorldTraceAgreement W χs)
    (path : WorldTracePath W χs′ U)
    {V v} →
  ValueTraceAgreement old-agreement [] V v →
  ValueTraceAgreement (world-trace-agreement-++ old-agreement path) [] V
    (NuReduction.applyTerms χs′ v)
value-trace-path-empty {χs′ = χs′}
    old-agreement path {v = v} V-agrees =
  subst
    (ValueTraceAgreement
      (world-trace-agreement-++ old-agreement path) [] _)
    (apply-value-changes-empty χs′ v)
    (value-trace-path old-agreement path V-agrees)

term-trace-path-empty :
  ∀ {W U χs χs′}
    (old-agreement : WorldTraceAgreement W χs)
    (path : WorldTracePath W χs′ U)
    {γ θ M P} →
  TermTraceAgreement old-agreement [] γ θ M P →
  TermTraceAgreement (world-trace-agreement-++ old-agreement path)
    [] γ θ M (NuReduction.applyTerms χs′ P)
term-trace-path-empty {χs′ = χs′}
    old-agreement path {P = P} M-agrees =
  subst
    (TermTraceAgreement
      (world-trace-agreement-++ old-agreement path) [] _ _ _)
    (apply-value-changes-empty χs′ P)
    (term-trace-path old-agreement path M-agrees)
