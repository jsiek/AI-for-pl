module proof.InterpreterSealNarrowingProof where

-- File Charter:
--   * Proves paired runtime-seal lookup, construction, and successful checking.
--   * Uses world-link functionality and injectivity to synchronize name tests.
--   * Contains no small-step semantics or reduction-derived result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Nullary using (yes; no)

open import Coercions renaming
  (seal to sealᶜ; unseal to unsealᶜ)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Narrowing.InterpreterEnvironmentNarrowing
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
open import Narrowing.InterpreterWorldNarrowingProperties
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module Environments =
  Narrowing.InterpreterEnvironmentNarrowing.EnvironmentNarrowing
    interpreterNarrowingLeaves

open Environments using
  ( TypeIndexNarrowing
  ; here-both
  ; under-both
  ; under-left
  ; under-right
  )

module WorldProperties =
  WorldNarrowingProperties InterpreterTypeNarrowing

paired-seal-lookup-forward :
  ∀ {W W′ θ θ′ x x′ α}
    {R : WorldRelation W W′}
    (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  TypeIndexNarrowing θ~θ′ x x′ →
  lookup θ x ≡ just (seal-name α) →
  Σ[ α′ ∈ SealName ]
    lookup θ′ x′ ≡ just (seal-name α′) ×
    SealLink R α α′
paired-seal-lookup-forward
    (abstract-name⊑ ∷⊑∷ᵗᵉ θ~θ′) here-both ()
paired-seal-lookup-forward
    (seal-name⊑ α~α′ ∷⊑∷ᵗᵉ θ~θ′) here-both refl =
  _ , refl , α~α′
paired-seal-lookup-forward
    (X~X′ ∷⊑∷ᵗᵉ θ~θ′) (under-both x~x′) left-lookup =
  paired-seal-lookup-forward θ~θ′ x~x′ left-lookup
paired-seal-lookup-forward
    (X-ok ∷ˡ⊑ᵗᵉ θ~θ′) (under-left x~x′) left-lookup =
  paired-seal-lookup-forward θ~θ′ x~x′ left-lookup
paired-seal-lookup-forward
    (X′-ok ∷ʳ⊑ᵗᵉ θ~θ′) (under-right x~x′) left-lookup =
  paired-seal-lookup-forward θ~θ′ x~x′ left-lookup

paired-seal-lookup-backward :
  ∀ {W W′ θ θ′ x x′ α′}
    {R : WorldRelation W W′}
    (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  TypeIndexNarrowing θ~θ′ x x′ →
  lookup θ′ x′ ≡ just (seal-name α′) →
  Σ[ α ∈ SealName ]
    lookup θ x ≡ just (seal-name α) ×
    SealLink R α α′
paired-seal-lookup-backward
    (abstract-name⊑ ∷⊑∷ᵗᵉ θ~θ′) here-both ()
paired-seal-lookup-backward
    (seal-name⊑ α~α′ ∷⊑∷ᵗᵉ θ~θ′) here-both refl =
  _ , refl , α~α′
paired-seal-lookup-backward
    (X~X′ ∷⊑∷ᵗᵉ θ~θ′) (under-both x~x′) right-lookup =
  paired-seal-lookup-backward θ~θ′ x~x′ right-lookup
paired-seal-lookup-backward
    (X-ok ∷ˡ⊑ᵗᵉ θ~θ′) (under-left x~x′) right-lookup =
  paired-seal-lookup-backward θ~θ′ x~x′ right-lookup
paired-seal-lookup-backward
    (X′-ok ∷ʳ⊑ᵗᵉ θ~θ′) (under-right x~x′) right-lookup =
  paired-seal-lookup-backward θ~θ′ x~x′ right-lookup

seal-match-forward :
  ∀ {W W′ expected expected′ actual actual′}
    {R : WorldRelation W W′} →
  SealLink R expected expected′ →
  SealLink R actual actual′ →
  expected ≡ actual →
  expected′ ≡ actual′
seal-match-forward expected~expected′ actual~actual′ refl =
  WorldProperties.seal-link-functional
    expected~expected′ actual~actual′

seal-match-backward :
  ∀ {W W′ expected expected′ actual actual′}
    {R : WorldRelation W W′} →
  SealLink R expected expected′ →
  SealLink R actual actual′ →
  expected′ ≡ actual′ →
  expected ≡ actual
seal-match-backward expected~expected′ actual~actual′ refl =
  WorldProperties.seal-link-injective
    expected~expected′ actual~actual′

target-seal-mismatch-reflects :
  ∀ {W W′ expected expected′ actual actual′}
    {R : WorldRelation W W′} →
  SealLink R expected expected′ →
  SealLink R actual actual′ →
  (expected′ ≡ actual′ → ⊥) →
  expected ≡ actual →
  ⊥
target-seal-mismatch-reflects
    expected~expected′ actual~actual′ expected′≢actual′
    expected≡actual =
  expected′≢actual′
    (seal-match-forward
      expected~expected′ actual~actual′ expected≡actual)

seal-computation-eq :
  ∀ {W θ A x α V} →
  lookup θ x ≡ just (seal-name α) →
  ∀ n →
  coerceValue W θ (sealᶜ A x) V n ≡
  immediateReturn W (sealed α V) n
seal-computation-eq lookup-eq zero =
  refl
seal-computation-eq lookup-eq (suc n)
    rewrite lookup-eq =
  refl

successful-unseal-computation-eq :
  ∀ {W θ x A expected actual V} →
  lookup θ x ≡ just (seal-name expected) →
  expected ≡ actual →
  ∀ n →
  coerceValue W θ (unsealᶜ x A) (sealed actual V) n ≡
  immediateReturn W V n
successful-unseal-computation-eq lookup-eq refl zero =
  refl
successful-unseal-computation-eq
    {expected = expected}
    lookup-eq refl (suc n)
    rewrite lookup-eq
    with expected ≟SealName expected
successful-unseal-computation-eq
    {expected = expected}
    lookup-eq refl (suc n)
    | yes refl =
  refl
successful-unseal-computation-eq
    {expected = expected}
    lookup-eq refl (suc n)
    | no expected≢expected =
  ⊥-elim (expected≢expected refl)

paired-seal-simulation :
  ∀ {W W′ θ θ′ A A′ x x′ α α′ V V′}
    {R : WorldRelation W W′} →
  lookup θ x ≡ just (seal-name α) →
  lookup θ′ x′ ≡ just (seal-name α′) →
  SealLink R α α′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (sealᶜ A x) V)
    (coerceValue W′ θ′ (sealᶜ A′ x′) V′)
paired-seal-simulation left-lookup right-lookup α~α′ V~V′ =
  simulation-pointwise
    (seal-computation-eq left-lookup)
    (seal-computation-eq right-lookup)
    (immediate-return-simulation
      (sealed⊑ α~α′ V~V′))

left-dynamic-seal-simulation :
  ∀ {W W′ θ A x α V V′}
    {R : WorldRelation W W′} →
  lookup θ x ≡ just (seal-name α) →
  LeftDynamicSeal R α →
  NotSealed V′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (sealᶜ A x) V)
    (immediateReturn W′ V′)
left-dynamic-seal-simulation
    lookup-eq dynamic V′-not-sealed V~V′ =
  simulation-pointwise
    (seal-computation-eq lookup-eq)
    (λ n → refl)
    (immediate-return-simulation
      (left-dynamic-sealed⊑
        dynamic V′-not-sealed V~V′))

paired-unseal-simulation :
  ∀ {W W′ θ θ′ x x′ A A′ expected expected′
     actual actual′ V V′}
    {R : WorldRelation W W′} →
  lookup θ x ≡ just (seal-name expected) →
  lookup θ′ x′ ≡ just (seal-name expected′) →
  SealLink R expected expected′ →
  SealLink R actual actual′ →
  expected ≡ actual →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (unsealᶜ x A) (sealed actual V))
    (coerceValue W′ θ′ (unsealᶜ x′ A′) (sealed actual′ V′))
paired-unseal-simulation
    left-lookup right-lookup expected~expected′
    actual~actual′ expected≡actual V~V′ =
  simulation-pointwise
    (successful-unseal-computation-eq
      left-lookup expected≡actual)
    (successful-unseal-computation-eq right-lookup
      (seal-match-forward expected~expected′
        actual~actual′ expected≡actual))
    (immediate-return-simulation V~V′)

left-dynamic-unseal-simulation :
  ∀ {W W′ θ x A expected actual V V′}
    {R : WorldRelation W W′} →
  lookup θ x ≡ just (seal-name expected) →
  LeftDynamicSeal R actual →
  expected ≡ actual →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (unsealᶜ x A) (sealed actual V))
    (immediateReturn W′ V′)
left-dynamic-unseal-simulation
    lookup-eq dynamic expected≡actual V~V′ =
  simulation-pointwise
    (successful-unseal-computation-eq
      lookup-eq expected≡actual)
    (λ n → refl)
    (immediate-return-simulation V~V′)
