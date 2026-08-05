module proof.InterpreterDirectionalFramedTypeInstantiation where

-- File Charter:
--   * Proves the paired and source-only type-abstraction leaves of framed
--     `instantiateValue` simulation in all three terminal directions.
--   * Preserves the exact future-allocation certificate at the runtime
--     relation supplied by the enclosing instantiation term.
--   * Contains no recursive call, small-step reduction, or catch-up result.

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using
  (_ˣ⊑★; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing; type-narrowing)
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (framed-value-operational; framed-value-typed)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Typing.InterpreterSemanticTypingCore using (WorldTyping)
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped)
import NuTermImprecision as NTI
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-source
  )
open import proof.InterpreterClosingRuntimeFrame using
  (left-closing-runtime-frame; paired-closing-runtime-frame)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import proof.InterpreterTypeAbstractionInstantiationHelpers using
  (type-abstraction-instantiation-computation)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-type-abstraction-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
    {ρbody :
      NTI.StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
    {θ θ′ A A′ B B′ X X′ V V′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {p⇑ :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {q :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (body-lift :
    NTI.LiftStoreⁱ
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρbody) →
  (instantiate :
    ∀ {U U′ C C′ σ σ′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    (C~C′ : InterpreterTypeNarrowing C C′) →
    (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
    (body-runtime :
      RuntimeNarrowing
        (allocate-both S C~C′ σ~σ′)
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ) ρbody
        (seal-name (freshSealName U) ∷ θ)
        (seal-name (freshSealName U′) ∷ θ′)) →
    FramedValueNarrowing
      {A = B} {A′ = B′} {p = q} body-runtime
      (substituteName X (freshSealName U) V)
      (substituteName X′ (freshSealName U′) V′)) →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  (allocated :
    RuntimeNarrowing
      (allocate-both R (type-narrowing p) θ~θ′)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) p⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′)) →
  FramedValueNarrowing
    {A = `∀ B} {A′ = `∀ B′}
    {p = ImprecisionWf.∀ⁱ q} runtime
    (type-abstraction X V) (type-abstraction X′ V′) →
  ForwardReturnSimulation
    (FramedValueResult
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) p⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′) q)
    (allocate-both R (type-narrowing p) θ~θ′)
    (instantiateValue
      (allocate W A θ) (freshSealName W)
      (type-abstraction X V))
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′)
      (type-abstraction X′ V′))
    index
paired-type-abstraction-forward
    {index = index} {W = W} {W′ = W′} {ρ′ = ρ′}
    {θ = θ} {θ′ = θ′}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {X = X} {X′ = X′} {V = V} {V′ = V′}
    {p = p} {p⇑ = p⇑} {q = q} {R = R}
    runtime body-lift instantiate
    θ~θ′ allocated value =
  forward-return simulation
  where
  body-runtime =
    runtime-narrowing-from-frame
      (left-world-typed allocated)
      (right-world-typed allocated)
      (assumption-membership-unique-matched
        (assumption-membership-unique runtime))
      (paired-closing-runtime-frame
        (runtime-narrowing-frame runtime)
        extension-refl (type-narrowing p) θ~θ′ body-lift)

  body-value =
    instantiate extension-refl (type-narrowing p) θ~θ′ body-runtime

  simulation :
    IndexedTerminalSimulation
      (FramedValueResult
        (NTI.store-matched zero (⇑ᵗ A)
          zero (⇑ᵗ A′) p⇑ ∷ ρ′)
        (seal-name (freshSealName W) ∷ θ)
        (seal-name (freshSealName W′) ∷ θ′) q)
      (allocate-both R (type-narrowing p) θ~θ′)
      (instantiateValue
        (allocate W A θ) (freshSealName W)
        (type-abstraction X V))
      (instantiateValue
        (allocate W′ A′ θ′) (freshSealName W′)
        (type-abstraction X′ V′))
      index zero
  simulation =
    indexed-simulation-pointwise
      type-abstraction-instantiation-computation
      type-abstraction-instantiation-computation
      (terminal-simulation-index
        (immediate-return-simulation
          (framed-result allocated
            (compiler-replanned-value
              (framed-value-typed body-value)
              (framed-value-operational body-value)
              body-value))))

paired-type-abstraction-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
    {ρbody :
      NTI.StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
    {θ θ′ A A′ B B′ X X′ V V′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {p⇑ :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {q :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (body-lift :
    NTI.LiftStoreⁱ
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρbody) →
  (instantiate :
    ∀ {U U′ C C′ σ σ′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    (C~C′ : InterpreterTypeNarrowing C C′) →
    (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
    (body-runtime :
      RuntimeNarrowing
        (allocate-both S C~C′ σ~σ′)
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ) ρbody
        (seal-name (freshSealName U) ∷ θ)
        (seal-name (freshSealName U′) ∷ θ′)) →
    FramedValueNarrowing
      {A = B} {A′ = B′} {p = q} body-runtime
      (substituteName X (freshSealName U) V)
      (substituteName X′ (freshSealName U′) V′)) →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  (allocated :
    RuntimeNarrowing
      (allocate-both R (type-narrowing p) θ~θ′)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) p⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′)) →
  FramedValueNarrowing
    {A = `∀ B} {A′ = `∀ B′}
    {p = ImprecisionWf.∀ⁱ q} runtime
    (type-abstraction X V) (type-abstraction X′ V′) →
  BackwardReturnSimulation
    (FramedValueResult
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) p⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′) q)
    (allocate-both R (type-narrowing p) θ~θ′)
    (instantiateValue
      (allocate W A θ) (freshSealName W)
      (type-abstraction X V))
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′)
      (type-abstraction X′ V′))
    index
paired-type-abstraction-backward
    {index = index} {W = W} {W′ = W′} {ρ′ = ρ′}
    {θ = θ} {θ′ = θ′}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {X = X} {X′ = X′} {V = V} {V′ = V′}
    {p = p} {p⇑ = p⇑} {q = q} {R = R}
    runtime body-lift instantiate
    θ~θ′ allocated value =
  backward-return simulation
  where
  body-runtime =
    runtime-narrowing-from-frame
      (left-world-typed allocated)
      (right-world-typed allocated)
      (assumption-membership-unique-matched
        (assumption-membership-unique runtime))
      (paired-closing-runtime-frame
        (runtime-narrowing-frame runtime)
        extension-refl (type-narrowing p) θ~θ′ body-lift)

  body-value =
    instantiate extension-refl (type-narrowing p) θ~θ′ body-runtime

  simulation :
    IndexedTerminalSimulation
      (FramedValueResult
        (NTI.store-matched zero (⇑ᵗ A)
          zero (⇑ᵗ A′) p⇑ ∷ ρ′)
        (seal-name (freshSealName W) ∷ θ)
        (seal-name (freshSealName W′) ∷ θ′) q)
      (allocate-both R (type-narrowing p) θ~θ′)
      (instantiateValue
        (allocate W A θ) (freshSealName W)
        (type-abstraction X V))
      (instantiateValue
        (allocate W′ A′ θ′) (freshSealName W′)
        (type-abstraction X′ V′))
      zero index
  simulation =
    indexed-simulation-pointwise
      type-abstraction-instantiation-computation
      type-abstraction-instantiation-computation
      (terminal-simulation-index
        (immediate-return-simulation
          (framed-result allocated
            (compiler-replanned-value
              (framed-value-typed body-value)
              (framed-value-operational body-value)
              body-value))))

paired-type-abstraction-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
    {ρbody :
      NTI.StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
    {θ θ′ A A′ B B′ X X′ V V′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {p⇑ :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {q :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (body-lift :
    NTI.LiftStoreⁱ
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρbody) →
  (instantiate :
    ∀ {U U′ C C′ σ σ′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    (C~C′ : InterpreterTypeNarrowing C C′) →
    (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
    (body-runtime :
      RuntimeNarrowing
        (allocate-both S C~C′ σ~σ′)
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ) ρbody
        (seal-name (freshSealName U) ∷ θ)
        (seal-name (freshSealName U′) ∷ θ′)) →
    FramedValueNarrowing
      {A = B} {A′ = B′} {p = q} body-runtime
      (substituteName X (freshSealName U) V)
      (substituteName X′ (freshSealName U′) V′)) →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  (allocated :
    RuntimeNarrowing
      (allocate-both R (type-narrowing p) θ~θ′)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) p⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′)) →
  FramedValueNarrowing
    {A = `∀ B} {A′ = `∀ B′}
    {p = ImprecisionWf.∀ⁱ q} runtime
    (type-abstraction X V) (type-abstraction X′ V′) →
  TargetBlameSimulation
    (allocate-both R (type-narrowing p) θ~θ′)
    (instantiateValue
      (allocate W A θ) (freshSealName W)
      (type-abstraction X V))
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′)
      (type-abstraction X′ V′))
    index
paired-type-abstraction-target-blame
    {index = index} {W = W} {W′ = W′} {ρ′ = ρ′}
    {θ = θ} {θ′ = θ′}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    {X = X} {X′ = X′} {V = V} {V′ = V′}
    {p = p} {p⇑ = p⇑} {q = q} {R = R}
    runtime body-lift instantiate
    θ~θ′ allocated value =
  target-blame-reflects simulation
  where
  body-runtime =
    runtime-narrowing-from-frame
      (left-world-typed allocated)
      (right-world-typed allocated)
      (assumption-membership-unique-matched
        (assumption-membership-unique runtime))
      (paired-closing-runtime-frame
        (runtime-narrowing-frame runtime)
        extension-refl (type-narrowing p) θ~θ′ body-lift)

  body-value =
    instantiate extension-refl (type-narrowing p) θ~θ′ body-runtime

  simulation :
    IndexedTerminalSimulation
      (FramedValueResult
        (NTI.store-matched zero (⇑ᵗ A)
          zero (⇑ᵗ A′) p⇑ ∷ ρ′)
        (seal-name (freshSealName W) ∷ θ)
        (seal-name (freshSealName W′) ∷ θ′) q)
      (allocate-both R (type-narrowing p) θ~θ′)
      (instantiateValue
        (allocate W A θ) (freshSealName W)
        (type-abstraction X V))
      (instantiateValue
        (allocate W′ A′ θ′) (freshSealName W′)
        (type-abstraction X′ V′))
      zero index
  simulation =
    indexed-simulation-pointwise
      type-abstraction-instantiation-computation
      type-abstraction-instantiation-computation
      (terminal-simulation-index
        (immediate-return-simulation
          (framed-result allocated
            (compiler-replanned-value
              (framed-value-typed body-value)
              (framed-value-operational body-value)
              body-value))))

left-type-abstraction-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ}
    {ρbody :
      NTI.StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ}
    {θ θ′ A B B′ X V V′}
    {hA⇑ : WfTy (suc Δᴸ) (⇑ᵗ A)}
    {q :
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ
        ⊢ B ⊑ B′ ⊣ Δᴿ}
    {nonvar : ImprecisionWf.NonVar B}
    {occ : occurs zero B ≡ true}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (body-lift :
    NTI.LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρbody) →
  (instantiate :
    ∀ {U U′ C σ}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    (σ-ok : TypeEnvironmentScoped U σ) →
    (body-runtime :
      RuntimeNarrowing
        (allocate-left-dynamic {A = C} S σ-ok)
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρbody
        (seal-name (freshSealName U) ∷ θ) θ′) →
    FramedValueNarrowing
      {A = B} {A′ = B′} {p = q} body-runtime
      (substituteName X (freshSealName U) V) V′) →
  (θ-ok : TypeEnvironmentScoped W θ) →
  (allocated :
    RuntimeNarrowing
      (allocate-left-dynamic {A = A} R θ-ok)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′) →
  FramedValueNarrowing
    {A = `∀ B} {A′ = B′}
    {p = ImprecisionWf.ν nonvar occ q} runtime
    (type-abstraction X V) V′ →
  ForwardReturnSimulation
    (FramedValueResult
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′ q)
    (allocate-left-dynamic {A = A} R θ-ok)
    (instantiateValue
      (allocate W A θ) (freshSealName W)
      (type-abstraction X V))
    (immediateReturn W′ V′)
    index
left-type-abstraction-forward
    {index = index} {W = W} {W′ = W′} {ρ′ = ρ′}
    {θ = θ} {θ′ = θ′}
    {A = A} {B = B} {B′ = B′}
    {X = X} {V = V} {V′ = V′}
    {hA⇑ = hA⇑} {q = q} {R = R}
    runtime body-lift instantiate θ-ok allocated value =
  forward-return simulation
  where
  body-runtime =
    runtime-narrowing-from-frame
      (left-world-typed allocated)
      (right-world-typed allocated)
      (assumption-membership-unique-source
        (assumption-membership-unique runtime))
      (left-closing-runtime-frame
        (runtime-narrowing-frame runtime)
        extension-refl θ-ok body-lift)

  body-value =
    instantiate extension-refl θ-ok body-runtime

  simulation :
    IndexedTerminalSimulation
      (FramedValueResult
        (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
        (seal-name (freshSealName W) ∷ θ) θ′ q)
      (allocate-left-dynamic {A = A} R θ-ok)
      (instantiateValue
        (allocate W A θ) (freshSealName W)
        (type-abstraction X V))
      (immediateReturn W′ V′)
      index zero
  simulation =
    indexed-simulation-pointwise
      type-abstraction-instantiation-computation
      (λ n → refl)
      (terminal-simulation-index
        (immediate-return-simulation
          (framed-result allocated
            (compiler-replanned-value
              (framed-value-typed body-value)
              (framed-value-operational body-value)
              body-value))))

left-type-abstraction-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ}
    {ρbody :
      NTI.StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ}
    {θ θ′ A B B′ X V V′}
    {hA⇑ : WfTy (suc Δᴸ) (⇑ᵗ A)}
    {q :
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ
        ⊢ B ⊑ B′ ⊣ Δᴿ}
    {nonvar : ImprecisionWf.NonVar B}
    {occ : occurs zero B ≡ true}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (body-lift :
    NTI.LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρbody) →
  (instantiate :
    ∀ {U U′ C σ}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    (σ-ok : TypeEnvironmentScoped U σ) →
    (body-runtime :
      RuntimeNarrowing
        (allocate-left-dynamic {A = C} S σ-ok)
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρbody
        (seal-name (freshSealName U) ∷ θ) θ′) →
    FramedValueNarrowing
      {A = B} {A′ = B′} {p = q} body-runtime
      (substituteName X (freshSealName U) V) V′) →
  (θ-ok : TypeEnvironmentScoped W θ) →
  (allocated :
    RuntimeNarrowing
      (allocate-left-dynamic {A = A} R θ-ok)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′) →
  FramedValueNarrowing
    {A = `∀ B} {A′ = B′}
    {p = ImprecisionWf.ν nonvar occ q} runtime
    (type-abstraction X V) V′ →
  BackwardReturnSimulation
    (FramedValueResult
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′ q)
    (allocate-left-dynamic {A = A} R θ-ok)
    (instantiateValue
      (allocate W A θ) (freshSealName W)
      (type-abstraction X V))
    (immediateReturn W′ V′)
    index
left-type-abstraction-backward
    {index = index} {W = W} {W′ = W′} {ρ′ = ρ′}
    {θ = θ} {θ′ = θ′}
    {A = A} {B = B} {B′ = B′}
    {X = X} {V = V} {V′ = V′}
    {hA⇑ = hA⇑} {q = q} {R = R}
    runtime body-lift instantiate θ-ok allocated value =
  backward-return simulation
  where
  body-runtime =
    runtime-narrowing-from-frame
      (left-world-typed allocated)
      (right-world-typed allocated)
      (assumption-membership-unique-source
        (assumption-membership-unique runtime))
      (left-closing-runtime-frame
        (runtime-narrowing-frame runtime)
        extension-refl θ-ok body-lift)

  body-value =
    instantiate extension-refl θ-ok body-runtime

  simulation :
    IndexedTerminalSimulation
      (FramedValueResult
        (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
        (seal-name (freshSealName W) ∷ θ) θ′ q)
      (allocate-left-dynamic {A = A} R θ-ok)
      (instantiateValue
        (allocate W A θ) (freshSealName W)
        (type-abstraction X V))
      (immediateReturn W′ V′)
      zero index
  simulation =
    indexed-simulation-pointwise
      type-abstraction-instantiation-computation
      (λ n → refl)
      (terminal-simulation-index
        (immediate-return-simulation
          (framed-result allocated
            (compiler-replanned-value
              (framed-value-typed body-value)
              (framed-value-operational body-value)
              body-value))))

left-type-abstraction-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ}
    {ρbody :
      NTI.StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ}
    {θ θ′ A B B′ X V V′}
    {hA⇑ : WfTy (suc Δᴸ) (⇑ᵗ A)}
    {q :
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ
        ⊢ B ⊑ B′ ⊣ Δᴿ}
    {nonvar : ImprecisionWf.NonVar B}
    {occ : occurs zero B ≡ true}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (body-lift :
    NTI.LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρbody) →
  (instantiate :
    ∀ {U U′ C σ}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    (σ-ok : TypeEnvironmentScoped U σ) →
    (body-runtime :
      RuntimeNarrowing
        (allocate-left-dynamic {A = C} S σ-ok)
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρbody
        (seal-name (freshSealName U) ∷ θ) θ′) →
    FramedValueNarrowing
      {A = B} {A′ = B′} {p = q} body-runtime
      (substituteName X (freshSealName U) V) V′) →
  (θ-ok : TypeEnvironmentScoped W θ) →
  (allocated :
    RuntimeNarrowing
      (allocate-left-dynamic {A = A} R θ-ok)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′) →
  FramedValueNarrowing
    {A = `∀ B} {A′ = B′}
    {p = ImprecisionWf.ν nonvar occ q} runtime
    (type-abstraction X V) V′ →
  TargetBlameSimulation
    (allocate-left-dynamic {A = A} R θ-ok)
    (instantiateValue
      (allocate W A θ) (freshSealName W)
      (type-abstraction X V))
    (immediateReturn W′ V′)
    index
left-type-abstraction-target-blame
    {index = index} {W = W} {W′ = W′} {ρ′ = ρ′}
    {θ = θ} {θ′ = θ′}
    {A = A} {B = B} {B′ = B′}
    {X = X} {V = V} {V′ = V′}
    {hA⇑ = hA⇑} {q = q} {R = R}
    runtime body-lift instantiate θ-ok allocated value =
  target-blame-reflects simulation
  where
  body-runtime =
    runtime-narrowing-from-frame
      (left-world-typed allocated)
      (right-world-typed allocated)
      (assumption-membership-unique-source
        (assumption-membership-unique runtime))
      (left-closing-runtime-frame
        (runtime-narrowing-frame runtime)
        extension-refl θ-ok body-lift)

  body-value =
    instantiate extension-refl θ-ok body-runtime

  simulation :
    IndexedTerminalSimulation
      (FramedValueResult
        (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
        (seal-name (freshSealName W) ∷ θ) θ′ q)
      (allocate-left-dynamic {A = A} R θ-ok)
      (instantiateValue
        (allocate W A θ) (freshSealName W)
        (type-abstraction X V))
      (immediateReturn W′ V′)
      zero index
  simulation =
    indexed-simulation-pointwise
      type-abstraction-instantiation-computation
      (λ n → refl)
      (terminal-simulation-index
        (immediate-return-simulation
          (framed-result allocated
            (compiler-replanned-value
              (framed-value-typed body-value)
              (framed-value-operational body-value)
              body-value))))
