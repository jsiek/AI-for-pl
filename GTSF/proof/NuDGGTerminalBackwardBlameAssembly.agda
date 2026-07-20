module proof.NuDGGTerminalBackwardBlameAssembly where

-- File Charter:
--   * Owns the higher-order backward-blame terminal trace assembly theorem.
--   * Proves those interfaces sufficient by fuel induction on the observed
--     target trace, preserving runtime and store invariants at every step.
--   * Does not import either live implementation; that fit check is isolated
--     in `NuDGGTerminalBackwardBlameIntegration`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; s≤s⁻¹; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_,_; ∃-syntax)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChange
  ; StoreChanges
  ; _—→[_]_
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; _∣_∣_⊢_⦂_; blame)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import proof.ReductionProperties using (↠-trans)
open import TermTyping using (forget)
open import proof.NuDGGTraceAlignment using
  (weak-result-target-prefix-blameᵀ)
open import proof.NuDGGTraceMeasure using
  (aligned-residual-shorter)
open import proof.NuDGGWeakResultPreservation using
  ( weak-result-source-store-wf
  ; weak-result-source-runtime
  ; weak-result-target-store-wf
  ; weak-result-target-runtime
  )
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedOutcome
  ; canonicalIndexedResults
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  ; resultStore
  ; sourceCatchup
  ; sourceChanges
  ; targetTailChanges
  ; weakIndexedResult
  )


normalize-empty-runtime-context :
  ∀ {Δ Σ Γ M A} →
  Γ ≡ [] →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A
normalize-empty-runtime-context refl M⊢ = M⊢

empty-context-source-typing :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A
empty-context-source-typing
    {Φ} {Δᴸ} {Δᴿ} {M} {M′} {A} {B} {ρ} {p} M⊑M′ =
  normalize-empty-runtime-context
    {Γ = leftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} []} refl
    (forget
      (nu-term-imprecision-source-typing
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γ = []}
        {M = M} {M′ = M′} {A = A} {B = B} {p = p} M⊑M′))

empty-context-target-typing :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ B
empty-context-target-typing
    {Φ} {Δᴸ} {Δᴿ} {M} {M′} {A} {B} {ρ} {p} M⊑M′ =
  normalize-empty-runtime-context
    {Γ = rightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} []} refl
    (forget
      (nu-term-imprecision-target-typing
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γ = []}
        {M = M} {M′ = M′} {A = A} {B = B} {p = p} M⊑M′))

backward-target-blame-general-from-componentsᵀ :
  (one-step :
    ∀ {Φ Δᴸ Δᴿ M M′ N′ A B}
      {χ : StoreChange}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    M′ —→[ χ ] N′ →
    WeakOneStepIndexedOutcome
      {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p) →
  (target-blame-catchup :
    ∀ {Φ Δᴸ Δᴿ M A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    RuntimeOK M →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ blame ⦂ A ⊑ B ∶ p →
    ∃[ χs ] (M —↠[ χs ] blame)) →
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  ∀ χs′ →
  M′ —↠[ χs′ ] blame →
  ∃[ χs ] (M —↠[ χs ] blame)
backward-target-blame-general-from-componentsᵀ
    one-step target-blame-catchup wfL wfR okM okM′ M⊑M′
    χs′ M′↠blame =
  go (length χs′) wfL wfR okM okM′ M⊑M′ χs′ M′↠blame ≤-refl
  where
  go :
    ∀ (fuel : ℕ) { Φ Δᴸ Δᴿ M M′ A B }
      { ρ : StoreImp Φ Δᴸ Δᴿ }
      { p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ } →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    ∀ (ψs : StoreChanges) →
    M′ —↠[ ψs ] blame →
    length ψs ≤ fuel →
    ∃[ χs ] (M —↠[ χs ] blame)
  go zero wfL wfR okM okM′ M⊑M′ [] ↠-refl bound =
    target-blame-catchup okM M⊑M′
  go zero wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) ()
  go (suc fuel) wfL wfR okM okM′ M⊑M′ [] ↠-refl bound =
    target-blame-catchup okM M⊑M′
  go (suc fuel) wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) bound
    with one-step wfR okM okM′ M⊑M′ target-step
  go (suc fuel) wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) bound
    | indexed-outcome-source-blame {χs = source-blame-changes}
        source-blame =
      source-blame-changes , source-blame
  go (suc fuel) wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) bound
    | indexed-outcome-related indexed transport coherence
    with weak-result-target-prefix-blameᵀ
      (weakIndexedResult indexed) target-rest
  go (suc fuel) wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) bound
    | indexed-outcome-related indexed transport coherence
    | residual-changes , target-result↠blame , trace-eq
    with go fuel
      (weak-result-source-store-wf
        (weakIndexedResult indexed) wfL okM
        (empty-context-source-typing M⊑M′))
      (weak-result-target-store-wf
        (weakIndexedResult indexed) wfR okM′
        (empty-context-target-typing M⊑M′) target-step)
      (weak-result-source-runtime
        (weakIndexedResult indexed) wfL okM
        (empty-context-source-typing M⊑M′))
      (weak-result-target-runtime
        (weakIndexedResult indexed) wfR okM′
        (empty-context-target-typing M⊑M′) target-step)
      (canonicalIndexedResults indexed)
      residual-changes target-result↠blame
      (s≤s⁻¹
        (≤-trans
          (aligned-residual-shorter
            {χ = χ}
            {observed = ψs}
            {administrative =
              targetTailChanges (weakIndexedResult indexed)}
            {residual = residual-changes}
            trace-eq)
          bound))
  go (suc fuel) wfL wfR okM okM′ M⊑M′
      (χ ∷ ψs) (↠-step target-step target-rest) bound
    | indexed-outcome-related indexed transport coherence
    | residual-changes , target-result↠blame , trace-eq
    | result-blame-changes , source-result↠blame =
      sourceChanges (weakIndexedResult indexed) ++ result-blame-changes ,
      ↠-trans (sourceCatchup (weakIndexedResult indexed))
              source-result↠blame
