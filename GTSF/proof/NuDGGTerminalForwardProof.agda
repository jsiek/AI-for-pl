module proof.NuDGGTerminalForwardProof where

-- File Charter:
--   * Proves the world-coherent forward source-value terminal contract from
--     exact source one-step simulation and right-value catch-up.
--   * Recurses structurally on the observed source trace and composes only the
--     target traces returned by the two semantic dependencies.
--   * Transports runtime, store, context, and type invariants mechanically.
--   * Imports neither live simulation implementation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyStore
  ; applyStores
  ; applyTy
  ; applyTyCtx
  ; applyTyCtxs
  ; applyTys
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
open import NuTerms using
  (RuntimeOK; Term; Value; _∣_∣_⊢_⦂_)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import proof.NuDGGPreservation using
  (multi-store-preservation)
open import proof.NuDGGTerminalForwardDef using
  (WorldCoherentForwardSourceValueᵀ)
open import proof.NuImprecisionWorldCoherentRightValueCatchupDef using
  (WorldCoherentRightValueCatchupᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepDef using
  (WorldCoherentSourceOneStepSimulationᵀ)
open import proof.NuPreservation using
  ( multi-runtime-preservation
  ; runtime-preservation
  ; store-preservation
  )
open import proof.NuProgress using (runtime-value-no•)
open import proof.ReductionProperties using
  ( applyStores-++
  ; applyTyCtxs-++
  ; applyTys-++
  ; ↠-trans
  )
open import TermTyping using (forget)


forward-normalize-empty-runtime-context :
  ∀ {Δ Σ Γ M A} →
  Γ ≡ [] →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A
forward-normalize-empty-runtime-context refl M⊢ = M⊢


forward-empty-context-source-typing :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A
forward-empty-context-source-typing
    {Φ} {Δᴸ} {Δᴿ} {M} {M′} {A} {B} {ρ} {p} M⊑M′ =
  forward-normalize-empty-runtime-context
    {Γ = leftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} []} refl
    (forget
      (nu-term-imprecision-source-typing
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γ = []}
        {M = M} {M′ = M′} {A = A} {B = B} {p = p} M⊑M′))


forward-empty-context-target-typing :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ B
forward-empty-context-target-typing
    {Φ} {Δᴸ} {Δᴿ} {M} {M′} {A} {B} {ρ} {p} M⊑M′ =
  forward-normalize-empty-runtime-context
    {Γ = rightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} []} refl
    (forget
      (nu-term-imprecision-target-typing
        {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γ = []}
        {M = M} {M′ = M′} {A = A} {B = B} {p = p} M⊑M′))


world-coherent-forward-source-value-proofᵀ :
  WorldCoherentSourceOneStepSimulationᵀ →
  WorldCoherentRightValueCatchupᵀ →
  WorldCoherentForwardSourceValueᵀ
world-coherent-forward-source-value-proofᵀ
    one-step right-catchup {M = M} coherent exclusive wfL wfR
    okM okM′ M⊑M′ .M [] ↠-refl vM =
  right-catchup coherent exclusive wfR okM′ vM
    (runtime-value-no• okM vM) M⊑M′
world-coherent-forward-source-value-proofᵀ
    one-step right-catchup
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} {ρ = ρ}
    coherent exclusive wfL wfR okM okM′ M⊑M′
    V (χ ∷ χs) (↠-step source-step source-rest) vV
    with one-step coherent exclusive wfL wfR okM okM′ M⊑M′
      source-step
world-coherent-forward-source-value-proofᵀ
    one-step right-catchup
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} {ρ = ρ}
    coherent exclusive wfL wfR okM okM′ M⊑M′
    V (χ ∷ χs) (↠-step source-step source-rest) vV
    | L′ , θs , Ψ , ρ′ , q , M′↠L′ , coherent′ , exclusive′ ,
      left-eq , right-eq , L⊑L′
    with world-coherent-forward-source-value-proofᵀ
      one-step right-catchup coherent′ exclusive′
      next-wfL next-wfR next-okL next-okL′ L⊑L′
      V χs source-rest vV
  where
  source-typing = forward-empty-context-source-typing M⊑M′

  target-typing = forward-empty-context-target-typing M⊑M′

  next-wfL =
    subst (StoreWf (applyTyCtx χ Δᴸ)) (sym left-eq)
      (store-preservation wfL source-typing source-step)

  next-wfR =
    subst (StoreWf (applyTyCtxs θs Δᴿ)) (sym right-eq)
      (multi-store-preservation wfR okM′ target-typing M′↠L′)

  next-okL = runtime-preservation wfL okM source-typing source-step

  next-okL′ =
    multi-runtime-preservation wfR okM′ target-typing M′↠L′
world-coherent-forward-source-value-proofᵀ
    one-step right-catchup
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} {ρ = ρ}
    coherent exclusive wfL wfR okM okM′ M⊑M′
    V (χ ∷ χs) (↠-step source-step source-rest) vV
    | L′ , θs , Ψ , ρ′ , q , M′↠L′ , coherent′ , exclusive′ ,
      left-eq , right-eq , L⊑L′
    | V′ , ηs , Ω , ρ″ , r , L′↠V′ , vV′ ,
      final-left-eq , final-right-eq , V⊑V′
    rewrite sym (applyTyCtxs-++ θs ηs Δᴿ)
          | sym (applyTys-++ θs ηs B) =
      V′ , θs ++ ηs , Ω , ρ″ , r ,
      ↠-trans M′↠L′ L′↠V′ ,
      vV′ ,
      trans final-left-eq (cong (applyStores χs) left-eq) ,
      trans final-right-eq
        (trans (cong (applyStores ηs) right-eq)
          (sym (applyStores-++ θs ηs (rightStoreⁱ ρ)))) ,
      V⊑V′
  where
  source-typing = forward-empty-context-source-typing M⊑M′

  target-typing = forward-empty-context-target-typing M⊑M′

  next-wfL =
    subst (StoreWf (applyTyCtx χ Δᴸ)) (sym left-eq)
      (store-preservation wfL source-typing source-step)

  next-wfR =
    subst (StoreWf (applyTyCtxs θs Δᴿ)) (sym right-eq)
      (multi-store-preservation wfR okM′ target-typing M′↠L′)

  next-okL = runtime-preservation wfL okM source-typing source-step

  next-okL′ =
    multi-runtime-preservation wfR okM′ target-typing M′↠L′
