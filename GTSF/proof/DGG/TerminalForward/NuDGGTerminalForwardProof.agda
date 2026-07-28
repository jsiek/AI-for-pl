module proof.DGG.TerminalForward.NuDGGTerminalForwardProof where

-- File Charter:
--   * Proves the world-coherent forward source-value terminal contract from
--     source one-step simulation up to bilateral reduction and right-value
--     catch-up.
--   * Aligns each returned source tail with the observed source trace before
--     recurring on the remaining suffix.
--   * Transports runtime, store, context, and type invariants mechanically.
--   * Imports neither live simulation implementation.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; s≤s⁻¹; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
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
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( leftCtxⁱ
  ; rightCtxⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; Value; _∣_∣_⊢_⦂_)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import proof.DGG.Core.NuDGGPreservation using
  (multi-store-preservation)
open import proof.DGG.TerminalForward.NuDGGTerminalForwardDef using
  (WorldCoherentForwardSourceValueᵀ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupDef using
  (WorldCoherentRightValueCatchupᵀ)
open import proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepDef using
  (WorldCoherentSourceOneStepSimulationᵀ)
open import proof.DGG.Core.NuPreservation using
  (multi-runtime-preservation)
open import proof.DGG.Core.NuProgress using (runtime-value-no•)
open import proof.Core.Properties.ReductionProperties using
  ( applyStores-++
  ; applyTyCtxs-++
  ; applyTys-++
  ; ↠-trans
  )
open import proof.DGG.Core.NuReductionDeterminism using
  (source-blame-excludes-value; target-tail-prefix-value)
open import proof.DGG.Core.NuDGGTraceMeasure using
  (aligned-residual-shorter)
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


private
 forward-source-value-with-fuel :
    WorldCoherentSourceOneStepSimulationᵀ →
    WorldCoherentRightValueCatchupᵀ →
    ∀ (fuel : ℕ) {Φ Δᴸ Δᴿ M M′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    WorldCoherent ρ →
    SourceNameExclusive Φ →
    AssumptionMembershipUnique Φ →
    StoreWf Δᴸ (leftStoreⁱ ρ) →
    StoreWf Δᴿ (rightStoreⁱ ρ) →
    RuntimeOK M →
    RuntimeOK M′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    ∀ V χs →
    M —↠[ χs ] V →
    Value V →
    length χs ≤ fuel →
    ∃[ V′ ] (Σ[ θs ∈ StoreChanges ]
    (∃[ Ψ ] (Σ[ ρ′ ∈
        StoreImp Ψ
          (applyTyCtxs χs Δᴸ) (applyTyCtxs θs Δᴿ) ]
    (Σ[ q ∈
        (Ψ ∣ applyTyCtxs χs Δᴸ
          ⊢ applyTys χs A ⊑ applyTys θs B
          ⊣ applyTyCtxs θs Δᴿ) ]
      ((M′ —↠[ θs ] V′) ×
       Value V′ ×
       (leftStoreⁱ ρ′ ≡ applyStores χs (leftStoreⁱ ρ)) ×
       (rightStoreⁱ ρ′ ≡ applyStores θs (rightStoreⁱ ρ)) ×
       Ψ ∣ applyTyCtxs χs Δᴸ
         ∣ applyTyCtxs θs Δᴿ ∣ ρ′ ∣ []
         ⊢ᴺ V ⊑ V′
         ⦂ applyTys χs A ⊑ applyTys θs B ∶ q)))))
 forward-source-value-with-fuel
    one-step right-catchup fuel
    {M = M} coherent exclusive unique wfL wfR
    okM okM′ M⊑M′ .M [] ↠-refl vM bound =
  right-catchup coherent exclusive unique wfR okM′ vM
    (runtime-value-no• okM vM) M⊑M′
 forward-source-value-with-fuel
    one-step right-catchup zero
    coherent exclusive unique wfL wfR okM okM′ M⊑M′
    V (χ ∷ χs) (↠-step source-step source-rest) vV ()
 forward-source-value-with-fuel
    one-step right-catchup
    (suc fuel)
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} {ρ = ρ}
    coherent exclusive unique wfL wfR okM okM′ M⊑M′
    V (χ ∷ χs) (↠-step source-step source-rest) vV bound
    with one-step coherent exclusive unique wfL wfR okM okM′ M⊑M′
      source-step
 forward-source-value-with-fuel
    one-step right-catchup
    (suc fuel)
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} {ρ = ρ}
    coherent exclusive unique wfL wfR okM okM′ M⊑M′
    V (χ ∷ χs) (↠-step source-step source-rest) vV bound
    | inj₂ (source-blame-changes , source↠blame) =
  ⊥-elim
    (source-blame-excludes-value source↠blame
      (↠-step source-step source-rest) vV)
 forward-source-value-with-fuel
    one-step right-catchup
    (suc fuel)
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} {ρ = ρ}
    coherent exclusive unique wfL wfR okM okM′ M⊑M′
    V (χ ∷ χs) (↠-step source-step source-rest) vV bound
    | inj₁
        (K , L′ , ψs , θs , Ψ , ρ′ , q , L↠K , M′↠L′ ,
          coherent′ , exclusive′ , unique′ , left-eq , right-eq , K⊑L′)
    with target-tail-prefix-value L↠K source-rest vV
  where
  source-typing = forward-empty-context-source-typing M⊑M′

  target-typing = forward-empty-context-target-typing M⊑M′

  next-wfL =
    subst
      (StoreWf (applyTyCtxs ψs (applyTyCtx χ Δᴸ)))
      (sym left-eq)
      (multi-store-preservation wfL okM source-typing
        (↠-step source-step L↠K))

  next-wfR =
    subst (StoreWf (applyTyCtxs θs Δᴿ)) (sym right-eq)
      (multi-store-preservation wfR okM′ target-typing M′↠L′)

  next-okK =
    multi-runtime-preservation wfL okM source-typing
      (↠-step source-step L↠K)

  next-okL′ =
    multi-runtime-preservation wfR okM′ target-typing M′↠L′

 forward-source-value-with-fuel
    one-step right-catchup
    (suc fuel)
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} {ρ = ρ}
    coherent exclusive unique wfL wfR okM okM′ M⊑M′
    V (χ ∷ χs) (↠-step source-step source-rest) vV bound
    | inj₁
        (K , L′ , ψs , θs , Ψ , ρ′ , q , L↠K , M′↠L′ ,
          coherent′ , exclusive′ , unique′ , left-eq , right-eq , K⊑L′)
    | ηs , K↠V , trace-eq
    with forward-source-value-with-fuel
      one-step right-catchup fuel coherent′ exclusive′
      unique′ next-wfL next-wfR next-okK next-okL′ K⊑L′
      V ηs K↠V vV
      (s≤s⁻¹
        (≤-trans
          (aligned-residual-shorter
            {χ = χ}
            {observed = χs}
            {administrative = ψs}
            {residual = ηs}
            trace-eq)
          bound))
  where
  source-typing = forward-empty-context-source-typing M⊑M′

  target-typing = forward-empty-context-target-typing M⊑M′

  next-wfL =
    subst
      (StoreWf (applyTyCtxs ψs (applyTyCtx χ Δᴸ)))
      (sym left-eq)
      (multi-store-preservation wfL okM source-typing
        (↠-step source-step L↠K))

  next-wfR =
    subst (StoreWf (applyTyCtxs θs Δᴿ)) (sym right-eq)
      (multi-store-preservation wfR okM′ target-typing M′↠L′)

  next-okK =
    multi-runtime-preservation wfL okM source-typing
      (↠-step source-step L↠K)

  next-okL′ =
    multi-runtime-preservation wfR okM′ target-typing M′↠L′

 forward-source-value-with-fuel
    one-step right-catchup
    (suc fuel)
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {A = A} {B = B} {ρ = ρ}
    coherent exclusive unique wfL wfR okM okM′ M⊑M′
    V (χ ∷ χs) (↠-step source-step source-rest) vV bound
    | inj₁
        (K , L′ , ψs , θs , Ψ , ρ′ , q , L↠K , M′↠L′ ,
          coherent′ , exclusive′ , unique′ , left-eq , right-eq , K⊑L′)
    | ηs , K↠V , trace-eq
    | V′ , ζs , Ω , ρ″ , r , L′↠V′ , vV′ ,
      final-left-eq , final-right-eq , V⊑V′
    rewrite trace-eq
          | sym (applyTyCtxs-++ ψs ηs (applyTyCtx χ Δᴸ))
          | sym (applyTys-++ ψs ηs (applyTy χ A))
          | sym (applyTyCtxs-++ θs ζs Δᴿ)
          | sym (applyTys-++ θs ζs B) =
      V′ , θs ++ ζs , Ω , ρ″ , r ,
      ↠-trans M′↠L′ L′↠V′ ,
      vV′ ,
      trans final-left-eq
        (trans (cong (applyStores ηs) left-eq)
          (sym
            (applyStores-++ ψs ηs
              (applyStore χ (leftStoreⁱ ρ))))) ,
      trans final-right-eq
        (trans (cong (applyStores ζs) right-eq)
          (sym (applyStores-++ θs ζs (rightStoreⁱ ρ)))) ,
      V⊑V′
  where
  source-typing = forward-empty-context-source-typing M⊑M′

  target-typing = forward-empty-context-target-typing M⊑M′

  next-wfL =
    subst
      (StoreWf (applyTyCtxs ψs (applyTyCtx χ Δᴸ)))
      (sym left-eq)
      (multi-store-preservation wfL okM source-typing
        (↠-step source-step L↠K))

  next-wfR =
    subst (StoreWf (applyTyCtxs θs Δᴿ)) (sym right-eq)
      (multi-store-preservation wfR okM′ target-typing M′↠L′)

  next-okK =
    multi-runtime-preservation wfL okM source-typing
      (↠-step source-step L↠K)

  next-okL′ =
    multi-runtime-preservation wfR okM′ target-typing M′↠L′


world-coherent-forward-source-value-proofᵀ :
  WorldCoherentSourceOneStepSimulationᵀ →
  WorldCoherentRightValueCatchupᵀ →
  WorldCoherentForwardSourceValueᵀ
world-coherent-forward-source-value-proofᵀ
    one-step right-catchup
    coherent exclusive unique wfL wfR okM okM′ M⊑M′
    V χs M↠V vV =
  forward-source-value-with-fuel
    one-step right-catchup (length χs)
    coherent exclusive unique wfL wfR okM okM′ M⊑M′
    V χs M↠V vV ≤-refl
