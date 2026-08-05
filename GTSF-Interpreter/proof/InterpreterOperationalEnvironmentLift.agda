module proof.InterpreterOperationalEnvironmentLift where

-- File Charter:
--   * Lifts exact operational term environments under paired or source-only
--     type binders.
--   * Uses the semantic interpretation equation for weakening a static type.
--   * Contains no interpreter call or reduction result.

open import Data.List using (_∷_)
import Data.Nat
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst; sym)

open import ImprecisionWf using (ImpCtx)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Narrowing.InterpreterOperationalValueNarrowing
open import Narrowing.InterpreterOperationalValueNarrowingProperties
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterWorldNarrowing using (TypeEnvironmentScoped)
import NuTermImprecision as NTI
import proof.InterpreterSemanticTypingProperties as SemanticProof
open import Types using (Ty; TyCtx)

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

operational-value-type-transport :
  ∀ {W W′ A A′ B B′ V V′}
    {R : WorldRelation W W′} →
  A ≡ A′ →
  B ≡ B′ →
  OperationalValueNarrowing A B R V V′ →
  OperationalValueNarrowing A′ B′ R V V′
operational-value-type-transport refl refl value =
  value

paired-operational-environment-lift :
  ∀ {W W′ U U′}
    {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {θ θ′ : TypeEnvironment}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {γᵀ′ : NTI.CtxImp Ψ (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ)}
    {γ γ′ : Environment}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {C C′ : Ty}
    {C~C′ : InterpreterTypeNarrowing C C′}
    {σ σ′ : TypeEnvironment}
    {σ~σ′ : TypeEnvironmentNarrowing S σ σ′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  WorldTyping (allocate U C σ) →
  WorldTyping (allocate U′ C′ σ′) →
  NTI.LiftCtxⁱ Ψ γᵀ γᵀ′ →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OperationalEnvironmentNarrowing
    (seal-name (freshSealName U) ∷ θ)
    (seal-name (freshSealName U′) ∷ θ′)
    (allocate-both S C~C′ σ~σ′) γᵀ′ γ γ′
paired-operational-environment-lift R≤S U⊢ U′⊢
    NTI.lift-ctx-[] []⊑[]ᵒ =
  []⊑[]ᵒ
paired-operational-environment-lift
    {U = U} {U′ = U′} {θ = θ} {θ′ = θ′}
    R≤S U⊢ U′⊢
    (NTI.lift-ctx-∷ {A = A} {B = B} liftγ)
    (value ∷⊑∷ᵒ environment) =
  operational-value-type-transport
    (sym (SemanticProof.interpret-weaken
      (nominal-type (seal-name (freshSealName U)))
      (semanticEnvironment θ) A))
    (sym (SemanticProof.interpret-weaken
      (nominal-type (seal-name (freshSealName U′)))
      (semanticEnvironment θ′) B))
    (operational-value-narrowing-weaken
      (extension-both R≤S) U⊢ U′⊢ value)
    ∷⊑∷ᵒ
  paired-operational-environment-lift
    R≤S U⊢ U′⊢ liftγ environment

left-operational-environment-lift :
  ∀ {W W′ U U′}
    {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {θ θ′ : TypeEnvironment}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {γᵀ′ : NTI.CtxImp Ψ (Data.Nat.suc Δᴸ) Δᴿ}
    {γ γ′ : Environment}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {C : Ty}
    {σ : TypeEnvironment}
    {σ-ok : TypeEnvironmentScoped U σ} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  WorldTyping (allocate U C σ) →
  WorldTyping U′ →
  NTI.LiftLeftCtxⁱ Ψ γᵀ γᵀ′ →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  OperationalEnvironmentNarrowing
    (seal-name (freshSealName U) ∷ θ) θ′
    (allocate-left-dynamic {A = C} S σ-ok) γᵀ′ γ γ′
left-operational-environment-lift R≤S U⊢ U′⊢
    NTI.lift-left-ctx-[] []⊑[]ᵒ =
  []⊑[]ᵒ
left-operational-environment-lift
    {U = U} {θ = θ}
    R≤S U⊢ U′⊢
    (NTI.lift-left-ctx-∷ {A = A} liftγ)
    (value ∷⊑∷ᵒ environment) =
  operational-value-type-transport
    (sym (SemanticProof.interpret-weaken
      (nominal-type (seal-name (freshSealName U)))
      (semanticEnvironment θ) A))
    refl
    (operational-value-narrowing-weaken
      (extension-left R≤S) U⊢ U′⊢ value)
    ∷⊑∷ᵒ
  left-operational-environment-lift
    R≤S U⊢ U′⊢ liftγ environment
