module Narrowing.InterpreterTermNarrowing where

-- File Charter:
--   * Public surface for reduction-free interpreter source-term narrowing.
--   * Exposes structural closure, compiler-image exclusions, world weakening,
--     and endpoint typing with their claims stated at the use site.
--   * Delegates proof scripts to `proof.InterpreterTermNarrowingProof`.

open import Data.Nat using (suc)
open import Data.List using (_∷_)
open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Coercions using (Coercion; _↦_; `∀; gen)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter using
  (Value; World; TypeEnvironment; closeValue; closure)
import Narrowing.InterpreterCoercionNarrowing as ICN
import Narrowing.InterpreterQuotientValueNarrowing as IQVN
import Runtime.InterpreterRuntimeFrame as Frame
open import Typing.InterpreterSemanticTypingCore using
  (EnvironmentTyping; WorldTyping)
open import Narrowing.InterpreterTermNarrowingCore public
open import Narrowing.InterpreterValueNarrowing
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties
import NuTermImprecision as NTI
import NuTerms as N
import TermTyping as TT
open import Types
import proof.InterpreterTermNarrowingProof as Proof
import proof.InterpreterTermShapeProof as ShapeProof

module PersistentWorldProperties =
  WorldProperties.WorldNarrowingProperties
    ICN.InterpreterTypeNarrowing

data PersistentBodyNarrowing
    {W W′ : World}
    (R : RelatedWorlds.WorldRelation W W′)
    (γ γ′ : Interpreter.Environment)
    (θ θ′ : TypeEnvironment)
    (N N′ : N.Term) : Set₁ where
  persistent-body-narrowing :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
      {A A′ B B′ : Ty}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ (NTI.ctx-imp A A′ pA ∷ γᵀ)
      N N′ B B′ pB →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    (∀ {U U′}
       {S : RelatedWorlds.WorldRelation U U′} →
      RelatedWorlds.WorldExtension R S →
      WorldTyping U →
      EnvironmentTyping U θ γ (NTI.leftCtxⁱ γᵀ)) →
    (∀ {U U′}
       {S : RelatedWorlds.WorldRelation U U′} →
      RelatedWorlds.WorldExtension R S →
      WorldTyping U′ →
      EnvironmentTyping U′ θ′ γ′ (NTI.rightCtxⁱ γᵀ)) →
    PersistentBodyNarrowing R γ γ′ θ θ′ N N′

data PersistentSemanticCoercionNarrowing
    {W W′ : World}
    (R : RelatedWorlds.WorldRelation W W′)
    (θ θ′ : TypeEnvironment)
    (c c′ : Coercion) : Set₁ where
  persistent-semantic-coercion :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {A A′ B B′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (ICN.apply-coercion c) (ICN.apply-coercion c′) p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentSemanticCoercionNarrowing R θ θ′ c c′

  persistent-component-coercion :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {A A′ B B′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (ICN.apply-coercion c) (ICN.apply-coercion c′) p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentSemanticCoercionNarrowing R θ θ′ c c′

  persistent-forall-component :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {A A′ B B′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (ICN.apply-coercion (`∀ c))
      (ICN.apply-coercion (`∀ c′)) p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentSemanticCoercionNarrowing R θ θ′ c c′

  persistent-generalized-component :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {A A′ B B′ C C′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (ICN.apply-coercion (gen C c))
      (ICN.apply-coercion (gen C′ c′)) p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentSemanticCoercionNarrowing R θ θ′ c c′

persistent-body-weaken :
  ∀ {W W′ U U′ γ γ′ θ θ′ N N′}
    {R : RelatedWorlds.WorldRelation W W′}
    {S : RelatedWorlds.WorldRelation U U′} →
  RelatedWorlds.WorldExtension R S →
  PersistentBodyNarrowing R γ γ′ θ θ′ N N′ →
  PersistentBodyNarrowing S γ γ′ θ θ′ N N′
persistent-body-weaken R≤S
    (persistent-body-narrowing
      (open-interpreter-narrowing alignment)
      runtime left-env right-env) =
  persistent-body-narrowing
    (open-interpreter-narrowing alignment)
    (Frame.runtime-frame-weaken R≤S runtime)
    (λ S≤T T⊢ →
      left-env
        (PersistentWorldProperties.world-extension-trans R≤S S≤T)
        T⊢)
    (λ S≤T T′⊢ →
      right-env
        (PersistentWorldProperties.world-extension-trans R≤S S≤T)
        T′⊢)

data PersistentLeftFunctionProxyBoundary
    {W W′ : World}
    (R : RelatedWorlds.WorldRelation W W′)
    (θ : TypeEnvironment)
    (p q : Coercion) : Set₁ where
  persistent-left-function-proxy :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ′ A A′ B B′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (ICN.apply-coercion (p ↦ q)) ICN.skip-coercion pA pB →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentLeftFunctionProxyBoundary R θ p q

  persistent-left-function-component :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ′ A A′ B B′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (ICN.apply-coercion (p ↦ q)) ICN.skip-coercion pA pB →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentLeftFunctionProxyBoundary R θ p q

data PersistentRightFunctionProxyBoundary
    {W W′ : World}
    (R : RelatedWorlds.WorldRelation W W′)
    (θ′ : TypeEnvironment)
    (p q : Coercion) : Set₁ where
  persistent-right-function-proxy :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ A A′ B B′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      ICN.skip-coercion (ICN.apply-coercion (p ↦ q)) pA pB →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentRightFunctionProxyBoundary R θ′ p q

  persistent-right-function-component :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ A A′ B B′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      ICN.skip-coercion (ICN.apply-coercion (p ↦ q)) pA pB →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentRightFunctionProxyBoundary R θ′ p q

data PersistentLeftForallProxyBoundary
    {W W′ : World}
    (R : RelatedWorlds.WorldRelation W W′)
    (θ : TypeEnvironment)
    (c : Coercion) : Set₁ where
  persistent-left-forall-proxy :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ′ A A′ B B′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (ICN.apply-coercion (`∀ c)) ICN.skip-coercion p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentLeftForallProxyBoundary R θ c

  persistent-left-forall-component :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ′ A A′ B B′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (ICN.apply-coercion (`∀ c)) ICN.skip-coercion p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentLeftForallProxyBoundary R θ c

data PersistentRightForallProxyBoundary
    {W W′ : World}
    (R : RelatedWorlds.WorldRelation W W′)
    (θ′ : TypeEnvironment)
    (c : Coercion) : Set₁ where
  persistent-right-forall-proxy :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ A A′ B B′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      ICN.skip-coercion (ICN.apply-coercion (`∀ c)) p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentRightForallProxyBoundary R θ′ c

  persistent-right-forall-component :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ A A′ B B′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    ICN.ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      ICN.skip-coercion (ICN.apply-coercion (`∀ c)) p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentRightForallProxyBoundary R θ′ c

data PersistentLeftGeneralizationBoundary
    {W W′ : World}
    (R : RelatedWorlds.WorldRelation W W′)
    (θ : TypeEnvironment)
    (A : Ty) (c : Coercion) : Set₁ where
  persistent-left-generalization :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ′ B B′ C C′}
      {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
    ICN.OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (ICN.apply-coercion (gen A c)) ICN.skip-coercion p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentLeftGeneralizationBoundary R θ A c

  persistent-left-generalization-component :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ′ B B′ C C′}
      {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
    ICN.ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (ICN.apply-coercion (gen A c)) ICN.skip-coercion p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentLeftGeneralizationBoundary R θ A c

data PersistentRightGeneralizationBoundary
    {W W′ : World}
    (R : RelatedWorlds.WorldRelation W W′)
    (θ′ : TypeEnvironment)
    (A : Ty) (c : Coercion) : Set₁ where
  persistent-right-generalization :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ B B′ C C′}
      {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
    ICN.OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      ICN.skip-coercion (ICN.apply-coercion (gen A c)) p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentRightGeneralizationBoundary R θ′ A c

  persistent-right-generalization-component :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ B B′ C C′}
      {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
    ICN.ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      ICN.skip-coercion (ICN.apply-coercion (gen A c)) p q →
    Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
    PersistentRightGeneralizationBoundary R θ′ A c

persistent-semantic-coercion-weaken :
  ∀ {W W′ U U′ θ θ′ c c′}
    {R : RelatedWorlds.WorldRelation W W′}
    {S : RelatedWorlds.WorldRelation U U′} →
  RelatedWorlds.WorldExtension R S →
  PersistentSemanticCoercionNarrowing R θ θ′ c c′ →
  PersistentSemanticCoercionNarrowing S θ θ′ c c′
persistent-semantic-coercion-weaken R≤S
    (persistent-semantic-coercion coercion runtime) =
  persistent-semantic-coercion coercion
    (Frame.runtime-frame-weaken R≤S runtime)
persistent-semantic-coercion-weaken R≤S
    (persistent-component-coercion coercion runtime) =
  persistent-component-coercion coercion
    (Frame.runtime-frame-weaken R≤S runtime)
persistent-semantic-coercion-weaken R≤S
    (persistent-forall-component coercion runtime) =
  persistent-forall-component coercion
    (Frame.runtime-frame-weaken R≤S runtime)
persistent-semantic-coercion-weaken R≤S
    (persistent-generalized-component coercion runtime) =
  persistent-generalized-component coercion
    (Frame.runtime-frame-weaken R≤S runtime)

persistent-left-function-weaken :
  ∀ {W W′ U U′ θ p q}
    {R : RelatedWorlds.WorldRelation W W′}
    {S : RelatedWorlds.WorldRelation U U′} →
  RelatedWorlds.WorldExtension R S →
  PersistentLeftFunctionProxyBoundary R θ p q →
  PersistentLeftFunctionProxyBoundary S θ p q
persistent-left-function-weaken R≤S
    (persistent-left-function-proxy coercion runtime) =
  persistent-left-function-proxy coercion
    (Frame.runtime-frame-weaken R≤S runtime)
persistent-left-function-weaken R≤S
    (persistent-left-function-component coercion runtime) =
  persistent-left-function-component coercion
    (Frame.runtime-frame-weaken R≤S runtime)

persistent-right-function-weaken :
  ∀ {W W′ U U′ θ′ p q}
    {R : RelatedWorlds.WorldRelation W W′}
    {S : RelatedWorlds.WorldRelation U U′} →
  RelatedWorlds.WorldExtension R S →
  PersistentRightFunctionProxyBoundary R θ′ p q →
  PersistentRightFunctionProxyBoundary S θ′ p q
persistent-right-function-weaken R≤S
    (persistent-right-function-proxy coercion runtime) =
  persistent-right-function-proxy coercion
    (Frame.runtime-frame-weaken R≤S runtime)
persistent-right-function-weaken R≤S
    (persistent-right-function-component coercion runtime) =
  persistent-right-function-component coercion
    (Frame.runtime-frame-weaken R≤S runtime)

persistent-left-forall-weaken :
  ∀ {W W′ U U′ θ c}
    {R : RelatedWorlds.WorldRelation W W′}
    {S : RelatedWorlds.WorldRelation U U′} →
  RelatedWorlds.WorldExtension R S →
  PersistentLeftForallProxyBoundary R θ c →
  PersistentLeftForallProxyBoundary S θ c
persistent-left-forall-weaken R≤S
    (persistent-left-forall-proxy coercion runtime) =
  persistent-left-forall-proxy coercion
    (Frame.runtime-frame-weaken R≤S runtime)
persistent-left-forall-weaken R≤S
    (persistent-left-forall-component coercion runtime) =
  persistent-left-forall-component coercion
    (Frame.runtime-frame-weaken R≤S runtime)

persistent-right-forall-weaken :
  ∀ {W W′ U U′ θ′ c}
    {R : RelatedWorlds.WorldRelation W W′}
    {S : RelatedWorlds.WorldRelation U U′} →
  RelatedWorlds.WorldExtension R S →
  PersistentRightForallProxyBoundary R θ′ c →
  PersistentRightForallProxyBoundary S θ′ c
persistent-right-forall-weaken R≤S
    (persistent-right-forall-proxy coercion runtime) =
  persistent-right-forall-proxy coercion
    (Frame.runtime-frame-weaken R≤S runtime)
persistent-right-forall-weaken R≤S
    (persistent-right-forall-component coercion runtime) =
  persistent-right-forall-component coercion
    (Frame.runtime-frame-weaken R≤S runtime)

persistent-left-generalization-weaken :
  ∀ {W W′ U U′ θ A c}
    {R : RelatedWorlds.WorldRelation W W′}
    {S : RelatedWorlds.WorldRelation U U′} →
  RelatedWorlds.WorldExtension R S →
  PersistentLeftGeneralizationBoundary R θ A c →
  PersistentLeftGeneralizationBoundary S θ A c
persistent-left-generalization-weaken R≤S
    (persistent-left-generalization coercion runtime) =
  persistent-left-generalization coercion
    (Frame.runtime-frame-weaken R≤S runtime)
persistent-left-generalization-weaken R≤S
    (persistent-left-generalization-component coercion runtime) =
  persistent-left-generalization-component coercion
    (Frame.runtime-frame-weaken R≤S runtime)

persistent-right-generalization-weaken :
  ∀ {W W′ U U′ θ′ A c}
    {R : RelatedWorlds.WorldRelation W W′}
    {S : RelatedWorlds.WorldRelation U U′} →
  RelatedWorlds.WorldExtension R S →
  PersistentRightGeneralizationBoundary R θ′ A c →
  PersistentRightGeneralizationBoundary S θ′ A c
persistent-right-generalization-weaken R≤S
    (persistent-right-generalization coercion runtime) =
  persistent-right-generalization coercion
    (Frame.runtime-frame-weaken R≤S runtime)
persistent-right-generalization-weaken R≤S
    (persistent-right-generalization-component coercion runtime) =
  persistent-right-generalization-component coercion
    (Frame.runtime-frame-weaken R≤S runtime)

interpreterNarrowingLeaves : NarrowingLeaves
interpreterNarrowingLeaves =
  record
    { BodyNarrowing = PersistentBodyNarrowing
    ; BodyNarrowingWeaken = persistent-body-weaken
    ; TypeNarrowing = ICN.InterpreterTypeNarrowing
    ; GroundNarrowing = ICN.InterpreterGroundNarrowing
    ; CoercionNarrowing = PersistentSemanticCoercionNarrowing
    ; CoercionNarrowingWeaken =
        persistent-semantic-coercion-weaken
    ; QuotientValueFrame = IQVN.InterpreterQuotientValueFrame
    ; QuotientValueFrameWeaken = IQVN.quotient-value-frame-weaken
    ; QuotientValueFrameSealLink =
        IQVN.quotient-value-frame-seal-link
    ; LeftTaggedBoundary = ICN.LeftTaggedBoundary
    ; RightTaggedBoundary = ICN.RightTaggedBoundary
    ; LeftFunctionProxyBoundary =
        PersistentLeftFunctionProxyBoundary
    ; LeftFunctionProxyBoundaryWeaken =
        persistent-left-function-weaken
    ; RightFunctionProxyBoundary =
        PersistentRightFunctionProxyBoundary
    ; RightFunctionProxyBoundaryWeaken =
        persistent-right-function-weaken
    ; LeftForallProxyBoundary =
        PersistentLeftForallProxyBoundary
    ; LeftForallProxyBoundaryWeaken =
        persistent-left-forall-weaken
    ; RightForallProxyBoundary =
        PersistentRightForallProxyBoundary
    ; RightForallProxyBoundaryWeaken =
        persistent-right-forall-weaken
    ; LeftTypeAbstractionBoundary = ICN.LeftTypeAbstractionBoundary
    ; LeftGeneralizationBoundary =
        PersistentLeftGeneralizationBoundary
    ; LeftGeneralizationBoundaryWeaken =
        persistent-left-generalization-weaken
    ; RightGeneralizationBoundary =
        PersistentRightGeneralizationBoundary
    ; RightGeneralizationBoundaryWeaken =
        persistent-right-generalization-weaken
    }

interpreter-term-no-bullet :
  ∀ {M} →
  InterpreterTerm M →
  N.No• M
interpreter-term-no-bullet =
  Proof.interpreter-term-no-bullet

interpreter-type-abstraction-value :
  ∀ {V} →
  InterpreterTerm (N.Λ V) →
  N.Value V
interpreter-type-abstraction-value =
  Proof.interpreter-type-abstraction-value

interpreter-term-not-blame :
  InterpreterTerm N.blame →
  ⊥
interpreter-term-not-blame =
  Proof.interpreter-term-not-blame

interpreter-term-type-rename :
  ∀ ρ {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameᵗᵐ ρ M)
interpreter-term-type-rename =
  Proof.interpreter-term-type-rename

interpreter-term-type-name-substitute :
  ∀ α {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameᵗᵐ (singleRenameᵗ α) M)
interpreter-term-type-name-substitute α =
  Proof.interpreter-term-type-rename (singleRenameᵗ α)

interpreter-term-rename :
  ∀ ρ {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameˣᵐ ρ M)
interpreter-term-rename =
  Proof.interpreter-term-rename

interpreter-term-weaken :
  ∀ {M} →
  InterpreterTerm M →
  InterpreterTerm (N.renameˣᵐ suc M)
interpreter-term-weaken =
  Proof.interpreter-term-rename suc

interpreter-term-substitute :
  ∀ {σ M} →
  (∀ x → InterpreterTerm (σ x)) →
  InterpreterTerm M →
  InterpreterTerm (N.substˣᵐ σ M)
interpreter-term-substitute =
  Proof.interpreter-term-substitute

interpreter-narrowing-source-term :
  ∀ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTerm N
interpreter-narrowing-source-term =
  ShapeProof.shape-source-interpreter-term

interpreter-narrowing-target-term :
  ∀ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTerm N′
interpreter-narrowing-target-term =
  ShapeProof.shape-target-interpreter-term

interpreter-narrowing-type-rename :
  ∀ ρ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.renameᵗᵐ ρ N)
    (N.renameᵗᵐ ρ N′)
interpreter-narrowing-type-rename =
  ShapeProof.shape-type-rename

interpreter-narrowing-type-name-substitute :
  ∀ α {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.renameᵗᵐ (singleRenameᵗ α) N)
    (N.renameᵗᵐ (singleRenameᵗ α) N′)
interpreter-narrowing-type-name-substitute α =
  ShapeProof.shape-type-rename (singleRenameᵗ α)

interpreter-narrowing-rename :
  ∀ ρ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.renameˣᵐ ρ N)
    (N.renameˣᵐ ρ N′)
interpreter-narrowing-rename =
  ShapeProof.shape-rename

interpreter-narrowing-weaken :
  ∀ {N N′} →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.renameˣᵐ suc N)
    (N.renameˣᵐ suc N′)
interpreter-narrowing-weaken =
  ShapeProof.shape-rename suc

interpreter-narrowing-substitute :
  ∀ {σ σ′ N N′} →
  (∀ x → InterpreterTermShape (σ x) (σ′ x)) →
  InterpreterTermShape N N′ →
  InterpreterTermShape
    (N.substˣᵐ σ N)
    (N.substˣᵐ σ′ N′)
interpreter-narrowing-substitute =
  ShapeProof.shape-substitute

open RelatedWorlds

open-interpreter-narrowing-world-weaken :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ γ N N′ A B p}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
  OpenInterpreterTermNarrowing
    S Φ Δᴸ Δᴿ ρ γ N N′ A B p
open-interpreter-narrowing-world-weaken =
  Proof.open-interpreter-narrowing-world-weaken

open-interpreter-narrowing-source-typing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ N N′ A B p}
    {R : WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
  TT._∣_∣_⊢_⦂_
    Δᴸ (NTI.leftStoreⁱ ρ) (NTI.leftCtxⁱ γ) N A
open-interpreter-narrowing-source-typing =
  Proof.open-interpreter-narrowing-source-typing

open-interpreter-narrowing-target-typing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γ N N′ A B p}
    {R : WorldRelation W W′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γ N N′ A B p →
  TT._∣_∣_⊢_⦂_
    Δᴿ (NTI.rightStoreⁱ ρ) (NTI.rightCtxⁱ γ) N′ B
open-interpreter-narrowing-target-typing =
  Proof.open-interpreter-narrowing-target-typing

module InterpreterValues =
  ValueNarrowing interpreterNarrowingLeaves

open InterpreterValues
