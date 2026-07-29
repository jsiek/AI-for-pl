module InterpreterCoercionNarrowing where

-- File Charter:
--   * Defines reduction-free type and coercion evidence used by the direct
--     interpreter narrowing relation.
--   * Hides static type contexts and stores only at the semantic-value leaves.
--   * Retains the existing typed paired-cast certificate instead of replacing
--     it by an unrestricted relation on raw coercions.

open import Coercions using (Coercion; _↦_; `∀; gen)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
import NuTermImprecision as NTI
open import QuotientedTermImprecision using (PairedCast)
open import Types

data InterpreterTypeNarrowing (A B : Ty) : Set₁ where
  type-narrowing :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
    InterpreterTypeNarrowing A B

data InterpreterGroundNarrowing :
    ∀ {G H} → Ground G → Ground H → Set₁ where
  ground-narrowing :
    ∀ {G H} {gG : Ground G} {gH : Ground H} →
    InterpreterTypeNarrowing G H →
    InterpreterGroundNarrowing gG gH

data InterpreterCoercionNarrowing
    (c c′ : Coercion) : Set₁ where
  paired-coercion-narrowing :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {A A′ B B′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
    InterpreterCoercionNarrowing c c′

LeftTaggedBoundary : ∀ {G} → Ground G → Set₁
LeftTaggedBoundary {G} gG =
  InterpreterTypeNarrowing G ★

RightTaggedBoundary : ∀ {G} → Ground G → Set₁
RightTaggedBoundary {G} gG =
  InterpreterTypeNarrowing ★ G

data LeftFunctionProxyBoundary
    (p q : Coercion) : Set₁ where
  left-function-proxy-boundary :
    ∀ {c} →
    InterpreterCoercionNarrowing (p ↦ q) c →
    LeftFunctionProxyBoundary p q

data RightFunctionProxyBoundary
    (p q : Coercion) : Set₁ where
  right-function-proxy-boundary :
    ∀ {c} →
    InterpreterCoercionNarrowing c (p ↦ q) →
    RightFunctionProxyBoundary p q

data LeftForallProxyBoundary (c : Coercion) : Set₁ where
  left-forall-proxy-boundary :
    ∀ {d} →
    InterpreterCoercionNarrowing (`∀ c) d →
    LeftForallProxyBoundary c

data RightForallProxyBoundary (c : Coercion) : Set₁ where
  right-forall-proxy-boundary :
    ∀ {d} →
    InterpreterCoercionNarrowing d (`∀ c) →
    RightForallProxyBoundary c

data LeftGeneralizationBoundary
    (A : Ty) (c : Coercion) : Set₁ where
  left-generalization-boundary :
    ∀ {d} →
    InterpreterCoercionNarrowing (gen A c) d →
    LeftGeneralizationBoundary A c

data RightGeneralizationBoundary
    (A : Ty) (c : Coercion) : Set₁ where
  right-generalization-boundary :
    ∀ {d} →
    InterpreterCoercionNarrowing d (gen A c) →
    RightGeneralizationBoundary A c
