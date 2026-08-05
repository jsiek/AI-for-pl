module Narrowing.InterpreterCoercionNarrowing where

-- File Charter:
--   * Defines reduction-free type and indexed operational coercion evidence.
--   * Retains static imprecision contexts, type contexts, relational stores,
--     and endpoint type precision throughout recursive coercion simulation.
--   * Hides those indices only at persistent semantic-value leaves.

open import Coercions using
  (Coercion; genᵈ; id-onlyᵈ; tag-or-idᵈ; _↦_; `∀; gen)
open import Conversion using (ConcealConversion; RevealConversion)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter using (Name)
import NuTermImprecision as NTI
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import QuotientedTermImprecision using
  (PairedCast; QuotientWideningPair)
open import TermTyping using (CastMode; SealModeStore★)
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

data CoercionAction : Set where
  skip-coercion :
    CoercionAction

  apply-coercion :
    Coercion →
    CoercionAction

data OperationalCoercionNarrowing
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : NTI.StoreImp Φ Δᴸ Δᴿ) :
    CoercionAction → CoercionAction →
    {A A′ B B′ : Ty} →
    Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
    Set₁ where

  paired-coercion-action :
    ∀ {c c′ A A′ B B′ p q} →
    PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) (apply-coercion c′)
      {A} {A′} {B} {B′} p q

  left-narrowing-action :
    ∀ {c μ A B B′ p q} →
    CastMode μ →
    SealModeStore★ μ (NTI.leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) skip-coercion
      {A} {B′} {B} {B′} p q

  left-widening-action :
    ∀ {c μ A B B′ p q} →
    CastMode μ →
    SealModeStore★ μ (NTI.leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) skip-coercion
      {A} {B′} {B} {B′} p q

  right-narrowing-action :
    ∀ {c′ μ′ A A′ B′ p q} →
    CastMode μ′ →
    SealModeStore★ μ′ (NTI.rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {A} {B′} p q

  right-widening-action :
    ∀ {c′ μ′ A A′ B′ p q} →
    CastMode μ′ →
    SealModeStore★ μ′ (NTI.rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {A} {B′} p q

  right-static-widening-action :
    ∀ {c′ μ′ A A′ B′ p q} →
    SealModeStore★ μ′ (NTI.rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
      ⊢ c′ ∶ A′ ⊑ B′ →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {A} {B′} p q

  left-reveal-action :
    ∀ {c μ α X A B B′ p q} →
    RevealConversion μ Δᴸ (NTI.leftStoreⁱ ρ)
      α X c A B →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) skip-coercion
      {A} {B′} {B} {B′} p q

  left-conceal-action :
    ∀ {c μ α X A B B′ p q} →
    ConcealConversion μ Δᴸ (NTI.leftStoreⁱ ρ)
      α X c A B →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) skip-coercion
      {A} {B′} {B} {B′} p q

  right-reveal-action :
    ∀ {c′ μ′ β X′ A A′ B′ p q} →
    RevealConversion μ′ Δᴿ (NTI.rightStoreⁱ ρ)
      β X′ c′ A′ B′ →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {A} {B′} p q

  right-conceal-action :
    ∀ {c′ μ′ β X′ A A′ B′ p q} →
    ConcealConversion μ′ Δᴿ (NTI.rightStoreⁱ ρ)
      β X′ c′ A′ B′ →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {A} {B′} p q

-- Component casts exposed by an inert proxy are not always themselves a
-- `PairedCast`.  In particular, the domains of paired function widenings are
-- paired narrowings.  This relation retains those executable component plans
-- once, when the proxy is constructed.
data ComponentCoercionNarrowing
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : NTI.StoreImp Φ Δᴸ Δᴿ) :
    CoercionAction → CoercionAction →
    {A A′ B B′ : Ty} →
    Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
    Set₁ where

  operational-component :
    ∀ {left right A A′ B B′ p q} →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      left right {A} {A′} {B} {B′} p q →
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      left right {A} {A′} {B} {B′} p q

  paired-narrowing-component :
    ∀ {c c′ μ μ′ A A′ B B′ p q} →
    CastMode μ →
    SealModeStore★ μ (NTI.leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
    CastMode μ′ →
    SealModeStore★ μ′ (NTI.rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) (apply-coercion c′)
      {A} {A′} {B} {B′} p q

  paired-widening-component :
    ∀ {c c′ μ μ′ A A′ B B′ p q} →
    CastMode μ →
    SealModeStore★ μ (NTI.leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
    CastMode μ′ →
    SealModeStore★ μ′ (NTI.rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) (apply-coercion c′)
      {A} {A′} {B} {B′} p q

  right-static-narrowing-component :
    ∀ {c′ μ′ A A′ B′ p q} →
    SealModeStore★ μ′ (NTI.rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
      ⊢ c′ ∶ A′ ⊒ B′ →
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {A} {B′} p q

data OperationalDownCoercionNarrowing
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : NTI.StoreImp Φ Δᴸ Δᴿ)
    (d d′ : Coercion)
    {C C′ D D′ : Ty}
    (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) : Set₁ where

  paired-id-down-action :
    id-onlyᵈ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
      ⊢ d ∶ C ⊒ D →
    id-onlyᵈ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
      ⊢ d′ ∶ C′ ⊒ D′ →
    OperationalDownCoercionNarrowing
      Φ Δᴸ Δᴿ ρ d d′ pC qD

  paired-generalized-down-action :
    genᵈ tag-or-idᵈ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
      ⊢ d ∶ C ⊒ D →
    genᵈ tag-or-idᵈ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
      ⊢ d′ ∶ C′ ⊒ D′ →
    OperationalDownCoercionNarrowing
      Φ Δᴸ Δᴿ ρ d d′ pC qD

data OperationalUpCoercionNarrowing
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : NTI.StoreImp Φ Δᴸ Δᴿ)
    (u u′ : Coercion)
    {D D′ A A′ : Ty}
    (qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ)
    (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) : Set₁ where

  paired-quotient-up-action :
    QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
    OperationalUpCoercionNarrowing
      Φ Δᴸ Δᴿ ρ u u′ qD pA

data SemanticCoercionNarrowing
    (c c′ : Coercion) : Set₁ where
  semantic-coercion-narrowing :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {A A′ B B′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) (apply-coercion c′) p q →
    SemanticCoercionNarrowing c c′

LeftTaggedBoundary : ∀ {G} → Ground G → Set₁
LeftTaggedBoundary {G} gG =
  InterpreterTypeNarrowing G ★

RightTaggedBoundary : ∀ {G} → Ground G → Set₁
RightTaggedBoundary {G} gG =
  InterpreterTypeNarrowing ★ G

data LeftFunctionProxyBoundary
    (p q : Coercion) : Set₁ where
  left-function-proxy-boundary :
    ∀ {Φ Δᴸ Δᴿ ρ A A′ B B′ pA pB} →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (p ↦ q)) skip-coercion
      {A} {A′} {B} {B′} pA pB →
    LeftFunctionProxyBoundary p q

data RightFunctionProxyBoundary
    (p q : Coercion) : Set₁ where
  right-function-proxy-boundary :
    ∀ {Φ Δᴸ Δᴿ ρ A A′ B B′ pA pB} →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (p ↦ q))
      {A} {A′} {B} {B′} pA pB →
    RightFunctionProxyBoundary p q

data LeftForallProxyBoundary (c : Coercion) : Set₁ where
  left-forall-proxy-boundary :
    ∀ {Φ Δᴸ Δᴿ ρ A A′ B B′ p q} →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (`∀ c)) skip-coercion
      {A} {A′} {B} {B′} p q →
    LeftForallProxyBoundary c

data RightForallProxyBoundary (c : Coercion) : Set₁ where
  right-forall-proxy-boundary :
    ∀ {Φ Δᴸ Δᴿ ρ A A′ B B′ p q} →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (`∀ c))
      {A} {A′} {B} {B′} p q →
    RightForallProxyBoundary c

data LeftTypeAbstractionBoundary (X : Name) : Set₁ where
  left-type-abstraction-boundary :
    ∀ {A B} →
    InterpreterTypeNarrowing (`∀ A) B →
    LeftTypeAbstractionBoundary X

data LeftGeneralizationBoundary
    (A : Ty) (c : Coercion) : Set₁ where
  left-generalization-boundary :
    ∀ {Φ Δᴸ Δᴿ ρ B B′ C C′ p q} →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion (gen A c)) skip-coercion
      {B} {B′} {C} {C′} p q →
    LeftGeneralizationBoundary A c

data RightGeneralizationBoundary
    (A : Ty) (c : Coercion) : Set₁ where
  right-generalization-boundary :
    ∀ {Φ Δᴸ Δᴿ ρ B B′ C C′ p q} →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion (gen A c))
      {B} {B′} {C} {C′} p q →
    RightGeneralizationBoundary A c
