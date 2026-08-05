module Narrowing.InterpreterReachableCoercionNarrowing where

-- File Charter:
--   * Distinguishes independently executable coercion components from the
--     larger component relation retained inside proxy origins.
--   * Excludes detached paired components, whose outer compatibility evidence
--     must be consumed by the enclosing proxy or quotient observer.
--   * Proves that every one-sided component is independently reachable.
--   * Contains only structural coercion metatheory.

open import Coercions using (Coercion; _↦_)
open import Conversion using
  (conceal-fun; reveal-fun)
open import Data.Product using (_×_; _,_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; _↦_)
open import Narrowing.InterpreterCoercionNarrowing
import NuTermImprecision as NTI
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import QuotientedTermImprecision using
  (PairedConversion; paired-conversion)
open import TermTyping using (SealModeStore★)
open import Types


data ReachableComponentCoercionNarrowing
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : NTI.StoreImp Φ Δᴸ Δᴿ) :
    CoercionAction → CoercionAction →
    {A A′ B B′ : Ty} →
    Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
    Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ →
    Set₁ where

  reachable-paired-conversion :
    ∀ {c c′ A A′ B B′ p q} →
    PairedConversion Φ Δᴸ Δᴿ ρ
      c c′ {A} {A′} {B} {B′} p q →
    ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) (apply-coercion c′)
      {A} {A′} {B} {B′} p q

  reachable-left-operational :
    ∀ {c A A′ B B′ p q} →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) skip-coercion
      {A} {A′} {B} {B′} p q →
    ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      (apply-coercion c) skip-coercion
      {A} {A′} {B} {B′} p q

  reachable-right-operational :
    ∀ {c′ A A′ B B′ p q} →
    OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {B} {B′} p q →
    ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {B} {B′} p q

  reachable-right-static-narrowing :
    ∀ {c′ μ′ A A′ B′ p q} →
    SealModeStore★ μ′ (NTI.rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
    ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′)
      {A} {A′} {A} {B′} p q


reachable-component :
  ∀ {Φ Δᴸ Δᴿ ρ left right A A′ B B′ p q} →
  ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    left right {A} {A′} {B} {B′} p q →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    left right {A} {A′} {B} {B′} p q
reachable-component
    (reachable-paired-conversion conversion) =
  operational-component
    (paired-coercion-action (paired-conversion conversion))
reachable-component (reachable-left-operational action) =
  operational-component action
reachable-component (reachable-right-operational action) =
  operational-component action
reachable-component
    (reachable-right-static-narrowing seal target) =
  right-static-narrowing-component seal target


left-component-reachable :
  ∀ {Φ Δᴸ Δᴿ ρ c A A′ B B′ p q} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion c) skip-coercion
    {A} {A′} {B} {B′} p q →
  ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion c) skip-coercion
    {A} {A′} {B} {B′} p q
left-component-reachable
    (operational-component action) =
  reachable-left-operational action


right-component-reachable :
  ∀ {Φ Δᴸ Δᴿ ρ c′ A A′ B B′ p q} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    skip-coercion (apply-coercion c′)
    {A} {A′} {B} {B′} p q →
  ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    skip-coercion (apply-coercion c′)
    {A} {A′} {B} {B′} p q
right-component-reachable
    (operational-component action) =
  reachable-right-operational action
right-component-reachable
    (right-static-narrowing-component seal target) =
  reachable-right-static-narrowing seal target


paired-conversion-function-components-reachable :
  ∀ {Φ Δᴸ Δᴿ ρ c d c′ d′
      A A′ B B′ C C′ D D′ pA pB pC pD} →
  ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (c ↦ d)) (apply-coercion (c′ ↦ d′))
    {A ⇒ B} {A′ ⇒ B′} {C ⇒ D} {C′ ⇒ D′}
    (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
  ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion c) (apply-coercion c′) pC pA
  ×
  ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion d) (apply-coercion d′) pB pD
paired-conversion-function-components-reachable
    (reachable-paired-conversion
      (QuotientedTermImprecision.paired-reveal link
        (reveal-fun source-domain source-codomain)
        (reveal-fun target-domain target-codomain))) =
  reachable-paired-conversion
    (QuotientedTermImprecision.paired-conceal
      link source-domain target-domain) ,
  reachable-paired-conversion
    (QuotientedTermImprecision.paired-reveal
      link source-codomain target-codomain)
paired-conversion-function-components-reachable
    (reachable-paired-conversion
      (QuotientedTermImprecision.paired-conceal link
        (conceal-fun source-domain source-codomain)
        (conceal-fun target-domain target-codomain))) =
  reachable-paired-conversion
    (QuotientedTermImprecision.paired-reveal
      link source-domain target-domain) ,
  reachable-paired-conversion
    (QuotientedTermImprecision.paired-conceal
      link source-codomain target-codomain)
