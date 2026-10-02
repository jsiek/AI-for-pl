{-# OPTIONS --safe #-}

module proof.DGG.notes.TargetInstantiationMeasureProbe where

-- File Charter:
--   * Strict-probes the private well-founded measure for target
--     instantiation catch-up before the live proof is written.
--   * Covers ordinary cast descent, beta-inst residual descent, target
--     all/gen cast descent, conversion-frame descent, and CTI source-wrapper
--     descent, including reveal-rebase frame entry and conceal-rebase pop.
--   * Keeps the measure private to proof recursion; the public catch-up
--     interfaces remain direct and fuel-free.
--   * Contains no term-imprecision changes and no legacy CtxImp surface.

open import Data.Nat using (ℕ; suc; _<_; _≤_; _+_; _*_; _^_)
import Data.Nat.Induction as NatInduction
open import Data.Nat.Properties using
  ( n<1+n; ≤-<-trans; +-monoʳ-<; m<n+m; ≤-trans )
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (_×_; _,_)
import Data.Product.Relation.Binary.Lex.Strict as ProductLex
open import Data.Sum.Base using (inj₁; inj₂)
import Induction.WellFounded as WF
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
  renaming (subst to subst≡)

open +-*-Solver using (solve; _:+_; _:*_; con)
  renaming (_:=_ to _:=ᵉ_)


------------------------------------------------------------------------
-- Private lexicographic measure
------------------------------------------------------------------------

record InstantiationMeasure : Set where
  constructor instantiation-measure
  field
    castMass : ℕ
    nameFrames : ℕ
    conversionPotential : ℕ
    spineLength : ℕ
    sourceDerivationSize : ℕ


MeasureTuple : Set
MeasureTuple = ℕ × (ℕ × (ℕ × (ℕ × ℕ)))


measureTuple : InstantiationMeasure → MeasureTuple
measureTuple
    (instantiation-measure mass names potential length source-size) =
  mass , (names , (potential , (length , source-size)))


_<tuple_ : MeasureTuple → MeasureTuple → Set
_<tuple_ =
  ProductLex.×-Lex _≡_ _<_
    (ProductLex.×-Lex _≡_ _<_
      (ProductLex.×-Lex _≡_ _<_
        (ProductLex.×-Lex _≡_ _<_ _<_)))


infix 4 _<measure_

_<measure_ : InstantiationMeasure → InstantiationMeasure → Set
left <measure right = measureTuple left <tuple measureTuple right


measure-well-founded : WF.WellFounded _<measure_
measure-well-founded measure =
  pullback (tuple-well-founded (measureTuple measure))
  where
  tuple-well-founded : WF.WellFounded _<tuple_
  tuple-well-founded =
    ProductLex.×-wellFounded NatInduction.<-wellFounded
      (ProductLex.×-wellFounded NatInduction.<-wellFounded
        (ProductLex.×-wellFounded NatInduction.<-wellFounded
          (ProductLex.×-wellFounded NatInduction.<-wellFounded
            NatInduction.<-wellFounded)))

  pullback : ∀ {current}
    → Acc _<tuple_ (measureTuple current)
    → Acc _<measure_ current
  pullback (acc smaller) =
    acc (λ {previous} previous< →
      pullback (smaller {y = measureTuple previous} previous<))


measure-cast-mass< : ∀ {m m′ n n′ p p′ l l′ s s′}
  → m < m′
  → instantiation-measure m n p l s <measure
      instantiation-measure m′ n′ p′ l′ s′
measure-cast-mass< mass< = inj₁ mass<


measure-name-frames< : ∀ {m n n′ p p′ l l′ s s′}
  → n < n′
  → instantiation-measure m n p l s <measure
      instantiation-measure m n′ p′ l′ s′
measure-name-frames< names< = inj₂ (refl , inj₁ names<)


measure-conversion-potential< : ∀ {m n p p′ l l′ s s′}
  → p < p′
  → instantiation-measure m n p l s <measure
      instantiation-measure m n p′ l′ s′
measure-conversion-potential< potential< =
  inj₂ (refl , inj₂ (refl , inj₁ potential<))


measure-spine-length< : ∀ {m n p l l′ s s′}
  → l < l′
  → instantiation-measure m n p l s <measure
      instantiation-measure m n p l′ s′
measure-spine-length< length< =
  inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ length<)))


measure-source-derivation< : ∀ {m n p l s s′}
  → s < s′
  → instantiation-measure m n p l s <measure
      instantiation-measure m n p l s′
measure-source-derivation< source< =
  inj₂
    (refl , inj₂
      (refl , inj₂
        (refl , inj₂ (refl , source<))))


------------------------------------------------------------------------
-- Primary cast-mass transitions
------------------------------------------------------------------------

ordinary-child-cast-decreases : ∀ child rest names potential length source
  → instantiation-measure (child + rest) names potential length source
      <measure
    instantiation-measure (suc child + rest) names potential length source
ordinary-child-cast-decreases child rest names potential length source =
  measure-cast-mass<
    (Data.Nat.Properties.+-monoˡ-< rest (n<1+n child))


inst-residual-cast-decreases : ∀ residual body rest
    names potential length source
  → residual ≤ body
  → instantiation-measure (residual + rest)
      names potential length source
      <measure
    instantiation-measure (suc body + rest)
      names potential length source
inst-residual-cast-decreases residual body rest
    names potential length source residual≤body =
  measure-cast-mass<
    (Data.Nat.Properties.+-monoˡ-< rest
      (≤-<-trans residual≤body (n<1+n body)))


all-value-cast-decreases : ∀ opened body rest
    names potential length source
  → opened ≤ body
  → instantiation-measure (opened + rest)
      names potential length source
      <measure
    instantiation-measure (suc body + rest)
      names potential length source
all-value-cast-decreases = inst-residual-cast-decreases


gen-value-cast-decreases : ∀ body rest names potential length source
  → instantiation-measure (body + rest)
      names potential length source
      <measure
    instantiation-measure (suc body + rest)
      names potential length source
gen-value-cast-decreases body rest names potential length source =
  measure-cast-mass<
    (Data.Nat.Properties.+-monoˡ-< rest (n<1+n body))


------------------------------------------------------------------------
-- Administrative rank transitions
------------------------------------------------------------------------

power-of-three-positive : ∀ n → 1 ≤ 3 ^ n
power-of-three-positive Data.Nat.zero = Data.Nat.s≤s Data.Nat.z≤n
power-of-three-positive (Data.Nat.suc n) =
  ≤-trans (power-of-three-positive n)
    (Data.Nat.Properties.m≤m+n (3 ^ n) (2 * 3 ^ n))


lambda-name-frame-decreases : ∀ mass names potential length source
  → instantiation-measure mass names potential length source
      <measure
    instantiation-measure mass (suc names) potential length source
lambda-name-frame-decreases mass names potential length source =
  measure-name-frames< (n<1+n names)


conversion-frame-potential-decreases : ∀ mass wrappers names potential
    length source
  → instantiation-measure mass names
      (wrappers * 3 ^ names + potential) length source
      <measure
    instantiation-measure mass names
      (wrappers * 3 ^ names + (3 ^ names + potential)) length source
conversion-frame-potential-decreases mass wrappers names potential
    length source =
  measure-conversion-potential<
    (Data.Nat.Properties.+-monoʳ-<
      (wrappers * 3 ^ names)
      (m<n+m potential (power-of-three-positive names)))


parent-conversion-normalize : ∀ wrappers names potential
  → suc wrappers * 3 ^ suc names + potential ≡
      wrappers * 3 ^ suc names +
        (3 ^ names + (3 ^ names + (3 ^ names + potential)))
parent-conversion-normalize wrappers names potential = solve 3
  (λ w power p →
    ((con 1 :+ w) :* (power :+ (power :+ (power :+ con 0))) :+ p)
      :=ᵉ
    (w :* (power :+ (power :+ (power :+ con 0))) :+
      (power :+ (power :+ (power :+ p)))))
  refl wrappers (3 ^ names) potential


two-generated-conversions-decrease : ∀ wrappers names potential
  → wrappers * 3 ^ suc names +
      (3 ^ names + (3 ^ names + potential))
    < suc wrappers * 3 ^ suc names + potential
two-generated-conversions-decrease wrappers names potential =
  subst≡
    (λ q → wrappers * 3 ^ suc names +
      (3 ^ names + (3 ^ names + potential)) < q)
    (sym (parent-conversion-normalize wrappers names potential))
    (Data.Nat.Properties.+-monoʳ-<
      (wrappers * 3 ^ suc names)
      (m<n+m (3 ^ names + (3 ^ names + potential))
        (power-of-three-positive names)))


reveal-conceal-expansion-decreases : ∀ mass wrappers names potential
    length source
  → instantiation-measure mass (suc names)
      (wrappers * 3 ^ suc names +
        (3 ^ names + (3 ^ names + potential))) length source
      <measure
    instantiation-measure mass (suc names)
      (suc wrappers * 3 ^ suc names + potential) length source
reveal-conceal-expansion-decreases mass wrappers names potential
    length source =
  measure-conversion-potential<
    (two-generated-conversions-decrease wrappers names potential)


ordinary-frame-consumption-decreases : ∀ mass names potential length source
  → instantiation-measure mass names potential length source <measure
    instantiation-measure mass names potential (suc length) source
ordinary-frame-consumption-decreases mass names potential length source =
  measure-spine-length< (n<1+n length)


------------------------------------------------------------------------
-- Structural CTI descent, including gamma-carried frame motion
------------------------------------------------------------------------

source-wrapper-decreases : ∀ mass names potential length source
  → instantiation-measure mass names potential length source <measure
    instantiation-measure mass names potential length (suc source)
source-wrapper-decreases mass names potential length source =
  measure-source-derivation< (n<1+n source)


spine-to-name-phase-decreases : ∀ mass names potential length source
  → instantiation-measure mass names potential length source <measure
    instantiation-measure mass names potential length (suc source)
spine-to-name-phase-decreases = source-wrapper-decreases


reveal-rebase-frame-entry-decreases : ∀ mass names potential length source
  → instantiation-measure mass names potential length source <measure
    instantiation-measure mass names potential length (suc source)
reveal-rebase-frame-entry-decreases = source-wrapper-decreases


conceal-rebase-frame-pop-decreases : ∀ mass names potential length source
  → instantiation-measure mass names potential length source <measure
    instantiation-measure mass names potential length (suc source)
conceal-rebase-frame-pop-decreases = source-wrapper-decreases


-- The frame stack is carried by gamma and controls which CTI constructors
-- are reachable.  It is deliberately not a numeric measure component:
-- reveal entry can increase its length, whereas both entry and the matching
-- conceal pop recurse through a strict CTI subderivation.
