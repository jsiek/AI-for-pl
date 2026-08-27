{-# OPTIONS --safe #-}

module proof.DGG.SimPrimitiveValuesLemma where

-- File Charter:
--   * Proves primitive value/value simulation by canonical forms for natural
--     and Boolean operands.
--   * Identifies each target value with its related source constant and takes
--     the matching target delta step.
--   * Closes the value-level primitive obligation without parameters.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Primitives using (κℕ; κ𝔹; δ-add; δ-and)
open import CastTerms using ($; _⊕[_]_)
open import Reduction using
  ( keep
  ; pure-step
  ; δ-⊕
  ; _—→[_]⟨_⟩_
  ; _∎[]
  ) renaming ([] to []ˢ; _∷_ to _∷ˢ_)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecisionTyping using (target-typing)
open import proof.DGG.SimPrimitiveValuesDef using
  (SimPrimitiveValuesᵀ)
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence using
  (evolutions-refl; evolutions-step-both)
open import proof.TypeSafety.Progress using
  (canonical-ℕ; canonical-𝔹; nv-const; bv-const)


sim-primitive-values : SimPrimitiveValuesᵀ
sim-primitive-values left-related right-related r left-value right-value
    δ-add
    with canonical-ℕ left-value (target-typing left-related)
       | canonical-ℕ right-value (target-typing right-related)
sim-primitive-values left-related right-related r left-value right-value
    δ-add
    | nv-const refl | nv-const refl
    with left-related | right-related
sim-primitive-values left-related right-related r left-value right-value
    δ-add
    | nv-const refl | nv-const refl
    | CTI.κ⊑κ² ._ p | CTI.κ⊑κ² ._ q =
  _ , _ , keep ∷ˢ []ˢ , _ , _ , r ,
  ($ _ ⊕[ _ ] $ _
    —→[ keep ]⟨ pure-step (δ-⊕ δ-add) ⟩
   $ _ ∎[]) ,
  evolutions-step-both refl refl evolution-keep evolutions-refl ,
  CTI.κ⊑κ² _ r

sim-primitive-values left-related right-related r left-value right-value
    δ-and
    with canonical-𝔹 left-value (target-typing left-related)
       | canonical-𝔹 right-value (target-typing right-related)
sim-primitive-values left-related right-related r left-value right-value
    δ-and
    | bv-const refl | bv-const refl
    with left-related | right-related
sim-primitive-values left-related right-related r left-value right-value
    δ-and
    | bv-const refl | bv-const refl
    | CTI.κ⊑κ² ._ p | CTI.κ⊑κ² ._ q =
  _ , _ , keep ∷ˢ []ˢ , _ , _ , r ,
  ($ _ ⊕[ _ ] $ _
    —→[ keep ]⟨ pure-step (δ-⊕ δ-and) ⟩
   $ _ ∎[]) ,
  evolutions-step-both refl refl evolution-keep evolutions-refl ,
  CTI.κ⊑κ² _ r
