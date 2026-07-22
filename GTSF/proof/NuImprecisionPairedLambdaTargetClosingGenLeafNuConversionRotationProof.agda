module
  proof.NuImprecisionPairedLambdaTargetClosingGenLeafNuConversionRotationProof
  where

-- File Charter:
--   * Reduces generic-terminal `ν` conversion rotation to the exact semantic
--     paired-conversion rotation through one source-only allocation.
--   * Performs ambient-prefix transport, constructs the generic narrowing
--     value, and applies the source runtime-bullet rule before the conversion.
--   * Contains no paired-conversion semantic implementation, postulate, hole,
--     permissive option, or broad simulation import.

open import Agda.Builtin.Equality using (refl)
import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ν
  ; ⊑-src-wf
  )
import NarrowWiden as NW
open import NuTermImprecision using
  ( leftStoreⁱ
  ; leftStoreⁱ-lift-left
  ; lift-left-ctx-[]
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-left
  )
open import NuTerms using
  ( no•-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; conv⊑convᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; paired-conversion
  ; α⊑ᵀ
  )
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import TermTyping using (_∣_∣_⊢_⦂_; ⊢•)
open import proof.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import proof.NuImprecisionPairedLambdaTargetClosingGenLeafNuConversionRotationDef
  using (PairedLambdaTargetClosingGenLeafNuConversionRotationᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  using
  (PairedLambdaTargetClosingNuPairedConversionRotationᵀ)
open import proof.TypePreservation using (term-weaken)


paired-lambda-target-closing-gen-leaf-ν-conversion-rotation-proofᵀ :
  PairedLambdaTargetClosingNuPairedConversionRotationᵀ →
  PairedLambdaTargetClosingGenLeafNuConversionRotationᵀ
paired-lambda-target-closing-gen-leaf-ν-conversion-rotation-proofᵀ
    rotate-conversion prefix vV noV vN′ noN′ mode seal★ hA occ-g
    g⊢ gⁿ V⊑N′ occ-r r h⇑Aν liftν lift∀ conversion
    with rotate-conversion h⇑Aν liftν occ-r conversion
paired-lambda-target-closing-gen-leaf-ν-conversion-rotation-proofᵀ
    rotate-conversion prefix vV noV vN′ noN′ mode seal★ hA occ-g
    g⊢ gⁿ V⊑N′ occ-r r h⇑Aν liftν lift∀ conversion
    | u , rotated-conversion =
  u , conv⊑convᵀ (paired-conversion rotated-conversion) bullet-relation
  where
  generic-value = vV ⟨ C.gen _ _ ⟩

  generic-no-bullet = no•-⟨⟩ noV

  generic-relation₀ =
    cast⊒⊑ᵀ mode seal★
      (C.cast-gen hA occ-g g⊢ , NW.gen gⁿ)
      V⊑N′ (ν _ occ-r r)

  generic-relation =
    allocation-prefixᵀ prefix generic-relation₀
      (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
        generic-no-bullet
        (nu-term-imprecision-source-typing generic-relation₀))
      (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
        noN′ (nu-term-imprecision-target-typing generic-relation₀))

  source-bullet-typing =
    subst
      (λ Σ → _ ∣ (_ , _) ∷ Σ ∣ [] ⊢ _ ⦂ _)
      (sym (leftStoreⁱ-lift-left liftν))
      (⊢• refl refl (⊑-src-wf r) generic-value generic-no-bullet
        (nu-term-imprecision-source-typing generic-relation))

  target-typing =
    subst
      (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
      (sym (rightStoreⁱ-lift-left liftν))
      (nu-term-imprecision-target-typing generic-relation)

  bullet-relation =
    α⊑ᵀ generic-value generic-no-bullet h⇑Aν liftν
      lift-left-ctx-[] generic-relation source-bullet-typing target-typing
