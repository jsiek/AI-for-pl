module
  proof.NuImprecisionPairedLambdaTargetClosingUpGenLeafClosingProof
  where

-- File Charter:
--   * Proves the full quotient gen-down/gen closing theorem by its outer
--     precision index.
--   * Handles the source-only `ν` branch constructively using the canonical
--     paired-conversion rotation, leaving only the paired-`∀ⁱ` branch as a
--     fused semantic dependency.
--   * Retains the exact target-closing handler adapter.
--   * Contains no postulate, hole, permissive option, broad simulation
--     import, or recursive frame-closing dependency.

open import Agda.Builtin.Equality using (refl)
import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; genᵈ
  ; tag-or-idᵈ
  )
open import Conversion using (reveal-all)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  ; ⊑-src-wf
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-left
  ; lift-left-ctx-[]
  ; rightStoreⁱ
  ; rightStoreⁱ-lift-left
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; allocation-prefixᵀ
  ; conv↑⊑ᵀ
  ; conv⊑convᵀ
  ; gen-down⊑gen-downᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; paired-conversion
  ; up⊑upᵀ
  ; α⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import TermTyping using (_∣_∣_⊢_⦂_; ⊢•)
open import Types using (Ty; TyCtx; `∀)
open import proof.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpGenLeafClosingDef
  using (PairedLambdaTargetClosingUpGenLeafClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  using (PairedLambdaTargetClosingNuPairedConversionRotationᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpGenLeafAllIndexClosingDef
  using (PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ)
open import proof.TypePreservation using (term-weaken)


paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ :
  PairedLambdaTargetClosingNuPairedConversionRotationᵀ →
  PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ →
  PairedLambdaTargetClosingUpGenLeafClosingᵀ
paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ
    rotate all-closing
    vM noM vM′ noM′ inert-d′ inert-u′ d⊒ d′⊒ M⊑M′
    qD widening (∀ⁱ r)
    prefix h⇑A reveal liftν lift∀ conversion =
  all-closing vM noM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ M⊑M′ qD widening
    prefix h⇑A reveal liftν lift∀ conversion
paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ
    rotate all-closing {X = X} {d = d} {d′ = d′} {u = u} {u′ = u′}
    vM noM vM′ noM′ inert-d′ inert-u′ d⊒ d′⊒ M⊑M′
    qD widening (ν occ-r r)
    prefix h⇑A reveal liftν lift∀ conversion
    with rotate h⇑A liftν occ-r conversion
paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ
    rotate all-closing {X = X} {d = d} {d′ = d′} {u = u} {u′ = u′}
    vM noM vM′ noM′ inert-d′ inert-u′ d⊒ d′⊒ M⊑M′
    qD widening (ν occ-r r)
    prefix h⇑A reveal liftν lift∀ conversion
    | s , rotated-conversion =
  conv↑⊑ᵀ (reveal-all reveal)
    (conv⊑convᵀ (paired-conversion rotated-conversion)
      bullet-relation)
    (⊑-source-liftνᵢ _)
  where
  source-value = (vM ⟨ C.gen X d ⟩) ⟨ C.`∀ u ⟩

  source-no-bullet = no•-⟨⟩ (no•-⟨⟩ noM)

  target-value = (vM′ ⟨ inert-d′ ⟩) ⟨ inert-u′ ⟩

  target-no-bullet = no•-⟨⟩ (no•-⟨⟩ noM′)

  quotient-relation =
    gen-down⊑gen-downᵀ d⊒ d′⊒ M⊑M′ qD

  endpoint-relation₀ =
    up⊑upᵀ quotient-relation widening (ν occ-r r)

  endpoint-relation =
    allocation-prefixᵀ prefix endpoint-relation₀
      (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
        source-no-bullet
        (nu-term-imprecision-source-typing endpoint-relation₀))
      (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
        target-no-bullet
        (nu-term-imprecision-target-typing endpoint-relation₀))

  source-bullet-typing =
    subst
      (λ Σ → _ ∣ (_ , _) ∷ Σ ∣ [] ⊢ _ ⦂ _)
      (sym (leftStoreⁱ-lift-left liftν))
      (⊢• refl refl (⊑-src-wf r) source-value source-no-bullet
        (nu-term-imprecision-source-typing endpoint-relation))

  target-typing =
    subst
      (λ Σ → _ ∣ Σ ∣ [] ⊢ _ ⦂ _)
      (sym (rightStoreⁱ-lift-left liftν))
      (nu-term-imprecision-target-typing endpoint-relation)

  bullet-relation =
    α⊑ᵀ source-value source-no-bullet h⇑A liftν
      lift-left-ctx-[] endpoint-relation source-bullet-typing target-typing


paired-lambda-target-closing-up-gen-leaf-handler-proofᵀ :
  PairedLambdaTargetClosingUpGenLeafClosingᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {X C′ D D′ B B′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ X ⊑ C′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion} →
  Value M → No• M →
  Value M′ → No• M′ →
  Inert d′ → Inert u′ →
  genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ C.gen X d ∶ X ⊒ `∀ D →
  genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ d′ ∶ C′ ⊒ D′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ X ⊑ C′ ∶ pC →
  (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
  (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    ((M ⟨ C.gen X d ⟩) ⟨ C.`∀ u ⟩)
    ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) B B′ q
paired-lambda-target-closing-up-gen-leaf-handler-proofᵀ
    closing vM noM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ M⊑M′ qD widening q
    prefix coherent exclusive wfL h⇑A reveal liftν lift∀ conversion =
  closing vM noM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ M⊑M′ qD widening q
    prefix h⇑A reveal liftν lift∀ conversion
