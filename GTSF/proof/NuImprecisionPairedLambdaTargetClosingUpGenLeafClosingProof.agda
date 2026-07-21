module
  proof.NuImprecisionPairedLambdaTargetClosingUpGenLeafClosingProof
  where

-- File Charter:
--   * Adapts the reusable fused quotient gen-down/gen closing theorem to the
--     exact target-closing handler field.
--   * Keeps the semantic theorem as an explicit higher-order dependency;
--     the refuted pre-reveal quotient rotation is not reintroduced.
--   * Contains no postulate, hole, permissive option, broad simulation
--     import, or recursive frame-closing dependency.

import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; genᵈ
  ; tag-or-idᵈ
  )
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpGenLeafClosingDef
  using (PairedLambdaTargetClosingUpGenLeafClosingᵀ)


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
    d⊒ d′⊒ M⊑M′ qD widening q =
  closing vM noM vM′ noM′ inert-d′ inert-u′
    d⊒ d′⊒ M⊑M′ qD widening q
