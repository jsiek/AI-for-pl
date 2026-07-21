module proof.NuImprecisionSourceTagQuotientUpProof where

-- File Charter:
--   * Closes the quotient-up branch of source ground-tag cancellation.
--   * Uses only ground-value quotient elimination as a semantic dependency.
--   * Rebuilds the surviving target widening without dequotienting globally.

open import Coercions using (Coercion; _!)
open import Data.List using ([])
open import Data.Product using (_,_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; quotient-cast-widening
  ; quotient-id-widening
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import TermTyping using (SealModeStore★)
open import Types using (Ground; Ty; TyCtx; ★)
open import
  proof.NuImprecisionGroundValueQuotientEliminationDef using
  (GroundValueQuotientEliminationᵀ)


seal-mode-store-id-only :
  ∀ {Σ} →
  SealModeStore★ Coercions.id-onlyᵈ Σ
seal-mode-store-id-only α ()


source-tag-quotient-up-cancellationᵀ :
  GroundValueQuotientEliminationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {G D′ B : Ty} {u′ : Coercion}
    {qD : Φ ∣ Δᴸ ⊢ G ⊑ᵖ D′ ⊣ Δᴿ} →
  Ground G →
  Value V →
  Value (V′ ⟨ u′ ⟩) →
  No• (V′ ⟨ u′ ⟩) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⊑ V′ ⦂ G ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (G !) u′ G D′ ★ B →
  (q : Φ ∣ Δᴸ ⊢ G ⊑ B ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⟨ u′ ⟩ ⦂ G ⊑ B ∶ q
source-tag-quotient-up-cancellationᵀ
    eliminate gG vV (vV′ ⟨ inert-u′ ⟩) noW inner
    (quotient-id-widening source-tag u′⊑) q
    with eliminate gG vV vV′ inner
source-tag-quotient-up-cancellationᵀ
    eliminate gG vV (vV′ ⟨ inert-u′ ⟩) noW inner
    (quotient-id-widening source-tag u′⊑) q
    | r , ordinary =
  ⊑cast⊑idᵀ seal-mode-store-id-only u′⊑ ordinary q
source-tag-quotient-up-cancellationᵀ
    eliminate gG vV (vV′ ⟨ inert-u′ ⟩) noW inner
    (quotient-cast-widening
      mode seal★ source-tag mode′ seal★′ u′⊑) q
    with eliminate gG vV vV′ inner
source-tag-quotient-up-cancellationᵀ
    eliminate gG vV (vV′ ⟨ inert-u′ ⟩) noW inner
    (quotient-cast-widening
      mode seal★ source-tag mode′ seal★′ u′⊑) q
    | r , ordinary =
  ⊑cast⊑ᵀ mode′ seal★′ u′⊑ ordinary q
