module proof.QuotientedTermImprecisionTest where

-- File Charter:
--   * Exercises the mutually recursive narrowing/widening rules using the
--     incomparable `D` and `E` intermediates from the bad-GLB example.
--   * Relates two casts of blame from the same source endpoint to the same
--     target endpoint without requiring ordinary imprecision between `D` and
--     `E`.

open import Data.List using ([])
open import Data.Nat using (zero)

open import Types
open import Imprecision using (idᵢ)
import ImprecisionWf as IWF
open import NuTerms using (blame; _⟨_⟩)
open import QuotientedTermImprecision
open import TermTyping using (⊢blame)
open import proof.ForallPermutationTest using (glb-lower-XY⊑ᵖYX)
open import proof.MLBGlbExample using
  (glb-bad-A; glb-bad-A⊑A; glb-bad-B; glb-bad-B⊑B)
open import proof.MLBRouteOperationalExperiment using
  ( down-D
  ; down-D-⊒
  ; down-E
  ; down-E-⊒
  ; up-D
  ; up-D-⊑
  ; up-E
  ; up-E-⊑
  )

blame-A⊑blame-A :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ blame ⊑ blame ⦂ glb-bad-A ⊑ glb-bad-A ∶ glb-bad-A⊑A
blame-A⊑blame-A =
  blame⊑ᵀ (⊢blame (IWF.⊑-tgt-wf glb-bad-A⊑A))

cast-via-D⊑cast-via-E :
  idᵢ zero ∣ zero ∣ zero ∣ [] ∣ []
    ⊢ᴺ (blame ⟨ down-D ⟩) ⟨ up-D ⟩
      ⊑ (blame ⟨ down-E ⟩) ⟨ up-E ⟩
    ⦂ glb-bad-B ⊑ glb-bad-B ∶ glb-bad-B⊑B
cast-via-D⊑cast-via-E =
  up⊑upᵀ
    (down⊑downᵀ down-D-⊒ down-E-⊒ blame-A⊑blame-A
      glb-lower-XY⊑ᵖYX)
    (quotient-id-widening up-D-⊑ up-E-⊑) glb-bad-B⊑B
