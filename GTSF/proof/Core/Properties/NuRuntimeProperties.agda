module proof.Core.Properties.NuRuntimeProperties where

-- File Charter:
--   * Structural projections for the Nu GTSF `RuntimeOK` judgment.
--   * Extracts runtime validity for the active subterm of applications, casts,
--     type allocations, and primitive operations.
--   * Reduction and preservation results belong in
--     `proof.DGG.Core.NuPreservation`.

open import NuTerms

runtime-·₁ :
  ∀ {L M} →
  RuntimeOK (L · M) →
  RuntimeOK L
runtime-·₁ (ok-no (no•-· noL noM)) = ok-no noL
runtime-·₁ (ok-·₁ okL noM) = okL
runtime-·₁ (ok-·₂ vL noL okM) = ok-no noL

runtime-·₂ :
  ∀ {L M} →
  Value L →
  RuntimeOK (L · M) →
  RuntimeOK M
runtime-·₂ vL (ok-no (no•-· noL noM)) = ok-no noM
runtime-·₂ vL (ok-·₁ okL noM) = ok-no noM
runtime-·₂ vL (ok-·₂ vL′ noL okM) = okM

runtime-⟨⟩ :
  ∀ {M c} →
  RuntimeOK (M ⟨ c ⟩) →
  RuntimeOK M
runtime-⟨⟩ (ok-no (no•-⟨⟩ noM)) = ok-no noM
runtime-⟨⟩ (ok-⟨⟩ okM) = okM

runtime-ν :
  ∀ {A L c} →
  RuntimeOK (ν A L c) →
  RuntimeOK L
runtime-ν (ok-no (no•-ν noL)) = ok-no noL
runtime-ν (ok-ν okL) = okL

runtime-⊕₁ :
  ∀ {L op M} →
  RuntimeOK (L ⊕[ op ] M) →
  RuntimeOK L
runtime-⊕₁ (ok-no (no•-⊕ noL noM)) = ok-no noL
runtime-⊕₁ (ok-⊕₁ okL noM) = okL
runtime-⊕₁ (ok-⊕₂ vL noL okM) = ok-no noL

runtime-⊕₂ :
  ∀ {L op M} →
  Value L →
  RuntimeOK (L ⊕[ op ] M) →
  RuntimeOK M
runtime-⊕₂ vL (ok-no (no•-⊕ noL noM)) = ok-no noM
runtime-⊕₂ vL (ok-⊕₁ okL noM) = ok-no noM
runtime-⊕₂ vL (ok-⊕₂ vL′ noL okM) = okM
