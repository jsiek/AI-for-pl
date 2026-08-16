module proof.DGG.Catchup.GeneratedProjectionReplacementProof where

-- File Charter:
--   * Checks the LG-3 replacement for the old GeneratedProjection/CatchupCast
--     projection provenance in the core exposed-cast case.
--   * Recovers the matched projection relation by RightInjInversion² and
--     rebuilds the expansion reduct with ordinary CTI target-cast layers.
--   * Does not prove the wrapper-aware target-cast-step inversion theorem.

open import Types
import Consistency as C
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; idᵍ; _!; ？_)
open import CastTerms using
  (Term; Value; Inert; ƛ_; Λ_; $; inj; fun; all; seal; _⟨_⟩;
   _《_》; _↑_; _↓_)

import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)
open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal; sv-reveal-fun;
   sv-conceal-fun; sv-reveal-all; sv-conceal-all)


value→spine : ∀ {Δ} {V : Term Δ}
  → Value V
  → SpineValue V
value→spine (ƛ N) = sv-ƛ N
value→spine (Λ vV) = sv-Λ (value→spine vV)
value→spine ($ κ) = sv-$ κ
value→spine (vV 《 inert 》) = sv-cast (value→spine vV) inert
value→spine (vV ↑ fun) = sv-reveal-fun (value→spine vV)
value→spine (vV ↑ all) = sv-reveal-all (value→spine vV)
value→spine (vV ↓ seal) = sv-seal (value→spine vV)
value→spine (vV ↓ fun) = sv-conceal-fun (value→spine vV)
value→spine (vV ↓ all) = sv-conceal-all (value→spine vV)


module _ (inversion : RightInjInversion²) where

  generated-project-same-replacement : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {N : Term Δᴿ}
      {A : Ty Δᴸ} {G : Ty Δᴿ} {μ : Env∼ Δᴿ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {p★ : A ⊑ᵂ⟨ W ⟩ ★}
    → Value M
    → Value N
    → W ∣ γ ⊢² M ⊑
        N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
            ⦃ C.ground-nonstar Gᵍ ⦄ ⟩ ∶ p★
    → (qG : A ⊑ᵂ⟨ W ⟩ G)
    → W ∣ γ ⊢² M ⊑ N ∶ qG
  generated-project-same-replacement vM vN rel qG =
    inversion (value→spine vM) vN rel qG


  generated-project-expand-replacement : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
      {M : Term Δᴸ} {N : Term Δᴿ}
      {A : Ty Δᴸ} {G B : Ty Δᴿ} {μ ν : Env∼ Δᴿ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★} {★∼G : ν ⊢★∼ G}
      {Bns : NonStar B} {p★ : A ⊑ᵂ⟨ W ⟩ ★}
    → Value M
    → Value N
    → W ∣ γ ⊢² M ⊑
        N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
            ⦃ C.ground-nonstar Gᵍ ⦄ ⟩ ∶ p★
    → (c : ν ⊢ G ∼ B)
    → (qG : A ⊑ᵂ⟨ W ⟩ G)
    → (qB : A ⊑ᵂ⟨ W ⟩ B)
    → W ∣ γ ⊢² M ⊑
        N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
            ⦃ C.ground-nonstar Gᵍ ⦄ ⟩
          ⟨ ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
            ⦃ C.ground-nonstar Gᵍ ⦄ ⟩
          ⟨ c ⟩ ∶ qB
  generated-project-expand-replacement
      {Gᵍ = Gᵍ} {G∼★ = G∼★} {★∼G = ★∼G} {p★ = p★}
      vM vN rel c qG qB =
    CTI2.⊑cast² c
      (CTI2.⊑cast² proj
        (CTI2.⊑cast² tag (inversion (value→spine vM) vN rel qG) p★)
        qG)
      qB
    where
    tag : _ ⊢ _ ∼ ★
    tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
      ⦃ C.ground-nonstar Gᵍ ⦄

    proj : _ ⊢ ★ ∼ _
    proj = ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
      ⦃ C.ground-nonstar Gᵍ ⦄
