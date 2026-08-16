module proof.DGG.Catchup.TargetCastStepInversionProof where

-- File Charter:
--   * Begins the LG-3 wrapper-aware target-cast-step inversion support.
--   * Proves the exposed `⊑cast²` ground-step cell by recovering the
--     intermediate ground imprecision witness from the CTI premise.
--   * Re-exports the checked generated-projection replacement cells under the
--     target-cast-step inversion naming convention.
--   * Does not change the CTI relation or the reduction relation.

open import Types
open import Relation.Binary.PropositionalEquality
  renaming (subst to subst≡)
import Consistency as C
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; idᵍ; _!; ？_; toRenameᵗ)
open import CastTerms using (Term; Value; _⟨_⟩)

import proof.ImprecisionConsistency as PI
import proof.Imprecision as PImp
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)
open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)
open import proof.DGG.Catchup.GeneratedProjectionReplacementProof
  as GPR using ()


target-ground-cast-witness : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
  → (Gᵍ : Ground G)
  → (Bns : NonStar B)
  → (c : ν ⊢ B ∼ G)
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ W ⟩ ★
  → A ⊑ᵂ⟨ W ⟩ G
target-ground-cast-witness {W = W} Gᵍ Bns c p q =
  PI.ground-cast-target⊑
    (C.renameGround (toRenameᵗ (CTI2.ηᴿʷ W)) Gᵍ)
    (C.renameNonStar (toRenameᵗ (CTI2.ηᴿʷ W)) Bns)
    (C.renameᵐᶜ (CTI2.ηᴿʷ W) c)
    p q


exposed-ground-step-inversion-⊑cast² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {Gᵍ : Ground G} {G∼★ : ν ⊢ G ∼★}
    {Bns : NonStar B}
    {p : A ⊑ᵂ⟨ W ⟩ B}
    {q : A ⊑ᵂ⟨ W ⟩ ★}
  → (c : ν ⊢ B ∼ G)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ γ ⊢² M ⊑
      M′ ⟨ c ⟩
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ C.ground-nonstar Gᵍ ⦄ ⟩
      ∶ q
exposed-ground-step-inversion-⊑cast²
    {W = W} {A = A} {G = G}
    {Gᵍ = Gᵍ} {G∼★ = G∼★} {Bns = Bns} {p = p} {q = q}
    c rel =
  CTI2.⊑cast² tag (CTI2.⊑cast² c rel qG) q
  where
  qG : A ⊑ᵂ⟨ W ⟩ G
  qG = target-ground-cast-witness {W = W} {A = A} {G = G}
    Gᵍ Bns c p q

  tag : _ ⊢ _ ∼ ★
  tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
    ⦃ C.ground-nonstar Gᵍ ⦄


target-expand-cast-witness : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {G B : Ty Δᴿ} {ν : Env∼ Δᴿ}
  → (Gᵍ : Ground G)
  → (Bns : NonStar B)
  → (c : ν ⊢ G ∼ B)
  → A ⊑ᵂ⟨ W ⟩ ★
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ W ⟩ G
target-expand-cast-witness {W = W} Gᵍ Bns c p q =
  PI.expand-cast-source⊑
    (C.renameGround (toRenameᵗ (CTI2.ηᴿʷ W)) Gᵍ)
    (C.renameNonStar (toRenameᵗ (CTI2.ηᴿʷ W)) Bns)
    (C.renameᵐᶜ (CTI2.ηᴿʷ W) c)
    p q


exposed-expand-step-inversion-⊑cast² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {G B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {Gᵍ : Ground G} {★∼G : ν ⊢★∼ G}
    {Bns : NonStar B}
    {p : A ⊑ᵂ⟨ W ⟩ ★}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → (c : ν ⊢ G ∼ B)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ γ ⊢² M ⊑
      M′ ⟨ ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
            ⦃ C.ground-nonstar Gᵍ ⦄ ⟩
        ⟨ c ⟩
      ∶ q
exposed-expand-step-inversion-⊑cast²
    {W = W} {A = A} {G = G}
    {Gᵍ = Gᵍ} {★∼G = ★∼G} {Bns = Bns} {p = p} {q = q}
    c rel =
  CTI2.⊑cast² c (CTI2.⊑cast² proj rel qG) q
  where
  qG : A ⊑ᵂ⟨ W ⟩ G
  qG = target-expand-cast-witness {W = W} {A = A} {G = G}
    Gᵍ Bns c p q

  proj : _ ⊢ ★ ∼ _
  proj = ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ Gᵍ)
    ⦃ C.ground-nonstar Gᵍ ⦄


exposed-id-step-inversion-⊑cast² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ γ ⊢² M ⊑ M′ ∶ q
exposed-id-step-inversion-⊑cast²
    {W = W} {γ = γ} {M = M} {M′ = M′} {p = p} {q = q} rel =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ M′ ∶ r) (PImp.⊑-unique p q) rel


module _ (inversion : RightInjInversion²) where

  exposed-project-same-step-inversion-⊑cast² =
    GPR.generated-project-same-replacement inversion

  exposed-project-expand-step-inversion-⊑cast² =
    GPR.generated-project-expand-replacement inversion
