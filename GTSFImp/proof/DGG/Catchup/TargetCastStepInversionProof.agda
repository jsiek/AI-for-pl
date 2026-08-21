module proof.DGG.Catchup.TargetCastStepInversionProof where

-- File Charter:
--   * Begins the LG-3 wrapper-aware target-cast-step inversion support.
--   * Proves exposed `⊑cast²` target-cast cells by recovering the
--     intermediate ground imprecision witnesses from the CTI premise.
--   * Proves the paired `cast⊑cast²` identity cell by replaying the
--     source-only cast after the target identity step.
--   * Re-exports the checked generated-projection replacement cells under the
--     target-cast-step inversion naming convention.
--   * Does not change the CTI relation or the reduction relation.

open import Types
open import Relation.Binary.PropositionalEquality
  renaming (subst to subst≡)
import Consistency as C
import Imprecision as I
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; idᵍ; _!; ？_;
   toRenameᵗ)
open import CastTerms using
  (Term; Value; _⊢_⦂_; ⟨_,_,_⟩; _⟨_⟩; Λ_; _《_》; _↑_; _↓_;
   ⊢⟨⟩)

import proof.ImprecisionConsistency as PI
import proof.Imprecision as PImp
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)
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
    (C.renameGround (toRenameᵗ (CTX.ηᴿʷ W)) Gᵍ)
    (C.renameNonStar (toRenameᵗ (CTX.ηᴿʷ W)) Bns)
    (C.renameᵐᶜ (CTX.ηᴿʷ W) c)
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
    (C.renameGround (toRenameᵗ (CTX.ηᴿʷ W)) Gᵍ)
    (C.renameNonStar (toRenameᵗ (CTX.ηᴿʷ W)) Bns)
    (C.renameᵐᶜ (CTX.ηᴿʷ W) c)
    p q


source-ground-cast-witness : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {H : Ty Δᴸ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
  → (Hᵍ : Ground H)
  → (Gᵍ : Ground G)
  → (Bns : NonStar B)
  → (c : ν ⊢ B ∼ G)
  → H ⊑ᵂ⟨ W ⟩ B
  → H ⊑ᵂ⟨ W ⟩ G
source-ground-cast-witness {W = W} {H = H} {G = G}
    Hᵍ Gᵍ Bns c p =
  subst≡ (λ T → I._⊢_⊑_ (CTX.impEnvʷ W) (CTX.embedᴸ W H) T)
    center-eq
    (PI.refl⊑ (CTX.embedᴸ W H))
  where
  center-eq : CTX.embedᴸ W H ≡ CTX.embedᴿ W G
  center-eq =
    PI.ground-cast-target-unique⊑
      (C.renameGround (toRenameᵗ (CTX.ηᴸʷ W)) Hᵍ)
      (C.renameGround (toRenameᵗ (CTX.ηᴸʷ W)) Hᵍ)
      (C.renameGround (toRenameᵗ (CTX.ηᴿʷ W)) Gᵍ)
      (C.renameNonStar (toRenameᵗ (CTX.ηᴿʷ W)) Bns)
      (C.renameᵐᶜ (CTX.ηᴿʷ W) c)
      (PI.refl⊑ (CTX.embedᴸ W H))
      p


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


exposed-id-step-inversion-cast⊑cast² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A C : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴸ}
    {p : C ⊑ᵂ⟨ W ⟩ B}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → (c : ν ⊢ C ∼ A)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ γ ⊢² M ⟨ c ⟩ ⊑ M′ ∶ q
exposed-id-step-inversion-cast⊑cast² c rel =
  CTI2.cast⊑² c rel _


typing-id-cast-core : ∀ {Δ} {Σ} {Γ} {M : Term Δ}
    {A : Ty Δ} {ν : Env∼ Δ}
  → (a : Atom A)
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⟨ id {μ = ν} a ⟩ ⦂ A
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
typing-id-cast-core a (⊢⟨⟩ M⊢ (id a′)) = M⊢


target-id-step-inversion : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → (a : Atom B)
  → Value M
  → Value M′
  → W ∣ γ ⊢² M ⊑ M′ ⟨ id {μ = ν} a ⟩ ∶ q
  → W ∣ γ ⊢² M ⊑ M′ ∶ q
target-id-step-inversion a vM vM′ (CTI2.⊑cast² (id a′) rel q) =
  exposed-id-step-inversion-⊑cast² rel
target-id-step-inversion a (vM 《 inert 》) vM′
    (CTI2.cast⊑cast² c (id a′) rel q) =
  CTI2.cast⊑² c rel q
target-id-step-inversion {M′ = M′} a (vM 《 inert 》) vM′
    (CTI2.cast⊑² c rel q) =
  CTI2.cast⊑² c (target-id-step-inversion {M′ = M′} a vM vM′ rel) q
target-id-step-inversion {M′ = M′} a (Λ vM) vM′
    (CTI2.Λ⊑² Anv z∈A liftγ vV M⊢ rel q) =
  CTI2.Λ⊑² Anv z∈A liftγ vV (typing-id-cast-core a M⊢)
    (target-id-step-inversion {M′ = M′} a vM vM′ rel) q
target-id-step-inversion {M′ = M′} a (Λ vM) vM′
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV M⊢ rel q) =
  CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV
    (typing-id-cast-core a M⊢)
    (target-id-step-inversion {M′ = M′} a vM vM′ rel) q
target-id-step-inversion {M′ = M′} a (vM ↑ rv) vM′
    (CTI2.reveal⊑² mono rb sameγ c⊢ rel q) =
  CTI2.reveal⊑² mono rb sameγ c⊢
    (target-id-step-inversion {M′ = M′} a vM vM′ rel) q
target-id-step-inversion {M′ = M′} a (vM ↓ cv) vM′
    (CTI2.conceal⊑² mono rb sameγ c⊢ rel q) =
  CTI2.conceal⊑²
    mono rb sameγ c⊢
    (target-id-step-inversion {M′ = M′} a vM vM′ rel) q


module _ (inversion : RightInjInversion²) where

  exposed-project-same-step-inversion-⊑cast² =
    GPR.generated-project-same-replacement inversion

  exposed-project-expand-step-inversion-⊑cast² =
    GPR.generated-project-expand-replacement inversion
