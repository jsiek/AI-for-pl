module proof.DGG.Catchup.ExtraCastRightAtProof where

-- File Charter:
--   * Implements checked structural base rows for the fuel-indexed
--     `ExtraCastRightAt` proof.
--   * The live fuel surface in `ValueCatchupRightDef` now consumes the
--     casted-target CTI premise directly.
--   * The internal worker surface carries `StructuralWorldExtendᴿ`; the
--     adapter in `StructuralCatchupRightDef` erases it to the public
--     `WorldExtendᴿ` boundary.

open import Data.Nat using (_<_)
open import Data.Fin using (zero)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
  renaming (subst to subst≡)

open import Types using (Ty; TyVar; Atom; Ground; NonStar; ★; ＇_; `∀; ∀★)
import Imprecision as I
import Consistency as C
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; idᵍ; _!; ？_;
   ground-nonstar; bot-elim; bot-intro)
open import Conversion using (Conv↓)
open import CastTerms using
  (Term; Value; Inert; ⟨_,_,_⟩; _⊢_⦂_; ⊢⟨⟩; inj; _⟨_⟩; _《_》)
open import Reduction using
  (pure-step; β-id; ground; expand; tag-untag; ξ-⟨⟩;
   applyConsistencies)
open import proof.Reduction using
  (applyConsistencies-Inert; castSize-applyConsistencies)
open import proof.TypeSafety.Progress using (no-bot-value)
open import proof.Imprecision using
  (imprecision-to-fresh; imprecision-no-star-to-bot)
open import proof.ImprecisionConsistency using
  (ext-injective; renameᵗ-injective; toRenameᵗ-injective)
import proof.DGG.CastTermImprecision2Typing as CTI2T
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (castSize; ground-other-decreaseᵀ; project-expand-decreaseᵀ)
open import proof.DGG.Catchup.StructuralCatchupRightDef public using
  (StructuralCatchupRightResult; StructuralExtraCastRightAt;
   erase-structural-extra-cast-right-at; structural-catchup-refl;
   structural-catchup-keep-step; structural-catchup-prepend-keep;
   structural-catchup-prepend-keep-stutter;
   structural-catchup-compose-target-cast;
   structural-catchup-compose-paired-target-cast)
open import proof.DGG.Catchup.StructuralWorldExtendProof using
  (structural-world-extendᴿ)
open import proof.DGG.Catchup.TargetCastStepInversionProof using
  (exposed-ground-step-inversion-⊑cast²; target-ground-cast-witness;
   target-expand-cast-witness;
   source-ground-cast-witness;
   exposed-project-same-step-inversion-⊑cast²;
   exposed-project-expand-step-inversion-⊑cast²;
   matched-conceal-partner-target-id-core;
   matched-conceal-partner-target-id-framed-core;
   target-id-step-inversion)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


source-value-target-bottom-impossible : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ}
  → Value M
  → ⟨ Δᴸ , CTX.sourceStoreʷ W , CTX.srcCtxʷ γ ⟩ ⊢ M ⦂ A
  → A ⊑ᵂ⟨ W ⟩ `∀ (＇ zero)
  → ⊥
source-value-target-bottom-impossible {W = W} {γ = γ}
    {M = M} {A = `∀ A} vM M⊢ (I.∀⊑∀ body) =
  no-bot-value vM
    (subst≡
      (λ A′ → ⟨ _ , CTX.sourceStoreʷ W , CTX.srcCtxʷ γ ⟩
        ⊢ M ⦂ `∀ A′)
      body-eq M⊢)
  where
  body-eq : A ≡ (＇ zero)
  body-eq =
    renameᵗ-injective
      (ext-injective (toRenameᵗ-injective (CTX.ηᴸʷ W)))
      (imprecision-to-fresh body)
source-value-target-bottom-impossible {A = `∀ A} vM M⊢
    (I.∀⊑ Anv z∈A body) =
  imprecision-no-star-to-bot refl body z∈A


target-bot-elim-refutation : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ `∀ ★}
  → Value M′
  → W ∣ γ ⊢² M ⊑ M′ ⟨ bot-elim {μ = ν} ⟩ ∶ q
  → ⊥
target-bot-elim-refutation vM′ rel
    with CTI2T.target-typing² rel
target-bot-elim-refutation vM′ rel | ⊢⟨⟩ M′⊢ bot-elim =
  no-bot-value vM′ M′⊢


target-bot-intro-refutation : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ `∀ (＇ zero)}
  → Value M
  → W ∣ γ ⊢² M ⊑ M′ ⟨ bot-intro {μ = ν} ⟩ ∶ q
  → ⊥
target-bot-intro-refutation {q = q} vM rel =
  source-value-target-bottom-impossible vM (CTI2T.source-typing² rel) q


rep★-ground-step-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ?}
    {M′ : Term Δᴿ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → CTX.Rep★PartnerOK W X P Xᴿ? (M′ ⟨ _! c ⟩)
  → CTX.Rep★PartnerOK W X P Xᴿ?
      ((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
rep★-ground-step-core c (CTX.rep★-untagged ())
rep★-ground-step-core c (CTX.rep★-nonvar-tag Gnv) =
  CTX.rep★-nonvar-tag Gnv
rep★-ground-step-core c (CTX.rep★-var-tag aligned) =
  CTX.rep★-var-tag aligned
rep★-ground-step-core c
    (CTX.rep★-matched-inner-tags X₂≢X aligned) =
  CTX.rep★-matched-inner-tags X₂≢X aligned
rep★-ground-step-core c (CTX.rep★-round-trip ok) =
  CTX.rep★-round-trip (rep★-ground-step-core c ok)


rep★-ground-step-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ?}
    {M′ : Term Δᴿ} {B G C D : Ty Δᴿ} {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → (d : μ ⊢ C ∼ D)
  → CTX.Rep★PartnerOK W X P Xᴿ? ((M′ ⟨ _! c ⟩) ⟨ d ⟩)
  → CTX.Rep★PartnerOK W X P Xᴿ?
      (((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩) ⟨ d ⟩)
rep★-ground-step-framed-core c d (CTX.rep★-untagged ())
rep★-ground-step-framed-core c d (CTX.rep★-nonvar-tag Gnv) =
  CTX.rep★-nonvar-tag Gnv
rep★-ground-step-framed-core c d (CTX.rep★-var-tag aligned) =
  CTX.rep★-var-tag aligned
rep★-ground-step-framed-core c d
    (CTX.rep★-matched-inner-tags X₂≢X aligned) =
  CTX.rep★-matched-inner-tags X₂≢X aligned
rep★-ground-step-framed-core c d (CTX.rep★-round-trip ok) =
  CTX.rep★-round-trip (rep★-ground-step-framed-core c d ok)


matched-conceal-partner-ground-step-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ : Term Δᴿ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → B ≢ G
  → CTX.MatchedConcealPartnerOK W P c₀ Xᴿ? (M′ ⟨ _! c ⟩)
  → CTX.MatchedConcealPartnerOK W P c₀ Xᴿ?
      ((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
matched-conceal-partner-ground-step-core c B≢G
    (CTX.matched-seal-star-partner ok) =
  CTX.matched-seal-star-partner (rep★-ground-step-core c ok)
matched-conceal-partner-ground-step-core c B≢G
    (CTX.matched-seal-nonstar Rns) =
  CTX.matched-seal-nonstar Rns
matched-conceal-partner-ground-step-core c B≢G
    CTX.matched-fun-conceal-target =
  CTX.matched-fun-conceal-target
matched-conceal-partner-ground-step-core c B≢G
    CTX.matched-all-conceal-target =
  CTX.matched-all-conceal-target
matched-conceal-partner-ground-step-core c B≢G
    CTX.matched-id-conceal-target =
  CTX.matched-id-conceal-target


matched-conceal-partner-ground-step-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ : Term Δᴿ} {B G C D : Ty Δᴿ}
    {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → (d : μ ⊢ C ∼ D)
  → CTX.MatchedConcealPartnerOK W P c₀ Xᴿ?
      ((M′ ⟨ _! c ⟩) ⟨ d ⟩)
  → CTX.MatchedConcealPartnerOK W P c₀ Xᴿ?
      (((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩) ⟨ d ⟩)
matched-conceal-partner-ground-step-framed-core c d
    (CTX.matched-seal-star-partner ok) =
  CTX.matched-seal-star-partner
    (rep★-ground-step-framed-core c d ok)
matched-conceal-partner-ground-step-framed-core c d
    (CTX.matched-seal-nonstar Rns) =
  CTX.matched-seal-nonstar Rns
matched-conceal-partner-ground-step-framed-core c d
    CTX.matched-fun-conceal-target =
  CTX.matched-fun-conceal-target
matched-conceal-partner-ground-step-framed-core c d
    CTX.matched-all-conceal-target =
  CTX.matched-all-conceal-target
matched-conceal-partner-ground-step-framed-core c d
    CTX.matched-id-conceal-target =
  CTX.matched-id-conceal-target


rep★-projection-impossible : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ?}
    {M′ : Term Δᴿ} {G B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → CTX.Rep★PartnerOK W X P Xᴿ? (M′ ⟨ ？ c ⟩)
  → ⊥
rep★-projection-impossible c (CTX.rep★-untagged ())
rep★-projection-impossible c (CTX.rep★-round-trip ok) =
  rep★-projection-impossible c ok


rep★-projection-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ?}
    {M′ N : Term Δᴿ} {G B C D : Ty Δᴿ}
    {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → (d : μ ⊢ C ∼ D)
  → CTX.Rep★PartnerOK W X P Xᴿ? ((M′ ⟨ ？ c ⟩) ⟨ d ⟩)
  → CTX.Rep★PartnerOK W X P Xᴿ? (N ⟨ d ⟩)
rep★-projection-framed-core c d (CTX.rep★-untagged ())
rep★-projection-framed-core c d (CTX.rep★-nonvar-tag Gnv) =
  CTX.rep★-nonvar-tag Gnv
rep★-projection-framed-core c d (CTX.rep★-var-tag aligned) =
  CTX.rep★-var-tag aligned
rep★-projection-framed-core c d
    (CTX.rep★-matched-inner-tags X₂≢X aligned) =
  CTX.rep★-matched-inner-tags X₂≢X aligned
rep★-projection-framed-core c d (CTX.rep★-round-trip ok) =
  CTX.rep★-round-trip (rep★-projection-framed-core c d ok)


matched-conceal-partner-projection-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ N : Term Δᴿ} {G B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → CTX.MatchedConcealPartnerOK W P c₀ Xᴿ? (M′ ⟨ ？ c ⟩)
  → CTX.MatchedConcealPartnerOK W P c₀ Xᴿ? N
matched-conceal-partner-projection-core c
    (CTX.matched-seal-star-partner ok) =
  ⊥-elim (rep★-projection-impossible c ok)
matched-conceal-partner-projection-core c
    (CTX.matched-seal-nonstar Rns) =
  CTX.matched-seal-nonstar Rns
matched-conceal-partner-projection-core c
    CTX.matched-fun-conceal-target =
  CTX.matched-fun-conceal-target
matched-conceal-partner-projection-core c
    CTX.matched-all-conceal-target =
  CTX.matched-all-conceal-target
matched-conceal-partner-projection-core c
    CTX.matched-id-conceal-target =
  CTX.matched-id-conceal-target


matched-conceal-partner-projection-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ N : Term Δᴿ} {G B C D : Ty Δᴿ}
    {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → (d : μ ⊢ C ∼ D)
  → CTX.MatchedConcealPartnerOK W P c₀ Xᴿ?
      ((M′ ⟨ ？ c ⟩) ⟨ d ⟩)
  → CTX.MatchedConcealPartnerOK W P c₀ Xᴿ? (N ⟨ d ⟩)
matched-conceal-partner-projection-framed-core c d
    (CTX.matched-seal-star-partner ok) =
  CTX.matched-seal-star-partner
    (rep★-projection-framed-core c d ok)
matched-conceal-partner-projection-framed-core c d
    (CTX.matched-seal-nonstar Rns) =
  CTX.matched-seal-nonstar Rns
matched-conceal-partner-projection-framed-core c d
    CTX.matched-fun-conceal-target =
  CTX.matched-fun-conceal-target
matched-conceal-partner-projection-framed-core c d
    CTX.matched-all-conceal-target =
  CTX.matched-all-conceal-target
matched-conceal-partner-projection-framed-core c d
    CTX.matched-id-conceal-target =
  CTX.matched-id-conceal-target


rep★-projection-double-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ?}
    {M′ N : Term Δᴿ} {G B C D E F : Ty Δᴿ}
    {ν μ ω : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → (d : μ ⊢ C ∼ D)
  → (e : ω ⊢ E ∼ F)
  → CTX.Rep★PartnerOK W X P Xᴿ?
      (((M′ ⟨ ？ c ⟩) ⟨ d ⟩) ⟨ e ⟩)
  → CTX.Rep★PartnerOK W X P Xᴿ? ((N ⟨ d ⟩) ⟨ e ⟩)
rep★-projection-double-framed-core c d e (CTX.rep★-untagged ())
rep★-projection-double-framed-core c d e (CTX.rep★-nonvar-tag Gnv) =
  CTX.rep★-nonvar-tag Gnv
rep★-projection-double-framed-core c d e (CTX.rep★-var-tag aligned) =
  CTX.rep★-var-tag aligned
rep★-projection-double-framed-core c d e
    (CTX.rep★-matched-inner-tags X₂≢X aligned) =
  CTX.rep★-matched-inner-tags X₂≢X aligned
rep★-projection-double-framed-core c d e (CTX.rep★-round-trip ok) =
  CTX.rep★-round-trip
    (rep★-projection-double-framed-core c d e ok)


matched-conceal-partner-projection-double-framed-core :
    ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ N : Term Δᴿ} {G B C D E F : Ty Δᴿ}
    {ν μ ω : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → (d : μ ⊢ C ∼ D)
  → (e : ω ⊢ E ∼ F)
  → CTX.MatchedConcealPartnerOK W P c₀ Xᴿ?
      (((M′ ⟨ ？ c ⟩) ⟨ d ⟩) ⟨ e ⟩)
  → CTX.MatchedConcealPartnerOK W P c₀ Xᴿ? ((N ⟨ d ⟩) ⟨ e ⟩)
matched-conceal-partner-projection-double-framed-core c d e
    (CTX.matched-seal-star-partner ok) =
  CTX.matched-seal-star-partner
    (rep★-projection-double-framed-core c d e ok)
matched-conceal-partner-projection-double-framed-core c d e
    (CTX.matched-seal-nonstar Rns) =
  CTX.matched-seal-nonstar Rns
matched-conceal-partner-projection-double-framed-core c d e
    CTX.matched-fun-conceal-target =
  CTX.matched-fun-conceal-target
matched-conceal-partner-projection-double-framed-core c d e
    CTX.matched-all-conceal-target =
  CTX.matched-all-conceal-target
matched-conceal-partner-projection-double-framed-core c d e
    CTX.matched-id-conceal-target =
  CTX.matched-id-conceal-target


structural-inert-extra-cast-right-at : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′ : ν ⊢ B ∼ B′)
  → (c′<fuel : castSize c′ < fuel)
  → (rel : W ∣ γ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q)
  → (vM : Value M)
  → (vM′ : Value M′)
  → (inert : Inert c′)
  → StructuralCatchupRightResult W γ M (M′ ⟨ c′ ⟩) q
structural-inert-extra-cast-right-at c′ c′<fuel rel vM vM′ inert =
  structural-catchup-refl (vM′ 《 inert 》) rel


structural-id-extra-cast-right-at : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → (a : Atom B)
  → castSize (id {μ = ν} a) < fuel
  → W ∣ γ ⊢² M ⊑ M′ ⟨ id {μ = ν} a ⟩ ∶ q
  → Value M
  → Value M′
  → StructuralCatchupRightResult W γ M (M′ ⟨ id {μ = ν} a ⟩) q
structural-id-extra-cast-right-at a c′<fuel rel vM vM′ =
  structural-catchup-keep-step vM′ (pure-step (β-id vM′))
    (target-id-step-inversion a vM vM′ rel)


structural-ground-extra-cast-right-at : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ ★}
  → (c : ν ⊢ B ∼ G)
  → StructuralExtraCastRightAt (castSize (_! c))
  → ground-other-decreaseᵀ
  → B ≢ G
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → StructuralCatchupRightResult W γ M (M′ ⟨ _! c ⟩) q
structural-ground-extra-cast-right-at {W = W} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B = B} {G = G}
    {ν = ν} ⦃ Gᵍ = Gᵍ ⦄
    ⦃ G∼★ = G∼★ ⦄ ⦃ Bns = Bns ⦄ {p = p} {q = q}
    c smaller-extra ground-other-decrease B≢G rel vM vM′ =
  structural-catchup-prepend-keep
    (pure-step (ground ⦃ Gns = ground-nonstar Gᵍ ⦄ vM′ B≢G))
    reduct-rel
    combined
  where
  tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
    ⦃ ground-nonstar Gᵍ ⦄

  qG : A ⊑ᵂ⟨ W ⟩ G
  qG = target-ground-cast-witness {W = W} {A = A} {B = B}
    {G = G} Gᵍ Bns c p q

  reduct-rel : W ∣ γ ⊢² M ⊑
      M′ ⟨ c ⟩
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩
      ∶ q
  reduct-rel =
    exposed-ground-step-inversion-⊑cast² {W = W} {γ = γ}
      {M = M} {M′ = M′} {A = A} {B = B} {G = G}
      {ν = ν} {Gᵍ = Gᵍ} {G∼★ = G∼★} {Bns = Bns}
      {p = p} {q = q} c rel

  child : StructuralCatchupRightResult W γ M (M′ ⟨ c ⟩) qG
  child =
    smaller-extra c (ground-other-decrease c)
      (CTI2.⊑cast² c rel qG) vM vM′

  plan = StructuralCatchupRightResult.structural-ext child
  ext = structural-world-extendᴿ plan
  χs = StructuralCatchupRightResult.χs child
  tagχ = applyConsistencies χs tag

  residual : StructuralCatchupRightResult
      (StructuralCatchupRightResult.W′ child)
      (ECR.mapCtxᴿ ext γ)
      M
      (StructuralCatchupRightResult.N′ child ⟨ tagχ ⟩)
      (ECR.transport⊑ᵂ ext q)
  residual =
    structural-catchup-refl
      (StructuralCatchupRightResult.final-value child
        《 applyConsistencies-Inert χs
          (inj ⦃ Gns = ground-nonstar Gᵍ ⦄) 》)
      (CTI2.⊑cast² tagχ
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ ext q))

  combined =
    structural-catchup-compose-target-cast tag child residual


structural-paired-ground-extra-cast-right-at : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {C A : Ty Δᴸ} {B G : Ty Δᴿ}
    {νᴸ : Env∼ Δᴸ} {νᴿ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : νᴿ ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
    {p : C ⊑ᵂ⟨ W ⟩ B}
    {qG : A ⊑ᵂ⟨ W ⟩ G}
    {q★ : A ⊑ᵂ⟨ W ⟩ ★}
  → (cᴸ : νᴸ ⊢ C ∼ A)
  → (cᴿ : νᴿ ⊢ B ∼ G)
  → StructuralExtraCastRightAt (castSize (_! cᴿ))
  → ground-other-decreaseᵀ
  → B ≢ G
  → Value M
  → Value M′
  → Inert cᴸ
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → StructuralCatchupRightResult W γ (M ⟨ cᴸ ⟩)
      (M′ ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ cᴿ ⟩)
      q★
structural-paired-ground-extra-cast-right-at {W = W} {γ = γ}
    {M = M} {M′ = M′} {C = C} {A = A} {B = B} {G = G}
    {νᴿ = νᴿ} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
    ⦃ Bns = Bns ⦄ {p = p} {qG = qG} {q★ = q★}
    cᴸ cᴿ smaller-extra ground-other-decrease B≢G vM vM′ inertᴸ rel =
  structural-catchup-prepend-keep-stutter
    (pure-step (ground ⦃ Gns = ground-nonstar Gᵍ ⦄ vM′ B≢G))
    after-ground
  where
  tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
    ⦃ ground-nonstar Gᵍ ⦄

  child : StructuralCatchupRightResult W γ
      (M ⟨ cᴸ ⟩) (M′ ⟨ cᴿ ⟩) qG
  child =
    smaller-extra cᴿ (ground-other-decrease cᴿ)
      (CTI2.cast⊑cast² cᴸ cᴿ rel qG) (vM 《 inertᴸ 》) vM′

  plan = StructuralCatchupRightResult.structural-ext child
  ext = structural-world-extendᴿ plan
  χs = StructuralCatchupRightResult.χs child
  tagχ = applyConsistencies χs tag

  residual : StructuralCatchupRightResult
      (StructuralCatchupRightResult.W′ child)
      (ECR.mapCtxᴿ ext γ)
      (M ⟨ cᴸ ⟩)
      (StructuralCatchupRightResult.N′ child ⟨ tagχ ⟩)
      (ECR.transport⊑ᵂ ext q★)
  residual =
    structural-catchup-refl
      (StructuralCatchupRightResult.final-value child
        《 applyConsistencies-Inert χs
          (inj ⦃ Gns = ground-nonstar Gᵍ ⦄) 》)
      (CTI2.⊑cast² tagχ
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ ext q★))

  after-ground : StructuralCatchupRightResult W γ (M ⟨ cᴸ ⟩)
      ((M′ ⟨ cᴿ ⟩) ⟨ tag ⟩) q★
  after-ground =
    structural-catchup-compose-target-cast tag child residual


structural-source-injection-ground-extra-cast-right-at :
    ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {H : Ty Δᴸ} {B G : Ty Δᴿ}
    {νᴸ : Env∼ Δᴸ} {νᴿ : Env∼ Δᴿ}
    ⦃ Hᵍ : Ground H ⦄ ⦃ H∼★ : νᴸ ⊢ H ∼★ ⦄
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : νᴿ ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
    {p : H ⊑ᵂ⟨ W ⟩ B}
    {q★ : ★ ⊑ᵂ⟨ W ⟩ ★}
  → (cᴿ : νᴿ ⊢ B ∼ G)
  → StructuralExtraCastRightAt (castSize (_! cᴿ))
  → ground-other-decreaseᵀ
  → B ≢ G
  → Value M
  → Value M′
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → StructuralCatchupRightResult W γ
      (M ⟨ _! ⦃ Hᵍ ⦄ ⦃ H∼★ ⦄ (idᵍ Hᵍ)
        ⦃ ground-nonstar Hᵍ ⦄ ⟩)
      (M′ ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ cᴿ ⟩)
      q★
structural-source-injection-ground-extra-cast-right-at
    {W = W} {γ = γ} {M = M} {M′ = M′} {H = H} {B = B}
    {G = G} {νᴸ = νᴸ} {νᴿ = νᴿ}
    ⦃ Hᵍ = Hᵍ ⦄ ⦃ H∼★ = H∼★ ⦄
    ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
    ⦃ Bns = Bns ⦄ {p = p} {q★ = q★}
    cᴿ smaller-extra ground-other-decrease B≢G vM vM′ rel =
  structural-catchup-prepend-keep-stutter
    (pure-step (ground ⦃ Gns = ground-nonstar Gᵍ ⦄ vM′ B≢G))
    after-ground
  where
  Htag = _! ⦃ Hᵍ ⦄ ⦃ H∼★ ⦄ (idᵍ Hᵍ)
    ⦃ ground-nonstar Hᵍ ⦄
  Gtag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
    ⦃ ground-nonstar Gᵍ ⦄

  qHG : H ⊑ᵂ⟨ W ⟩ G
  qHG = source-ground-cast-witness {W = W} {H = H} {B = B}
    {G = G} {ν = νᴿ} Hᵍ Gᵍ Bns cᴿ p

  child : StructuralCatchupRightResult W γ M (M′ ⟨ cᴿ ⟩) qHG
  child =
    smaller-extra cᴿ (ground-other-decrease cᴿ)
      (CTI2.⊑cast² cᴿ rel qHG) vM vM′

  plan = StructuralCatchupRightResult.structural-ext child
  ext = structural-world-extendᴿ plan
  χs = StructuralCatchupRightResult.χs child
  Gtagχ = applyConsistencies χs Gtag

  residual : StructuralCatchupRightResult
      (StructuralCatchupRightResult.W′ child)
      (ECR.mapCtxᴿ ext γ)
      (M ⟨ Htag ⟩)
      (StructuralCatchupRightResult.N′ child ⟨ Gtagχ ⟩)
      (ECR.transport⊑ᵂ ext q★)
  residual =
    structural-catchup-refl
      (StructuralCatchupRightResult.final-value child
        《 applyConsistencies-Inert χs
          (inj ⦃ Gns = ground-nonstar Gᵍ ⦄) 》)
      (CTI2.cast⊑cast² Htag Gtagχ
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ ext q★))

  after-ground : StructuralCatchupRightResult W γ
      (M ⟨ Htag ⟩)
      ((M′ ⟨ cᴿ ⟩) ⟨ Gtag ⟩)
      q★
  after-ground =
    structural-catchup-compose-paired-target-cast Htag Gtag
      child residual


structural-project-same-extra-cast-right-at : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {G : Ty Δᴿ} {μ ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    ⦃ ★∼G : ν ⊢★∼ G ⦄
    {p★ : A ⊑ᵂ⟨ W ⟩ ★} {qG : A ⊑ᵂ⟨ W ⟩ G}
  → RightInjInversion²
  → Value M
  → Value N
  → W ∣ γ ⊢² M ⊑
      N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ {μ = μ} Gᵍ)
        ⦃ ground-nonstar Gᵍ ⦄ ⟩
      ∶ p★
  → StructuralCatchupRightResult W γ M
      ((N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ {μ = μ} Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
        ⟨ ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ {μ = ν} Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
      qG
structural-project-same-extra-cast-right-at {W = W} {γ = γ}
    {M = M} {N = N} {A = A} {G = G} {μ = μ} {ν = ν}
    ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ ⦃ ★∼G = ★∼G ⦄
    {p★ = p★} {qG = qG} inversion vM vN rel-tag =
  structural-catchup-keep-step vN
    (pure-step (tag-untag ⦃ Gns = ground-nonstar Gᵍ ⦄ vN))
    (exposed-project-same-step-inversion-⊑cast²
      inversion {W = W} {γ = γ} {M = M} {N = N}
      {A = A} {G = G} {μ = μ} {Gᵍ = Gᵍ}
      {G∼★ = G∼★} {p★ = p★}
      vM vN rel-tag qG)


structural-paired-project-same-extra-cast-right-at : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {C A : Ty Δᴸ} {G : Ty Δᴿ}
    {νᴸ : Env∼ Δᴸ} {μ νᴿ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    ⦃ ★∼G : νᴿ ⊢★∼ G ⦄
    {p★ : C ⊑ᵂ⟨ W ⟩ ★}
    {qG : C ⊑ᵂ⟨ W ⟩ G}
    {q : A ⊑ᵂ⟨ W ⟩ G}
  → RightInjInversion²
  → (cᴸ : νᴸ ⊢ C ∼ A)
  → Value M
  → Value N
  → Inert cᴸ
  → W ∣ γ ⊢² M ⊑
      N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ {μ = μ} Gᵍ)
        ⦃ ground-nonstar Gᵍ ⦄ ⟩
      ∶ p★
  → StructuralCatchupRightResult W γ (M ⟨ cᴸ ⟩)
      ((N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ {μ = μ} Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
        ⟨ ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ {μ = νᴿ} Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
      q
structural-paired-project-same-extra-cast-right-at {W = W} {γ = γ}
    {M = M} {N = N} {C = C} {G = G} {μ = μ}
    ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ ⦃ ★∼G = ★∼G ⦄
    {p★ = p★} {qG = qG} {q = q}
    inversion cᴸ vM vN inertᴸ rel-tag =
  structural-catchup-keep-step vN
    (pure-step (tag-untag ⦃ Gns = ground-nonstar Gᵍ ⦄ vN))
    (CTI2.cast⊑² cᴸ core q)
  where
  core : W ∣ γ ⊢² M ⊑ N ∶ qG
  core =
    exposed-project-same-step-inversion-⊑cast²
      inversion {W = W} {γ = γ} {M = M} {N = N}
      {A = C} {G = G} {μ = μ} {Gᵍ = Gᵍ}
      {G∼★ = G∼★} {p★ = p★}
      vM vN rel-tag qG


structural-project-expand-extra-cast-right-at : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {G B : Ty Δᴿ} {μ ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    ⦃ ★∼G : ν ⊢★∼ G ⦄ ⦃ Bns : NonStar B ⦄
    {p★ : A ⊑ᵂ⟨ W ⟩ ★} {qB : A ⊑ᵂ⟨ W ⟩ B}
  → RightInjInversion²
  → (c : ν ⊢ G ∼ B)
  → StructuralExtraCastRightAt (castSize (？ c))
  → project-expand-decreaseᵀ
  → G ≢ B
  → Value M
  → Value N
  → W ∣ γ ⊢² M ⊑
      N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ {μ = μ} Gᵍ)
        ⦃ ground-nonstar Gᵍ ⦄ ⟩
      ∶ p★
  → StructuralCatchupRightResult W γ M
      ((N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ {μ = μ} Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
        ⟨ ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⟩)
      qB
structural-project-expand-extra-cast-right-at {W = W} {γ = γ}
    {M = M} {N = N} {A = A} {G = G} {B = B}
    {μ = μ} {ν = ν}
    ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ ⦃ ★∼G = ★∼G ⦄
    ⦃ Bns = Bns ⦄ {p★ = p★} {qB = qB}
    inversion c smaller-extra project-expand-decrease G≢B vM vN rel-tag =
  structural-catchup-prepend-keep
    (pure-step (expand ⦃ Gns = ground-nonstar Gᵍ ⦄
      (vN 《 inj ⦃ Gns = ground-nonstar Gᵍ ⦄ 》) G≢B))
    reduct-rel
    combined
  where
  tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ {μ = μ} Gᵍ)
    ⦃ ground-nonstar Gᵍ ⦄
  proj = ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ (idᵍ {μ = ν} Gᵍ)
    ⦃ ground-nonstar Gᵍ ⦄

  qG : A ⊑ᵂ⟨ W ⟩ G
  qG = target-expand-cast-witness {W = W} {A = A} {G = G}
    {B = B} Gᵍ Bns c p★ qB

  reduct-rel : W ∣ γ ⊢² M ⊑
      (N ⟨ tag ⟩) ⟨ proj ⟩ ⟨ c ⟩ ∶ qB
  reduct-rel =
    exposed-project-expand-step-inversion-⊑cast²
      inversion {W = W} {γ = γ} {M = M} {N = N}
      {A = A} {G = G} {B = B} {μ = μ} {ν = ν}
      {Gᵍ = Gᵍ} {G∼★ = G∼★} {★∼G = ★∼G}
      {Bns = Bns} {p★ = p★}
      vM vN rel-tag c qG qB

  child : StructuralCatchupRightResult W γ M
      ((N ⟨ tag ⟩) ⟨ proj ⟩) qG
  child =
    structural-project-same-extra-cast-right-at
      inversion vM vN rel-tag

  plan = StructuralCatchupRightResult.structural-ext child
  ext = structural-world-extendᴿ plan
  χs = StructuralCatchupRightResult.χs child
  cχ = applyConsistencies χs c
  cχ< =
    subst≡ (λ n → n < castSize (？ c))
      (sym (castSize-applyConsistencies χs c))
      (project-expand-decrease c)

  residual : StructuralCatchupRightResult
      (StructuralCatchupRightResult.W′ child)
      (ECR.mapCtxᴿ ext γ)
      M
      (StructuralCatchupRightResult.N′ child ⟨ cχ ⟩)
      (ECR.transport⊑ᵂ ext qB)
  residual =
    smaller-extra cχ cχ<
      (CTI2.⊑cast² cχ
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ ext qB))
      vM (StructuralCatchupRightResult.final-value child)

  combined =
    structural-catchup-compose-target-cast c child residual


structural-paired-project-expand-extra-cast-right-at : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {C A : Ty Δᴸ} {G B : Ty Δᴿ}
    {νᴸ : Env∼ Δᴸ} {μ νᴿ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    ⦃ ★∼G : νᴿ ⊢★∼ G ⦄ ⦃ Bns : NonStar B ⦄
    {p★ : C ⊑ᵂ⟨ W ⟩ ★}
    {qG : C ⊑ᵂ⟨ W ⟩ G}
    {qB : A ⊑ᵂ⟨ W ⟩ B}
  → RightInjInversion²
  → (cᴸ : νᴸ ⊢ C ∼ A)
  → (cᴿ : νᴿ ⊢ G ∼ B)
  → StructuralExtraCastRightAt (castSize (？ cᴿ))
  → project-expand-decreaseᵀ
  → G ≢ B
  → Value M
  → Value N
  → Inert cᴸ
  → W ∣ γ ⊢² M ⊑
      N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ {μ = μ} Gᵍ)
        ⦃ ground-nonstar Gᵍ ⦄ ⟩
      ∶ p★
  → StructuralCatchupRightResult W γ (M ⟨ cᴸ ⟩)
      ((N ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ {μ = μ} Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
        ⟨ ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ cᴿ ⟩)
      qB
structural-paired-project-expand-extra-cast-right-at {W = W} {γ = γ}
    {M = M} {N = N} {C = C} {A = A} {G = G} {B = B}
    {μ = μ} {νᴿ = νᴿ}
    ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄ ⦃ ★∼G = ★∼G ⦄
    ⦃ Bns = Bns ⦄ {p★ = p★} {qG = qG} {qB = qB}
    inversion cᴸ cᴿ smaller-extra project-expand-decrease G≢B
    vM vN inertᴸ rel-tag =
  structural-catchup-prepend-keep-stutter
    (pure-step (expand ⦃ Gns = ground-nonstar Gᵍ ⦄
      (vN 《 inj ⦃ Gns = ground-nonstar Gᵍ ⦄ 》) G≢B))
    after-expand
  where
  tag = _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ {μ = μ} Gᵍ)
    ⦃ ground-nonstar Gᵍ ⦄
  proj-core = idᵍ {μ = νᴿ} Gᵍ
  proj = ？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ proj-core
    ⦃ ground-nonstar Gᵍ ⦄

  core : W ∣ γ ⊢² M ⊑ N ∶ qG
  core =
    exposed-project-same-step-inversion-⊑cast²
      inversion {W = W} {γ = γ} {M = M} {N = N}
      {A = C} {G = G} {μ = μ} {Gᵍ = Gᵍ}
      {G∼★ = G∼★} {p★ = p★}
      vM vN rel-tag qG

  cᴿ< =
    project-expand-decrease cᴿ

  residual : StructuralCatchupRightResult W γ (M ⟨ cᴸ ⟩)
      (N ⟨ cᴿ ⟩) qB
  residual =
    smaller-extra cᴿ cᴿ<
      (CTI2.cast⊑cast² cᴸ cᴿ core qB)
      (vM 《 inertᴸ 》)
      vN

  after-expand : StructuralCatchupRightResult W γ (M ⟨ cᴸ ⟩)
      ((N ⟨ tag ⟩) ⟨ proj ⟩ ⟨ cᴿ ⟩) qB
  after-expand =
    structural-catchup-prepend-keep-stutter
      (ξ-⟨⟩
        (pure-step
          (tag-untag ⦃ Gns = ground-nonstar Gᵍ ⦄ vN))
        refl)
      residual


structural-bot-elim-extra-cast-right-at : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ `∀ ★}
  → W ∣ γ ⊢² M ⊑ M′ ⟨ bot-elim {μ = ν} ⟩ ∶ q
  → Value M
  → Value M′
  → StructuralCatchupRightResult W γ M
      (M′ ⟨ bot-elim {μ = ν} ⟩) q
structural-bot-elim-extra-cast-right-at rel vM vM′ =
  ⊥-elim (target-bot-elim-refutation vM′ rel)


structural-bot-intro-extra-cast-right-at : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ `∀ (＇ zero)}
  → W ∣ γ ⊢² M ⊑ M′ ⟨ bot-intro {μ = ν} ⟩ ∶ q
  → Value M
  → Value M′
  → StructuralCatchupRightResult W γ M
      (M′ ⟨ bot-intro {μ = ν} ⟩) q
structural-bot-intro-extra-cast-right-at rel vM vM′ =
  ⊥-elim (target-bot-intro-refutation vM rel)
