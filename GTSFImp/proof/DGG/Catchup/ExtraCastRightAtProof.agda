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
   structural-catchup-compose-target-cast)
open import proof.DGG.Catchup.StructuralWorldExtendProof using
  (structural-world-extendᴿ)
open import proof.DGG.Catchup.TargetCastStepInversionProof using
  (exposed-ground-step-inversion-⊑cast²; target-ground-cast-witness;
   target-expand-cast-witness;
   exposed-project-same-step-inversion-⊑cast²;
   exposed-project-expand-step-inversion-⊑cast²;
   matched-conceal-partner-target-id-core;
   matched-conceal-partner-target-id-framed-core;
   source-conceal-partner-target-id-core;
   source-conceal-partner-target-id-framed-core;
   target-id-step-inversion)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


source-value-target-bottom-impossible : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ}
  → Value M
  → ⟨ Δᴸ , CTI2.sourceStoreʷ W , CTI2.srcCtxʷ γ ⟩ ⊢ M ⦂ A
  → A ⊑ᵂ⟨ W ⟩ `∀ (＇ zero)
  → ⊥
source-value-target-bottom-impossible {W = W} {γ = γ}
    {M = M} {A = `∀ A} vM M⊢ (I.∀⊑∀ body) =
  no-bot-value vM
    (subst≡
      (λ A′ → ⟨ _ , CTI2.sourceStoreʷ W , CTI2.srcCtxʷ γ ⟩
        ⊢ M ⦂ `∀ A′)
      body-eq M⊢)
  where
  body-eq : A ≡ (＇ zero)
  body-eq =
    renameᵗ-injective
      (ext-injective (toRenameᵗ-injective (CTI2.ηᴸʷ W)))
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


variable-ground-other-impossible : ∀ {Δ} {μ : Env∼ Δ}
    {X : TyVar Δ} {G : Ty Δ}
  → Ground G
  → (c : μ ⊢ ＇ X ∼ G)
  → ＇ X ≢ G
  → ⊥
variable-ground-other-impossible (＇ X) (id (＇ .X)) X≢X =
  X≢X refl
variable-ground-other-impossible ∀★
    ((C.gen_ ⦃ _ ⦄ ⦃ () ⦄ c) A≢★) X≢G


rep★-ground-step-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ?}
    {M′ : Term Δᴿ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → CTI2.Rep★PartnerOK W X P Xᴿ? (M′ ⟨ _! c ⟩)
  → CTI2.Rep★PartnerOK W X P Xᴿ?
      ((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
rep★-ground-step-core c (CTI2.rep★-untagged ())
rep★-ground-step-core c (CTI2.rep★-nonvar-tag Gnv) =
  CTI2.rep★-nonvar-tag Gnv
rep★-ground-step-core c (CTI2.rep★-var-tag aligned) =
  CTI2.rep★-var-tag aligned
rep★-ground-step-core c
    (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
  CTI2.rep★-matched-inner-tags X₂≢X aligned
rep★-ground-step-core c (CTI2.rep★-round-trip ok) =
  CTI2.rep★-round-trip (rep★-ground-step-core c ok)


seal-partner-ground-step-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {R : Ty Δᴸ} {Xᴿ?}
    {M′ : Term Δᴿ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → B ≢ G
  → CTI2.SealPartnerOK W X P R Xᴿ? (M′ ⟨ _! c ⟩)
  → CTI2.SealPartnerOK W X P R Xᴿ?
      ((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
seal-partner-ground-step-core c B≢G
    (CTI2.star-rep-target no-target ok) =
  CTI2.star-rep-target no-target (rep★-ground-step-core c ok)
seal-partner-ground-step-core c B≢G (CTI2.plain-target ())
seal-partner-ground-step-core ⦃ Gᵍ = Gᵍ ⦄ c B≢G
    (CTI2.name-protected-target {Y = Y}) =
  ⊥-elim (variable-ground-other-impossible Gᵍ c B≢G)


source-conceal-partner-ground-step-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ : Term Δᴿ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → B ≢ G
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ? (M′ ⟨ _! c ⟩)
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ?
      ((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
source-conceal-partner-ground-step-core c B≢G
    (CTI2.seal-partner-ok ok) =
  CTI2.seal-partner-ok (seal-partner-ground-step-core c B≢G ok)
source-conceal-partner-ground-step-core c B≢G
    CTI2.fun-conceal-target =
  CTI2.fun-conceal-target
source-conceal-partner-ground-step-core c B≢G
    CTI2.all-conceal-target =
  CTI2.all-conceal-target
source-conceal-partner-ground-step-core c B≢G
    CTI2.id-conceal-target =
  CTI2.id-conceal-target


rep★-ground-step-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ?}
    {M′ : Term Δᴿ} {B G C D : Ty Δᴿ} {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → (d : μ ⊢ C ∼ D)
  → CTI2.Rep★PartnerOK W X P Xᴿ? ((M′ ⟨ _! c ⟩) ⟨ d ⟩)
  → CTI2.Rep★PartnerOK W X P Xᴿ?
      (((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩) ⟨ d ⟩)
rep★-ground-step-framed-core c d (CTI2.rep★-untagged ())
rep★-ground-step-framed-core c d (CTI2.rep★-nonvar-tag Gnv) =
  CTI2.rep★-nonvar-tag Gnv
rep★-ground-step-framed-core c d (CTI2.rep★-var-tag aligned) =
  CTI2.rep★-var-tag aligned
rep★-ground-step-framed-core c d
    (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
  CTI2.rep★-matched-inner-tags X₂≢X aligned
rep★-ground-step-framed-core c d (CTI2.rep★-round-trip ok) =
  CTI2.rep★-round-trip (rep★-ground-step-framed-core c d ok)


seal-partner-ground-step-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {R : Ty Δᴸ} {Xᴿ?}
    {M′ : Term Δᴿ} {B G C D : Ty Δᴿ} {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → (d : μ ⊢ C ∼ D)
  → CTI2.SealPartnerOK W X P R Xᴿ? ((M′ ⟨ _! c ⟩) ⟨ d ⟩)
  → CTI2.SealPartnerOK W X P R Xᴿ?
      (((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩) ⟨ d ⟩)
seal-partner-ground-step-framed-core c d
    (CTI2.star-rep-target no-target ok) =
  CTI2.star-rep-target no-target
    (rep★-ground-step-framed-core c d ok)
seal-partner-ground-step-framed-core c d (CTI2.plain-target ())


source-conceal-partner-ground-step-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ : Term Δᴿ} {B G C D : Ty Δᴿ}
    {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → (d : μ ⊢ C ∼ D)
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ?
      ((M′ ⟨ _! c ⟩) ⟨ d ⟩)
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ?
      (((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩) ⟨ d ⟩)
source-conceal-partner-ground-step-framed-core c d
    (CTI2.seal-partner-ok ok) =
  CTI2.seal-partner-ok
    (seal-partner-ground-step-framed-core c d ok)
source-conceal-partner-ground-step-framed-core c d
    CTI2.fun-conceal-target =
  CTI2.fun-conceal-target
source-conceal-partner-ground-step-framed-core c d
    CTI2.all-conceal-target =
  CTI2.all-conceal-target
source-conceal-partner-ground-step-framed-core c d
    CTI2.id-conceal-target =
  CTI2.id-conceal-target


matched-conceal-partner-ground-step-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ : Term Δᴿ} {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → B ≢ G
  → CTI2.MatchedConcealPartnerOK W P c₀ Xᴿ? (M′ ⟨ _! c ⟩)
  → CTI2.MatchedConcealPartnerOK W P c₀ Xᴿ?
      ((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩)
matched-conceal-partner-ground-step-core c B≢G
    (CTI2.matched-seal-star-partner ok) =
  CTI2.matched-seal-star-partner (rep★-ground-step-core c ok)
matched-conceal-partner-ground-step-core c B≢G
    (CTI2.matched-seal-nonstar Rns) =
  CTI2.matched-seal-nonstar Rns
matched-conceal-partner-ground-step-core c B≢G
    CTI2.matched-fun-conceal-target =
  CTI2.matched-fun-conceal-target
matched-conceal-partner-ground-step-core c B≢G
    CTI2.matched-all-conceal-target =
  CTI2.matched-all-conceal-target
matched-conceal-partner-ground-step-core c B≢G
    CTI2.matched-id-conceal-target =
  CTI2.matched-id-conceal-target


matched-conceal-partner-ground-step-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ : Term Δᴿ} {B G C D : Ty Δᴿ}
    {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : ν ⊢ G ∼★ ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ B ∼ G)
  → (d : μ ⊢ C ∼ D)
  → CTI2.MatchedConcealPartnerOK W P c₀ Xᴿ?
      ((M′ ⟨ _! c ⟩) ⟨ d ⟩)
  → CTI2.MatchedConcealPartnerOK W P c₀ Xᴿ?
      (((M′ ⟨ c ⟩)
        ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ)
          ⦃ ground-nonstar Gᵍ ⦄ ⟩) ⟨ d ⟩)
matched-conceal-partner-ground-step-framed-core c d
    (CTI2.matched-seal-star-partner ok) =
  CTI2.matched-seal-star-partner
    (rep★-ground-step-framed-core c d ok)
matched-conceal-partner-ground-step-framed-core c d
    (CTI2.matched-seal-nonstar Rns) =
  CTI2.matched-seal-nonstar Rns
matched-conceal-partner-ground-step-framed-core c d
    CTI2.matched-fun-conceal-target =
  CTI2.matched-fun-conceal-target
matched-conceal-partner-ground-step-framed-core c d
    CTI2.matched-all-conceal-target =
  CTI2.matched-all-conceal-target
matched-conceal-partner-ground-step-framed-core c d
    CTI2.matched-id-conceal-target =
  CTI2.matched-id-conceal-target


rep★-projection-impossible : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ?}
    {M′ : Term Δᴿ} {G B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → CTI2.Rep★PartnerOK W X P Xᴿ? (M′ ⟨ ？ c ⟩)
  → ⊥
rep★-projection-impossible c (CTI2.rep★-untagged ())
rep★-projection-impossible c (CTI2.rep★-round-trip ok) =
  rep★-projection-impossible c ok


source-conceal-partner-projection-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ N : Term Δᴿ} {G B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ? (M′ ⟨ ？ c ⟩)
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ? N
source-conceal-partner-projection-core c
    (CTI2.seal-partner-ok (CTI2.star-rep-target no-target ok)) =
  ⊥-elim (rep★-projection-impossible c ok)
source-conceal-partner-projection-core c
    (CTI2.seal-partner-ok (CTI2.plain-target ()))
source-conceal-partner-projection-core c CTI2.fun-conceal-target =
  CTI2.fun-conceal-target
source-conceal-partner-projection-core c CTI2.all-conceal-target =
  CTI2.all-conceal-target
source-conceal-partner-projection-core c CTI2.id-conceal-target =
  CTI2.id-conceal-target


rep★-projection-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ?}
    {M′ N : Term Δᴿ} {G B C D : Ty Δᴿ}
    {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → (d : μ ⊢ C ∼ D)
  → CTI2.Rep★PartnerOK W X P Xᴿ? ((M′ ⟨ ？ c ⟩) ⟨ d ⟩)
  → CTI2.Rep★PartnerOK W X P Xᴿ? (N ⟨ d ⟩)
rep★-projection-framed-core c d (CTI2.rep★-untagged ())
rep★-projection-framed-core c d (CTI2.rep★-nonvar-tag Gnv) =
  CTI2.rep★-nonvar-tag Gnv
rep★-projection-framed-core c d (CTI2.rep★-var-tag aligned) =
  CTI2.rep★-var-tag aligned
rep★-projection-framed-core c d
    (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
  CTI2.rep★-matched-inner-tags X₂≢X aligned
rep★-projection-framed-core c d (CTI2.rep★-round-trip ok) =
  CTI2.rep★-round-trip (rep★-projection-framed-core c d ok)


seal-partner-projection-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {R : Ty Δᴸ} {Xᴿ?}
    {M′ N : Term Δᴿ} {G B C D : Ty Δᴿ}
    {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → (d : μ ⊢ C ∼ D)
  → CTI2.SealPartnerOK W X P R Xᴿ? ((M′ ⟨ ？ c ⟩) ⟨ d ⟩)
  → CTI2.SealPartnerOK W X P R Xᴿ? (N ⟨ d ⟩)
seal-partner-projection-framed-core c d
    (CTI2.star-rep-target no-target ok) =
  CTI2.star-rep-target no-target
    (rep★-projection-framed-core c d ok)
seal-partner-projection-framed-core c d (CTI2.plain-target ())


source-conceal-partner-projection-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ N : Term Δᴿ} {G B C D : Ty Δᴿ}
    {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → (d : μ ⊢ C ∼ D)
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ?
      ((M′ ⟨ ？ c ⟩) ⟨ d ⟩)
  → CTI2.SourceConcealPartnerOK W P c₀ Xᴿ? (N ⟨ d ⟩)
source-conceal-partner-projection-framed-core c d
    (CTI2.seal-partner-ok ok) =
  CTI2.seal-partner-ok
    (seal-partner-projection-framed-core c d ok)
source-conceal-partner-projection-framed-core c d
    CTI2.fun-conceal-target =
  CTI2.fun-conceal-target
source-conceal-partner-projection-framed-core c d
    CTI2.all-conceal-target =
  CTI2.all-conceal-target
source-conceal-partner-projection-framed-core c d
    CTI2.id-conceal-target =
  CTI2.id-conceal-target


matched-conceal-partner-projection-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ N : Term Δᴿ} {G B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → CTI2.MatchedConcealPartnerOK W P c₀ Xᴿ? (M′ ⟨ ？ c ⟩)
  → CTI2.MatchedConcealPartnerOK W P c₀ Xᴿ? N
matched-conceal-partner-projection-core c
    (CTI2.matched-seal-star-partner ok) =
  ⊥-elim (rep★-projection-impossible c ok)
matched-conceal-partner-projection-core c
    (CTI2.matched-seal-nonstar Rns) =
  CTI2.matched-seal-nonstar Rns
matched-conceal-partner-projection-core c
    CTI2.matched-fun-conceal-target =
  CTI2.matched-fun-conceal-target
matched-conceal-partner-projection-core c
    CTI2.matched-all-conceal-target =
  CTI2.matched-all-conceal-target
matched-conceal-partner-projection-core c
    CTI2.matched-id-conceal-target =
  CTI2.matched-id-conceal-target


matched-conceal-partner-projection-framed-core : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A₀ A₁ : Ty Δᴸ} {c₀ : Conv↓ Δᴸ A₀ A₁}
    {Xᴿ?} {M′ N : Term Δᴿ} {G B C D : Ty Δᴿ}
    {ν μ : Env∼ Δᴿ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : ν ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : ν ⊢ G ∼ B)
  → (d : μ ⊢ C ∼ D)
  → CTI2.MatchedConcealPartnerOK W P c₀ Xᴿ?
      ((M′ ⟨ ？ c ⟩) ⟨ d ⟩)
  → CTI2.MatchedConcealPartnerOK W P c₀ Xᴿ? (N ⟨ d ⟩)
matched-conceal-partner-projection-framed-core c d
    (CTI2.matched-seal-star-partner ok) =
  CTI2.matched-seal-star-partner
    (rep★-projection-framed-core c d ok)
matched-conceal-partner-projection-framed-core c d
    (CTI2.matched-seal-nonstar Rns) =
  CTI2.matched-seal-nonstar Rns
matched-conceal-partner-projection-framed-core c d
    CTI2.matched-fun-conceal-target =
  CTI2.matched-fun-conceal-target
matched-conceal-partner-projection-framed-core c d
    CTI2.matched-all-conceal-target =
  CTI2.matched-all-conceal-target
matched-conceal-partner-projection-framed-core c d
    CTI2.matched-id-conceal-target =
  CTI2.matched-id-conceal-target


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
    (source-conceal-partner-target-id-core a)
    (source-conceal-partner-target-id-framed-core a)
    (matched-conceal-partner-target-id-core a)
    (matched-conceal-partner-target-id-framed-core a)


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
    (source-conceal-partner-ground-step-core c B≢G)
    (source-conceal-partner-ground-step-framed-core c)
    (matched-conceal-partner-ground-step-core c B≢G)
    (matched-conceal-partner-ground-step-framed-core c)
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
    (source-conceal-partner-projection-core
      ⦃ Bns = ground-nonstar Gᵍ ⦄ proj)
    (source-conceal-partner-projection-framed-core
      ⦃ Bns = ground-nonstar Gᵍ ⦄ proj)
    (matched-conceal-partner-projection-core
      ⦃ Bns = ground-nonstar Gᵍ ⦄ proj)
    (matched-conceal-partner-projection-framed-core
      ⦃ Bns = ground-nonstar Gᵍ ⦄ proj)
  where
  proj = idᵍ {μ = ν} Gᵍ


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
    (source-conceal-partner-projection-core c)
    (source-conceal-partner-projection-framed-core c)
    (matched-conceal-partner-projection-core c)
    (matched-conceal-partner-projection-framed-core c)
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
