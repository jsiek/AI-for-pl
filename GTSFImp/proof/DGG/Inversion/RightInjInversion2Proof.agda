module proof.DGG.Inversion.RightInjInversion2Proof where

-- File Charter:
--   * Proves the v2 right-injection inversion statement relative to supplied
--     target-walk and source-star-chain inhabitants.
--   * Carries no WFWorld, ParkedWorld, or OpenStrata premise; frozen target
--     rebases make the remaining seal-chain obstruction impossible.
--   * Depends on the stable SpineValueDef surface, TargetWalkDef, and
--     TargetWalkSupport.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore using
  (TyStore; store-lift; store-bind; _∋_⦂_; Z∋; S-lift∋;
   S-bind∋)
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _↪ᵗ_; keep; skip; toRenameᵗ;
   id; _!; ∀ᶜ_; gen_; inst_)
import Consistency as C
import proof.Consistency as PC
open import Conversion using
  (Conv↑; Conv↓; _⊢↓_; `∀↑_; `∀↓_; _↦↑_; _↦↓_;
   ⊢↓-seal)
open import Imprecision
open import Primitives using (Const; κℕ; κ𝔹)
open import CastTerms
open import Reduction
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.Inversion.SpineValueDef as SVD
import proof.DGG.WorldDecay as WD
import proof.DGG.TermImpDecay as TD
import proof.DGG.TagTransport as TT
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.SealTransferCore as STC
open import proof.DGG.ConvImp using
  (pivot-id-endpoints↑; pivot-id-endpoints↓)
open CTX using
  (World;
   ηᴸʷ;
   ηᴿʷ;
   impEnvʷ;
   sourceStoreʷ;
   targetStoreʷ;
   embedᴿ;
   _⊑ᵂ⟨_⟩_;
   CtxImp;
   ctx-imp)
open CTI2 using (_∣_⊢²_⊑_∶_)
open SVD using
  (SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal;
   sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all;
   varv-seal; var-value-view; right-tag-variable-view;
   variable-obligation-aligns; seal-rebase-target)
open import proof.ImprecisionConsistency using
  (ground-cast-source⊑; source-occurs-target; rename-occurs;
   ext-injective; toRenameᵗ-injective; nonstar-from-≢★; rename-⊑;
   fin-suc-injective; nonvar-occurs-nonstar)
import proof.Imprecision as PI
open import proof.TypeInTermSubst using (toRename-keep-eq)
open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)
open import proof.DGG.Inversion.TargetWalkDef using
  (TargetTagSealWalk; TargetSourceStarChain;
   target-source-star-chain-final; target-source-star-chain-residual;
   target-source-star-chain-paired; target-source-star-chain-payload)
open import proof.DGG.Inversion.TargetWalkSupport

------------------------------------------------------------------------
-- Higher-order right-injection inversion for spine values
------------------------------------------------------------------------

module _
    (target-tag-seal-walk : TargetTagSealWalk)
    (target-source-star-chain : TargetSourceStarChain)
    where

  right-var-obligation-nonstar : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {R : Ty Δᴸ} {Y : TyVar Δᴿ}
    → R ⊑ᵂ⟨ W ⟩ (＇ Y)
    → NonStar R
  right-var-obligation-nonstar {W = W} {R = R} {Y = Y} p
      with SPT.right-var-obligation-view {W = W} {R = R} {Y = Y} p
  right-var-obligation-nonstar p | X₂ , refl , aligned =
    nonstar-X

  right-inj-reveal-all-id² : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ γ′ : CtxImp W}
      {V : Term Δᴸ} {N : Term Δᴿ}
      {A B : Ty (suc Δᴸ)} {H : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {c : Conv↑ (suc Δᴸ) A B}
      {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
      {cH : ν ⊢ H ∼ H} {p : `∀ A ⊑ᵂ⟨ W ⟩ ★}
    → SpineValue V
    → Value N
    → CTX.SameCtx γ γ′
    → store-lift (sourceStoreʷ W) Conv.⊢↑[ nothing ] c
    → W ∣ γ′ ⊢² V
        ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
    → (q : `∀ B ⊑ᵂ⟨ W ⟩ H)
    → W ∣ γ ⊢² V ↑ `∀↑ c ⊑ N ∶ q


  right-inj-inversion² : RightInjInversion²

  -- Target-only cast: the premise already carries the tag obligation.
  right-inj-inversion² sv vN
      (CTI2.⊑cast² {p = p₀} c′ prem q₀) q =
    subst≡ (λ r → _ ∣ _ ⊢² _ ⊑ _ ∶ r) (PI.⊑-unique p₀ q) prem

  -- Paired cast: keep the source cast as a source-only cast.
  right-inj-inversion² sv vN
      (CTI2.cast⊑cast² c c′ prem q₀) q =
    CTI2.cast⊑² c prem q

  -- Source-only cast around an injection value: no obligation matches.
  right-inj-inversion² {gH = ＇ Y} (sv-cast sv inj)
    vN (CTI2.cast⊑² c prem q₀) ()
  right-inj-inversion² {gH = ‵ ι} (sv-cast sv inj)
    vN (CTI2.cast⊑² c prem q₀) ()
  right-inj-inversion² {gH = ★⇒★} (sv-cast sv inj)
    vN (CTI2.cast⊑² c prem q₀) ()
  right-inj-inversion² {gH = ∀★} (sv-cast sv inj)
    vN (CTI2.cast⊑² c prem q₀) ()

  -- Source-only function cast: the premise components rebuild the
  -- premise-level tag obligation.
  right-inj-inversion² {gH = ★⇒★} (sv-cast sv fun)
      vN (CTI2.cast⊑² {p = ⇒⊑★ pA pB} c prem q₀) (⇒⊑⇒ qA qB) =
    CTI2.cast⊑² c
      (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
      (⇒⊑⇒ qA qB)
  right-inj-inversion² {gH = ＇ Y} (sv-cast sv fun)
    vN (CTI2.cast⊑² c prem q₀) ()
  right-inj-inversion² {gH = ‵ ι} (sv-cast sv fun)
    vN (CTI2.cast⊑² c prem q₀) ()
  right-inj-inversion² {gH = ∀★} (sv-cast sv fun)
    vN (CTI2.cast⊑² c prem q₀) ()

  -- Source-only universal cast: chase the tag through the cast with the
  -- embedded consistency evidence.
  right-inj-inversion² {W = W} {gH = gH}
      (sv-cast sv (all {c = c₁}))
      vN (CTI2.cast⊑² {p = p₀} .(∀ᶜ c₁) prem q₀) q =
    CTI2.cast⊑² (∀ᶜ c₁)
      (right-inj-inversion² sv vN prem
        (ground-cast-source⊑ (PC.renameGroundᵐ (ηᴿʷ W) gH) nonstar-∀
          (C.renameᵐᶜ (ηᴸʷ W) (∀ᶜ c₁)) p₀ q₀ q))
      q

  -- Source-only generalization cast: same, with the gen tag's source.
  right-inj-inversion² {W = W} {gH = gH}
      (sv-cast sv (genᵥ A≢★ safe))
      vN (CTI2.cast⊑² {p = p₀} c prem q₀) q =
    CTI2.cast⊑² c
      (right-inj-inversion² sv vN prem
        (ground-cast-source⊑ (PC.renameGroundᵐ (ηᴿʷ W) gH)
          (C.renameNonStar (toRenameᵗ (ηᴸʷ W))
            (nonstar-from-≢★ A≢★))
          (C.renameᵐᶜ (ηᴸʷ W) c) p₀ q₀ q))
      q

  -- Type abstraction against a non-∀ ground: only the ∀⊑ view is
  -- possible, and its body is exactly a left-only lifted premise.
  right-inj-inversion² {W = W} {gH = ＇ Y} (sv-Λ sv)
      vN (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV
        (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ＇ Y} body))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ＇ Y} (sv-Λ sv)
      vN (CTI2.Λ⊑²-smart-comma {A = A₀} Anv z∈A liftW
        liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (CTX.smartCommaLift-transport⊑ᵂ liftW
          (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ＇ Y} body)))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ‵ ι} (sv-Λ sv)
      vN (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV
        (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ‵ ι} body))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ‵ ι} (sv-Λ sv)
      vN (CTI2.Λ⊑²-smart-comma {A = A₀} Anv z∈A liftW
        liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (CTX.smartCommaLift-transport⊑ᵂ liftW
          (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ‵ ι} body)))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ★⇒★} (sv-Λ sv)
      vN (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV
        (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ★ ⇒ ★} body))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ★⇒★} (sv-Λ sv)
      vN (CTI2.Λ⊑²-smart-comma {A = A₀} Anv z∈A liftW
        liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (CTX.smartCommaLift-transport⊑ᵂ liftW
          (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ★ ⇒ ★} body)))
      (∀⊑ Anv′ z∈A′ body)

  -- Type abstraction against the ∀★ ground.  The Λ⊑² occurrence premise
  -- exposes the body's head, which rules out bot-elim, refutes ∀⊑∀ by
  -- occurrence preservation, and leaves the ∀⊑ rebuild.
  right-inj-inversion² {gH = ∀★} (sv-Λ sv)
    vN (CTI2.Λ⊑² () var-∈ liftγ vV M′⊢ prem q₀) q
  right-inj-inversion² {gH = ∀★} (sv-Λ sv)
    vN (CTI2.Λ⊑²-smart-comma () var-∈ liftW liftγ vV M′⊢ prem q₀) q
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN (CTI2.Λ⊑² {A = A₀} Anv (∈-fun-left z∈) liftγ vV
        (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑² Anv (∈-fun-left z∈) liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN (CTI2.Λ⊑²-smart-comma {A = A₀} Anv
        (∈-fun-left z∈) liftW liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑²-smart-comma Anv (∈-fun-left z∈) liftW liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (CTX.smartCommaLift-transport⊑ᵂ liftW
          (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body)))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN (CTI2.Λ⊑² Anv (∈-fun-left z∈) liftγ vV M′⊢ prem q₀)
      (∀⊑∀ qbody)
    with source-occurs-target refl qbody
           (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
             (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
             (∈-fun-left z∈))
  ... | ()
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN (CTI2.Λ⊑²-smart-comma Anv (∈-fun-left z∈) liftW
        liftγ vV M′⊢ prem q₀)
      (∀⊑∀ qbody)
    with source-occurs-target refl qbody
           (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
             (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
             (∈-fun-left z∈))
  ... | ()
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN (CTI2.Λ⊑² {A = A₀} Anv (∈-fun-right z∉ z∈) liftγ vV
        (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑² Anv (∈-fun-right z∉ z∈) liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN (CTI2.Λ⊑²-smart-comma {A = A₀} Anv
        (∈-fun-right z∉ z∈) liftW liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑²-smart-comma Anv (∈-fun-right z∉ z∈)
      liftW liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (CTX.smartCommaLift-transport⊑ᵂ liftW
          (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body)))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN
      (CTI2.Λ⊑² Anv (∈-fun-right z∉ z∈) liftγ vV M′⊢ prem q₀)
      (∀⊑∀ qbody)
    with source-occurs-target refl qbody
           (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
             (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
             (∈-fun-right z∉ z∈))
  ... | ()
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN
      (CTI2.Λ⊑²-smart-comma Anv (∈-fun-right z∉ z∈)
        liftW liftγ vV M′⊢ prem q₀)
      (∀⊑∀ qbody)
    with source-occurs-target refl qbody
           (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
             (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
             (∈-fun-right z∉ z∈))
  ... | ()
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN (CTI2.Λ⊑² {A = A₀} Anv (∈-all z∈) liftγ vV
        (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑² Anv (∈-all z∈) liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN (CTI2.Λ⊑²-smart-comma {A = A₀} Anv
        (∈-all z∈) liftW liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
      (∀⊑ Anv′ z∈A′ body) =
    CTI2.Λ⊑²-smart-comma Anv (∈-all z∈) liftW liftγ vV N⊢
      (right-inj-inversion² sv vN prem
        (CTX.smartCommaLift-transport⊑ᵂ liftW
          (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body)))
      (∀⊑ Anv′ z∈A′ body)
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN (CTI2.Λ⊑² Anv (∈-all z∈) liftγ vV M′⊢ prem q₀)
      (∀⊑∀ qbody)
    with source-occurs-target refl qbody
           (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
             (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
             (∈-all z∈))
  ... | ()
  right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
      vN (CTI2.Λ⊑²-smart-comma Anv (∈-all z∈) liftW
        liftγ vV M′⊢ prem q₀)
      (∀⊑∀ qbody)
    with source-occurs-target refl qbody
           (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
             (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
             (∈-all z∈))
  ... | ()

  -- Function-shaped reveal: the premise's ⇒⊑★ components rebuild the
  -- premise-level tag obligation, and by ⊑-unique it does not matter
  -- that this inhabitant differs from any other.
  right-inj-inversion² {gH = ★⇒★} (sv-reveal-fun sv)
      vN (CTI2.reveal⊑² {p = ⇒⊑★ pA pB} mono CTX.rebase-idᴸ
        sc ⊢c prem q₀)
      (⇒⊑⇒ qA qB) =
    CTI2.reveal⊑² mono CTX.rebase-idᴸ sc ⊢c
      (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
      (⇒⊑⇒ qA qB)
  right-inj-inversion² {gH = ★⇒★} (sv-reveal-fun sv)
      vN (CTI2.reveal⊑² {p = ⇒⊑★ pA pB} mono
        (CTX.rebase-onlyᴸ ts dis rep) sc ⊢c prem q₀)
      (⇒⊑⇒ qA qB) =
    CTI2.reveal⊑² mono (CTX.rebase-onlyᴸ ts dis rep) sc ⊢c
      (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
      (⇒⊑⇒ qA qB)
  right-inj-inversion² {W = W} {gH = ★⇒★} (sv-reveal-fun sv)
      vN (CTI2.reveal⊑² {W′ = W′} {p = ⇒⊑★ pA pB} mono
        (CTX.rebase-varᴸ rb) sc ⊢c prem q₀)
      (⇒⊑⇒ qA qB) =
    CTI2.reveal⊑² mono (CTX.rebase-varᴸ rb) sc ⊢c
      (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB)) (⇒⊑⇒ qA qB)
  right-inj-inversion² {gH = ＇ Y} (sv-reveal-fun sv)
    vN (CTI2.reveal⊑² _ _ _ _ _ _) ()
  right-inj-inversion² {gH = ‵ ι} (sv-reveal-fun sv)
    vN (CTI2.reveal⊑² _ _ _ _ _ _) ()
  right-inj-inversion² {gH = ∀★} (sv-reveal-fun sv)
    vN (CTI2.reveal⊑² _ _ _ _ _ _) ()

  -- Function-shaped conceal: same construction.
  right-inj-inversion² {gH = ★⇒★} (sv-conceal-fun sv)
      vN (CTI2.conceal⊑² {p = ⇒⊑★ pA pB} mono
        rb sc ⊢c prem q₀)
      (⇒⊑⇒ qA qB) =
    CTI2.conceal⊑² mono rb sc ⊢c
      (right-inj-inversion² sv vN prem (⇒⊑⇒ pA pB))
      (⇒⊑⇒ qA qB)
  right-inj-inversion² {gH = ＇ Y} (sv-conceal-fun sv)
    vN (CTI2.conceal⊑² _ _ _ _ _ _) ()
  right-inj-inversion² {gH = ‵ ι} (sv-conceal-fun sv)
    vN (CTI2.conceal⊑² _ _ _ _ _ _) ()
  right-inj-inversion² {gH = ∀★} (sv-conceal-fun sv)
    vN (CTI2.conceal⊑² _ _ _ _ _ _) ()

  -- Universal reveal: transport the requested tag obligation through the
  -- body conversion.  Variable rebases recurse in the honestified world.
  right-inj-inversion² (sv-reveal-all sv) vN
      (CTI2.reveal⊑² mono CTX.rebase-idᴸ sc (Conv.⊢↑-∀-idˣ c⊢)
        prem q₀) q =
    right-inj-reveal-all-id² sv vN sc c⊢ prem q
  right-inj-inversion² {W = W} {gH = ★⇒★}
      (sv-reveal-all sv) vN
      (CTI2.reveal⊑² {p = p₀} mono (CTX.rebase-onlyᴸ ts dis rep) sc
        (Conv.⊢↑-∀ˣ c⊢) prem q₀) q =
    CTI2.reveal⊑² mono (CTX.rebase-onlyᴸ ts dis rep) sc
      (Conv.⊢↑-∀ˣ c⊢)
      (right-inj-inversion² sv vN prem
        (TT.transport↑-∀-fun c⊢
          (toRenameᵗ-injective (ηᴸʷ W))
          (toRenameᵗ-injective (ηᴸʷ W))
          p₀ q))
      q
  right-inj-inversion² {W = W} {gH = ∀★} (sv-reveal-all sv) vN
      (CTI2.reveal⊑² {p = p₀} mono (CTX.rebase-onlyᴸ ts dis rep) sc
        (Conv.⊢↑-∀ˣ c⊢) prem q₀) q =
    CTI2.reveal⊑² mono (CTX.rebase-onlyᴸ ts dis rep) sc
      (Conv.⊢↑-∀ˣ c⊢)
      (right-inj-inversion² sv vN prem
        (TT.transport↑-∀-all c⊢
          (toRenameᵗ-injective (ηᴸʷ W))
          (toRenameᵗ-injective (ηᴸʷ W))
          p₀ q))
      q
  right-inj-inversion² {W = W} {gH = ‵ ι} (sv-reveal-all sv) vN
      (CTI2.reveal⊑² {p = p₀} mono (CTX.rebase-onlyᴸ ts dis rep) sc
        (Conv.⊢↑-∀ˣ c⊢) prem q₀) q =
    ⊥-elim
      (TT.transport↑-∀-ι-⊥ c⊢
        (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
        p₀ q)
  right-inj-inversion² {W = W} {gH = ＇ Y} (sv-reveal-all sv) vN
      (CTI2.reveal⊑² {p = p₀} mono (CTX.rebase-onlyᴸ ts dis rep) sc
        (Conv.⊢↑-∀ˣ c⊢) prem q₀) q =
    ⊥-elim
      (TT.transport↑-∀-var-⊥ c⊢
        (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
        p₀ q)
  right-inj-inversion² {W = W} {gH = ★⇒★}
      (sv-reveal-all sv) vN
      (CTI2.reveal⊑² {W′ = W′} {p = p₀} mono
        (CTX.rebase-varᴸ rb) sc (Conv.⊢↑-∀ˣ c⊢) prem q₀) q =
    CTI2.reveal⊑² mono (CTX.rebase-varᴸ rb) sc (Conv.⊢↑-∀ˣ c⊢)
      (right-inj-inversion² sv vN prem
        (TT.transport↑-∀-fun c⊢
          (toRenameᵗ-injective (ηᴸʷ W′))
          (toRenameᵗ-injective (ηᴸʷ W))
          p₀ q))
      q
  right-inj-inversion² {W = W} {gH = ∀★} (sv-reveal-all sv) vN
      (CTI2.reveal⊑² {W′ = W′} {p = p₀} mono
        (CTX.rebase-varᴸ rb) sc (Conv.⊢↑-∀ˣ c⊢) prem q₀) q =
    CTI2.reveal⊑² mono (CTX.rebase-varᴸ rb) sc (Conv.⊢↑-∀ˣ c⊢)
      (right-inj-inversion² sv vN prem
        (TT.transport↑-∀-all c⊢
          (toRenameᵗ-injective (ηᴸʷ W′))
          (toRenameᵗ-injective (ηᴸʷ W))
          p₀ q))
      q
  right-inj-inversion² {W = W} {gH = ‵ ι} (sv-reveal-all sv) vN
      (CTI2.reveal⊑² {W′ = W′} {p = p₀} mono
        (CTX.rebase-varᴸ rb) sc (Conv.⊢↑-∀ˣ c⊢) prem q₀) q =
    ⊥-elim
      (TT.transport↑-∀-ι-⊥ c⊢
        (toRenameᵗ-injective (ηᴸʷ W′))
        (toRenameᵗ-injective (ηᴸʷ W))
        p₀ q)
  right-inj-inversion² {W = W} {gH = ＇ Y} (sv-reveal-all sv) vN
      (CTI2.reveal⊑² {W′ = W′} {p = p₀} mono
        (CTX.rebase-varᴸ rb) sc (Conv.⊢↑-∀ˣ c⊢) prem q₀) q =
    ⊥-elim
      (TT.transport↑-∀-var-⊥ c⊢
        (toRenameᵗ-injective (ηᴸʷ W′))
        (toRenameᵗ-injective (ηᴸʷ W))
        p₀ q)

  -- Universal conceal: the dual transport has the same obligations, while
  -- the variable-rebase decay uses conceal's opposite rebase orientation.
  right-inj-inversion² {W = W} {H = H} (sv-conceal-all sv) vN
      (CTI2.conceal⊑² mono CTX.tag-rebase-idᴸ sc
        (Conv.⊢↓-∀-idˣ c⊢) prem q₀) q =
    CTI2.conceal⊑² mono CTX.tag-rebase-idᴸ sc
      (Conv.⊢↓-∀-idˣ c⊢)
      (right-inj-inversion² sv vN prem
        (subst≡ (λ T → T ⊑ᵂ⟨ W ⟩ H)
          (sym (cong `∀ (pivot-id-endpoints↓ c⊢))) q))
      q
  right-inj-inversion² {W = W} {gH = ★⇒★}
      (sv-conceal-all sv) vN
      (CTI2.conceal⊑² {p = p₀} mono
        (CTX.tag-rebase-onlyᴸ ts dis rep) sc
        (Conv.⊢↓-∀ˣ c⊢) prem q₀) q =
    CTI2.conceal⊑² mono (CTX.tag-rebase-onlyᴸ ts dis rep) sc
      (Conv.⊢↓-∀ˣ c⊢)
      (right-inj-inversion² sv vN prem
        (TT.transport↓-∀-fun c⊢
          (toRenameᵗ-injective (ηᴸʷ W))
          (toRenameᵗ-injective (ηᴸʷ W))
          p₀ q))
      q
  right-inj-inversion² {W = W} {gH = ∀★}
      (sv-conceal-all sv) vN
      (CTI2.conceal⊑² {p = p₀} mono
        (CTX.tag-rebase-onlyᴸ ts dis rep) sc
        (Conv.⊢↓-∀ˣ c⊢) prem q₀) q =
    CTI2.conceal⊑² mono (CTX.tag-rebase-onlyᴸ ts dis rep) sc
      (Conv.⊢↓-∀ˣ c⊢)
      (right-inj-inversion² sv vN prem
        (TT.transport↓-∀-all c⊢
          (toRenameᵗ-injective (ηᴸʷ W))
          (toRenameᵗ-injective (ηᴸʷ W))
          p₀ q))
      q
  right-inj-inversion² {W = W} {gH = ‵ ι}
      (sv-conceal-all sv) vN
      (CTI2.conceal⊑² {p = p₀} mono
        (CTX.tag-rebase-onlyᴸ ts dis rep) sc
        (Conv.⊢↓-∀ˣ c⊢) prem q₀) q =
    ⊥-elim
      (TT.transport↓-∀-ι-⊥ c⊢
        (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
        p₀ q)
  right-inj-inversion² {W = W} {gH = ＇ Y} (sv-conceal-all sv) vN
      (CTI2.conceal⊑² {p = p₀} mono
        (CTX.tag-rebase-onlyᴸ ts dis rep) sc
        (Conv.⊢↓-∀ˣ c⊢) prem q₀) q =
    ⊥-elim
      (TT.transport↓-∀-var-⊥ c⊢
        (toRenameᵗ-injective (ηᴸʷ W)) (toRenameᵗ-injective (ηᴸʷ W))
        p₀ q)
  -- Bare unmatched source seal.
  right-inj-inversion² {gH = ‵ ι} (sv-seal sv) vN
      (CTI2.conceal⊑² mono rb sc
        (Conv.⊢↓-sealˣ X∈) prem q₀) q
      with q
  right-inj-inversion² {gH = ‵ ι} (sv-seal sv) vN
      (CTI2.conceal⊑² mono rb sc
        (Conv.⊢↓-sealˣ X∈) prem q₀) q
      | ()
  right-inj-inversion² {gH = ★⇒★} (sv-seal sv) vN
      (CTI2.conceal⊑² mono rb sc
        (Conv.⊢↓-sealˣ X∈) prem q₀) q
      with q
  right-inj-inversion² {gH = ★⇒★} (sv-seal sv) vN
      (CTI2.conceal⊑² mono rb sc
        (Conv.⊢↓-sealˣ X∈) prem q₀) q
      | ()
  right-inj-inversion² {gH = ∀★} (sv-seal sv) vN
      (CTI2.conceal⊑² mono rb sc
        (Conv.⊢↓-sealˣ X∈) prem q₀) q
      with q
  right-inj-inversion² {gH = ∀★} (sv-seal sv) vN
      (CTI2.conceal⊑² mono rb sc
        (Conv.⊢↓-sealˣ X∈) prem q₀) q
      | ()
  right-inj-inversion² {W = W} {gH = ＇ Y}
      (sv-seal {X = Xᴸ} {R = R} sv) vN
      (CTI2.conceal⊑² mono rb sc
        (Conv.⊢↓-sealˣ Xᴸ∈) prem q₀) q
      with seal-rebase-target (CTX.forgetTagRebaseᴸ rb) q
         | right-tag-variable-view vN prem
  right-inj-inversion² {W = W} {gH = ＇ Y}
      (sv-seal {X = Xᴸ} {R = R} sv) vN
      (CTI2.conceal⊑² mono rb sc
        (Conv.⊢↓-sealˣ Xᴸ∈) prem q₀) q
      | ra′ | varv-seal {W = U} {R = S} vU Y∈ refl =
    target-tag-seal-walk sv vU mono ra′ sc Xᴸ∈
      (rebase-target-membership ra′ Y∈) prem

  -- Type applications are not spine values.
  right-inj-inversion² () vN (CTI2.•⊑² _ _ _ _) q

  ------------------------------------------------------------------------
  -- Identity-pivot universal wrappers
  ------------------------------------------------------------------------

  -- These are the complete nothing-pivot subcases of the two universal
  -- wrapper branches.  Their body conversions have equal endpoints and the
  -- wrapper world is definitionally unchanged, so ordinary index transport
  -- exposes the recursive injection obligation.

  right-inj-reveal-all-id² {W = W} {A = A} {B = B}
      {H = H} {c = c} sv vN sc c⊢ prem q =
    CTI2.reveal⊑² CTX.impEnvMono-refl CTX.rebase-idᴸ sc
      (Conv.⊢↑-∀-idˣ c⊢)
      (right-inj-inversion² sv vN prem
        (subst≡ (λ T → T ⊑ᵂ⟨ W ⟩ H)
          (sym (cong `∀ (pivot-id-endpoints↑ c⊢))) q))
      q
