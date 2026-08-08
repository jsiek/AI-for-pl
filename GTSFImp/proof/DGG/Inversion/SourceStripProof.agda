module proof.DGG.Inversion.SourceStripProof where

-- File Charter:
--   * Provides the source-strip inhabitants consumed by the composed target
--     tag/seal walk.
--   * Keeps the structural strip proof behind the `SourceStripDef` surface.
--   * Exposes no right-injection theorem directly.

open import Relation.Binary.PropositionalEquality using (refl)
  renaming (subst to subst≡)

open import Types
open import TyStore using (_∋_⦂_)
open import CastTerms using (Term)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip; SourceTagSealCore;
   SourceAtom;
   SourceCorePremise; CoreRebuild; TargetChainData; core-sealed;
   core-terminus; core-tagged; core-untagged; atom-ƛ; atom-Λ; atom-$;
   target-chain-data)
open import proof.DGG.Inversion.TargetStripDef using
  (TargetStripAt★Data; TargetStripAt★ᴸData;
   target-strip★-data; target-strip★ᴸ-data)
open import proof.DGG.Inversion.TargetStripLemma using
  (target-strip-at★; target-strip-at★ᴸ)
open import proof.DGG.Inversion.SourceStripWorkerProof using
  (source-column-strip-worker; source-spine-strip-worker)
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; sv-ƛ; sv-Λ; sv-$)

private
  rebase-target-membership-forward : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : CTI2.World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
    → CTI2.RebaseAt W′ W X Y
    → CTI2.targetStoreʷ W ∋ Y ⦂ S
    → CTI2.targetStoreʷ W′ ∋ Y ⦂ S
  rebase-target-membership-forward rb Y∈ =
    subst≡ (λ Σ → Σ ∋ _ ⦂ _)
      (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb)) Y∈

  source-atom-spine : ∀ {Δ : TyCtx} {P : Term Δ}
    → SourceAtom P
    → SpineValue P
  source-atom-spine (atom-ƛ N) = sv-ƛ N
  source-atom-spine (atom-Λ sv) = sv-Λ sv
  source-atom-spine (atom-$ κ) = sv-$ κ

source-column-strip : SourceColumnStrip
source-column-strip = source-column-strip-worker

source-spine-strip : SourceSpineStrip
source-spine-strip = source-spine-strip-worker

source-tag-seal-core : SourceTagSealCore
source-tag-seal-core atom vU mono rb sc target∈ (core-untagged qᶜ D) =
  core-sealed _ _ mono sc (CTI2.rebase-varᴸ rb)
    (rebase-target-membership-forward rb target∈) qᶜ D
source-tag-seal-core {Xᴸ = Xᴸ} (atom-Λ sv) vU mono rb sc target∈
    (core-tagged
      (CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ prem q)) =
  core-terminus
    (target-chain-data
      Y★ ★ refl W★ γ★ mono★ same★ boundary★ target∈★ q★
      (CTI2.Λ⊑² Anv z∈A lift★ vV U⊢★ premise★ q★))
  where
  strip★ᴸ =
    target-strip-at★ᴸ sv vU mono rb sc target∈ liftγ prem

  open TargetStripAt★ᴸData strip★ᴸ
source-tag-seal-core {Xᴸ = Xᴸ} atom vU mono rb sc target∈
    (core-tagged D)
    with target-strip-at★ (source-atom-spine atom)
      vU mono rb sc target∈ D
source-tag-seal-core {Xᴸ = Xᴸ} atom vU mono rb sc target∈
    (core-tagged D)
    | target-strip★-data Y★ W★ γ★ mono★ same★ boundary★
        target∈★ q★ premise★ =
  core-terminus
    (target-chain-data
      Y★ _ refl W★ γ★ mono★ same★ boundary★ target∈★ q★ premise★)
