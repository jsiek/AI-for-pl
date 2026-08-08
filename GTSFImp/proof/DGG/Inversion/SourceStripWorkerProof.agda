module proof.DGG.Inversion.SourceStripWorkerProof where

-- File Charter:
--   * Provides the source-column and source-spine strip members.
--   * Keeps the public `SourceStripProof` module free of local proof scripts.
--   * The two statements are exactly the frozen worker goals from
--     `SourceStripDef`.

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl; subst)

open import Types
open import TyStore using (_∋_⦂_)
open import Conversion using (seal)
open import CastTerms using
  (Term; Value; Inert; RevealValue; ConcealValue; ƛ_; Λ_; $;
   _⟨_⟩; _↓_; _↑_; _《_》; seal; fun; all)
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip; SourceCorePremise;
   CoreRebuild; SourceAtom; core-sealed; core-terminus; core-tagged;
   core-untagged; source-strip; source-column-strip; atom-ƛ; atom-Λ;
   atom-$)
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; sv-ƛ; sv-Λ; sv-$; sv-cast; sv-seal;
   sv-reveal-fun; sv-conceal-fun; sv-reveal-all; sv-conceal-all;
   var-value-view; varv-seal)
open import proof.DGG.Inversion.TargetWalkSupport using
  (composeSamePivotRebase; impEnvMono-∘; rebase-source-membership-back;
   sameCtx-∘)

open CTI2 using
  (World; CtxImp; RebaseAt; RebaseAtᴸ; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; sourceStoreʷ; targetStoreʷ)

private
  spine-value : ∀ {Δ} {V : Term Δ}
    → SpineValue V
    → Value V
  spine-value (sv-ƛ N) = ƛ N
  spine-value (sv-Λ sv) = Λ (spine-value sv)
  spine-value (sv-$ κ) = $ κ
  spine-value (sv-cast sv inert) = spine-value sv 《 inert 》
  spine-value (sv-seal sv) = spine-value sv ↓ seal
  spine-value (sv-reveal-fun sv) = spine-value sv ↑ fun
  spine-value (sv-conceal-fun sv) = spine-value sv ↓ fun
  spine-value (sv-reveal-all sv) = spine-value sv ↑ all
  spine-value (sv-conceal-all sv) = spine-value sv ↓ all

postulate
  source-column-strip-worker : SourceColumnStrip
  source-spine-strip-worker : SourceSpineStrip
