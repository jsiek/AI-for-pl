module proof.DGG.Catchup.StructuralValueKeepProof where

-- File Charter:
--   * Implements the D14(c) hereditary target-frame keep routing for source
--     values.
--   * Identity reveal/conceal rows are total under D17(c): unmatched
--     non-star source seals retain their no-target-occupant witness.
--   * Exposes one pinned residual for the genuinely distinct target
--     conceal/reveal peel; no other keep row is assumed.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty; TyVar)
open import Conversion using (Conv↑; Conv↓; seal; unseal; id↑; id↓)
import CastTerms as CT
open import CastTerms using (Term; Value; Λ_; _↑_; _↓_)
open import Reduction using
  (keep; pure-step; id-reveal; id-conceal; conceal-reveal;
   blame-reveal; blame-conceal; ξ-reveal; ξ-conceal; _—→[_]_)

import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTX using (World; CtxImp; _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)
open import proof.DGG.Catchup.StructuralCatchupRightDef using
  (SourceΛReplayStack; source-Λ-stack-id; source-Λ-stack-plain;
   source-Λ-stack-smart; source-Λ-stack-replay-here)
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof using
  (value-no-step)
open import proof.DGG.TargetExtend using (⊢²-retarget)


record StructuralValueKeepResiduals : Set₁ where
  field
    source-stack-conceal-reveal : ∀ {Δᴸ₀ Δᴿ Δ₀}
        {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
        {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
        {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
        {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {A : Ty Δᴸ} {R : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ R}
        {N : Term Δᴿ} {X : TyVar Δᴿ}
      → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
      → Value M
      → Value N
      → W ∣ γ ⊢² M ⊑ (N ↓ seal X R) ↑ unseal X R ∶ q
      → W₀ ∣ γ₀ ⊢² M₀ ⊑ N ∶ q₀


source-stack-target-id-reveal-strip : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B} {N : Term Δᴿ}
  → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → Value M
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↑ id↑ B ∶ q
  → W₀ ∣ γ₀ ⊢² M₀ ⊑ N ∶ q₀
source-stack-target-id-reveal-strip stack vM vN
    (CTI2.⊑reveal² {p = p} (Conv.⊢↑-id-var member X≠Y) refl rel q) =
  source-Λ-stack-replay-here stack (⊢²-retarget rel)
source-stack-target-id-reveal-strip stack vM vN
    (CTI2.⊑reveal² {p = p} (Conv.⊢↑-id-base member) refl rel q) =
  source-Λ-stack-replay-here stack (⊢²-retarget rel)
source-stack-target-id-reveal-strip stack vM vN
    (CTI2.⊑reveal² {p = p} (Conv.⊢↑-id-star member) refl rel q) =
  source-Λ-stack-replay-here stack
    (⊢²-retarget rel)
source-stack-target-id-reveal-strip stack (CT.Λ vM) vN
    (CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ rel q) =
  source-stack-target-id-reveal-strip
    (source-Λ-stack-plain stack Anv z∈A liftγ vV) vM vN rel
source-stack-target-id-reveal-strip stack (CT.Λ vM) vN
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV target⊢ rel q) =
  source-stack-target-id-reveal-strip
    (source-Λ-stack-smart stack Anv z∈A liftW liftγ vV) vM vN rel
source-stack-target-id-reveal-strip stack (vM CT.《 inert 》) vN
    (CTI2.cast⊑² c rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.cast⊑² c
      (source-stack-target-id-reveal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-reveal-strip stack (vM CT.↑ rv) vN
    (CTI2.reveal⊑-neutral² c⊢ position rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.reveal⊑-neutral² c⊢ position
      (source-stack-target-id-reveal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-reveal-strip stack (vM CT.↑ rv) vN
    (CTI2.reveal⊑-only² c⊢ position mark disaligned represented rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.reveal⊑-only² c⊢ position mark disaligned represented
      (source-stack-target-id-reveal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-reveal-strip stack (vM CT.↑ rv) vN
    (CTI2.reveal⊑² c⊢ position target-member represented mono rb sc
      rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.reveal⊑² c⊢ position target-member represented mono rb sc
      (source-stack-target-id-reveal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-reveal-strip stack (vM CT.↓ cv) vN
    (CTI2.conceal⊑-neutral² c⊢ position rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.conceal⊑-neutral² c⊢ position
      (source-stack-target-id-reveal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-reveal-strip stack (vM CT.↓ cv) vN
    (CTI2.conceal⊑² c⊢ position mark disaligned represented rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.conceal⊑² c⊢ position mark disaligned represented
      (source-stack-target-id-reveal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-reveal-strip stack vM vN
    (CTI2.reveal⊑reveal² c⊢ (Conv.⊢↑-id-var member X≠Y)
      positions position≢absent represented mono rb sc rel q) =
  ⊥-elim (position≢absent positions)
source-stack-target-id-reveal-strip stack vM vN
    (CTI2.reveal⊑reveal² c⊢ (Conv.⊢↑-id-base member)
      positions position≢absent represented mono rb sc rel q) =
  ⊥-elim (position≢absent positions)
source-stack-target-id-reveal-strip stack vM vN
    (CTI2.reveal⊑reveal² c⊢ (Conv.⊢↑-id-star member)
      positions position≢absent represented mono rb sc rel q) =
  ⊥-elim (position≢absent positions)


source-stack-target-id-conceal-strip : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B} {N : Term Δᴿ}
  → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → Value M
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↓ id↓ B ∶ q
  → W₀ ∣ γ₀ ⊢² M₀ ⊑ N ∶ q₀
source-stack-target-id-conceal-strip stack vM vN
    (CTI2.⊑conceal² {p = p} (Conv.⊢↓-id-var member X≠Y) refl rel q) =
  source-Λ-stack-replay-here stack (⊢²-retarget rel)
source-stack-target-id-conceal-strip stack vM vN
    (CTI2.⊑conceal² {p = p} (Conv.⊢↓-id-base member) refl rel q) =
  source-Λ-stack-replay-here stack (⊢²-retarget rel)
source-stack-target-id-conceal-strip stack vM vN
    (CTI2.⊑conceal² {p = p} (Conv.⊢↓-id-star member) refl rel q) =
  source-Λ-stack-replay-here stack
    (⊢²-retarget rel)
source-stack-target-id-conceal-strip stack (CT.Λ vM) vN
    (CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ rel q) =
  source-stack-target-id-conceal-strip
    (source-Λ-stack-plain stack Anv z∈A liftγ vV) vM vN rel
source-stack-target-id-conceal-strip stack (CT.Λ vM) vN
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV target⊢ rel q) =
  source-stack-target-id-conceal-strip
    (source-Λ-stack-smart stack Anv z∈A liftW liftγ vV) vM vN rel
source-stack-target-id-conceal-strip stack (vM CT.《 inert 》) vN
    (CTI2.cast⊑² c rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.cast⊑² c
      (source-stack-target-id-conceal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-conceal-strip stack (vM CT.↑ rv) vN
    (CTI2.reveal⊑-neutral² c⊢ position rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.reveal⊑-neutral² c⊢ position
      (source-stack-target-id-conceal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-conceal-strip stack (vM CT.↑ rv) vN
    (CTI2.reveal⊑-only² c⊢ position mark disaligned represented rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.reveal⊑-only² c⊢ position mark disaligned represented
      (source-stack-target-id-conceal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-conceal-strip stack (vM CT.↑ rv) vN
    (CTI2.reveal⊑² c⊢ position target-member represented mono rb sc
      rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.reveal⊑² c⊢ position target-member represented mono rb sc
      (source-stack-target-id-conceal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-conceal-strip stack (vM CT.↓ cv) vN
    (CTI2.conceal⊑-neutral² c⊢ position rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.conceal⊑-neutral² c⊢ position
      (source-stack-target-id-conceal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-conceal-strip stack (vM CT.↓ cv) vN
    (CTI2.conceal⊑² c⊢ position mark disaligned represented rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.conceal⊑² c⊢ position mark disaligned represented
      (source-stack-target-id-conceal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-conceal-strip stack vM vN
    (CTI2.conceal⊑conceal² c⊢ (Conv.⊢↓-id-var member X≠Y)
      positions position≢absent represented mono rb sc rel q) =
  ⊥-elim (position≢absent positions)
source-stack-target-id-conceal-strip stack vM vN
    (CTI2.conceal⊑conceal² c⊢ (Conv.⊢↓-id-base member)
      positions position≢absent represented mono rb sc rel q) =
  ⊥-elim (position≢absent positions)
source-stack-target-id-conceal-strip stack vM vN
    (CTI2.conceal⊑conceal² c⊢ (Conv.⊢↓-id-star member)
      positions position≢absent represented mono rb sc rel q) =
  ⊥-elim (position≢absent positions)


source-stack-target-reveal-keep :
  StructuralValueKeepResiduals
  → ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
    {N N₁ : Term Δᴿ}
  → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → Value M
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↑ c′ ∶ q
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → W₀ ∣ γ₀ ⊢² M₀ ⊑ N₁ ∶ q₀
source-stack-target-reveal-keep residuals stack vM vN rel
    (pure-step (id-reveal vN′)) finalV =
  source-stack-target-id-reveal-strip stack vM vN rel
source-stack-target-reveal-keep residuals stack vM vN rel
    (pure-step (conceal-reveal vN′)) finalV =
  StructuralValueKeepResiduals.source-stack-conceal-reveal
    residuals stack vM vN′ rel
source-stack-target-reveal-keep residuals stack vM () rel
    (pure-step blame-reveal) finalV
source-stack-target-reveal-keep residuals stack vM vN rel
    (ξ-reveal step refl) finalV =
  ⊥-elim (value-no-step vN step)


source-stack-target-conceal-keep : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
    {N N₁ : Term Δᴿ}
  → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → Value M
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↓ c′ ∶ q
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → W₀ ∣ γ₀ ⊢² M₀ ⊑ N₁ ∶ q₀
source-stack-target-conceal-keep stack vM vN rel
    (pure-step (id-conceal vN′)) finalV =
  source-stack-target-id-conceal-strip stack vM vN rel
source-stack-target-conceal-keep stack vM () rel
    (pure-step blame-conceal) finalV
source-stack-target-conceal-keep stack vM vN rel
    (ξ-conceal step refl) finalV =
  ⊥-elim (value-no-step vN step)


source-value-target-reveal-keep : StructuralValueKeepResiduals
  → ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N N₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
  → Value M
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↑ c′ ∶ q
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² M ⊑ N₁ ∶ q
source-value-target-reveal-keep residuals =
  source-stack-target-reveal-keep residuals source-Λ-stack-id


source-value-target-conceal-keep : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N N₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
  → Value M
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↓ c′ ∶ q
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² M ⊑ N₁ ∶ q
source-value-target-conceal-keep =
  source-stack-target-conceal-keep source-Λ-stack-id
