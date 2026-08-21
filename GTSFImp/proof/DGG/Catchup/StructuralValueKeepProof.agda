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
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym)
  renaming (subst to subst≡)

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
open CTX using (World; CtxImp; SameCtx; _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.Imprecision as PI
open import proof.DGG.Catchup.StructuralCatchupRightDef using
  (SourceΛReplayStack; source-Λ-stack-id; source-Λ-stack-plain;
   source-Λ-stack-smart; source-Λ-stack-replay-here)
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof using
  (value-no-step)
open import proof.DGG.TargetExtend using (⊢²-retarget)


ctx-imp-eq : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p p′ : A ⊑ᵂ⟨ W ⟩ B}
  → CTX.ctx-imp A B p ≡ CTX.ctx-imp A B p′
ctx-imp-eq {W = W} {A = A} {B = B} {p = p} {p′ = p′} =
  cong (λ r → CTX.ctx-imp {W = W} A B r) (PI.⊑-unique p p′)


sameCtx-eq : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ γ′ : CtxImp W}
  → SameCtx γ γ′
  → γ ≡ γ′
sameCtx-eq CTX.same-[] = refl
sameCtx-eq (CTX.same-∷ sc) =
  cong₂ _∷_ ctx-imp-eq (sameCtx-eq sc)


sameCtx-transport : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ γ′ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → SameCtx γ γ′
  → W ∣ γ′ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ p
sameCtx-transport {W = W} {γ = γ} {M = M} {N = N} {p = p} sc rel =
  subst≡ (λ γ₀ → W ∣ γ₀ ⊢² M ⊑ N ∶ p)
    (sym (sameCtx-eq sc)) rel


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
    (CTI2.⊑reveal² {p = p} mono CTX.rebase-idᴿ sc
      Conv.⊢↑-idˣ rel q) =
  source-Λ-stack-replay-here stack
    (⊢²-retarget (sameCtx-transport sc rel))
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
    (CTI2.reveal⊑² mono rb sc c⊢ rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.reveal⊑² mono rb sc c⊢
      (source-stack-target-id-reveal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-reveal-strip stack (vM CT.↓ cv) vN
    (CTI2.conceal⊑² mono rb sc c⊢ rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.conceal⊑² mono rb sc c⊢
      (source-stack-target-id-reveal-strip source-Λ-stack-id vM vN rel)
      q)


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
    (CTI2.⊑conceal² {p = p} mono CTX.rebase-idᴿ sc
      Conv.⊢↓-idˣ rel q) =
  source-Λ-stack-replay-here stack
    (⊢²-retarget (sameCtx-transport sc rel))
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
    (CTI2.reveal⊑² mono rb sc c⊢ rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.reveal⊑² mono rb sc c⊢
      (source-stack-target-id-conceal-strip source-Λ-stack-id vM vN rel)
      q)
source-stack-target-id-conceal-strip stack (vM CT.↓ cv) vN
    (CTI2.conceal⊑² mono rb sc c⊢ rel q) =
  source-Λ-stack-replay-here stack
    (CTI2.conceal⊑² mono rb sc c⊢
      (source-stack-target-id-conceal-strip source-Λ-stack-id vM vN rel)
      q)


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
