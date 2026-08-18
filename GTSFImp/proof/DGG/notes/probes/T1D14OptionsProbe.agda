module proof.DGG.notes.probes.T1D14OptionsProbe where

-- File Charter:
--   * Checks the exact statement surfaces considered by the T1 D14 options.
--   * Restates the proven non-Lambda source theorem, the four Lambda-head
--     residuals, narrowed certificates, generalized recursive theorems, and
--     hereditary SourceLambdaReplayStack routing.
--   * Implements the migrated source-conceal replay glue and the hereditary
--     keep workers relative to the exact remaining endpoint residuals.

open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)

open import Types using
  (Ty; TyCtx; TyVar; NonVar; NonStar; _∈ᵗ_; `∀; ★; ＇_)
open import Conversion using (Conv↑; Conv↓; seal; unseal; id↑; id↓)
import CastTerms as CT
open import CastTerms using
  (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; Λ_; _↑_; _↓_)
open import Reduction using
  (StoreChanges; keep; pure-step; id-reveal; id-conceal; conceal-reveal;
   blame-reveal; blame-conceal; ξ-reveal; ξ-conceal; _—→[_]_)
open import Imprecision using (X⊑★)

import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_; LiftCtxᴸ;
   SmartCommaLiftᴸ; SmartLiftCtxᴸ)
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralWorldExtendDef using
  (StructuralWorldExtendᴿ)
open import proof.DGG.Catchup.StructuralWorldExtendProof using
  (structural-world-extendᴿ)
open import proof.DGG.Catchup.StructuralCatchupRightDef using
  (PairedConcealRevealPeelᵀ; SourceOnlyConcealRevealPeelᵀ;
   SourceΛReplayStack; SourceΛReplayStackTransport;
   source-Λ-stack-id; source-Λ-stack-plain; source-Λ-stack-smart;
   source-Λ-stack-replay-here)
open import proof.DGG.notes.probes.T1PlainSourceKeepProbe using
  (NonΛBareValue; bare-nonΛ-ƛ; bare-nonΛ-$;
   nonΛ-source-target-reveal-keep; nonΛ-source-target-conceal-keep;
   sameCtx-transport; ⊢²-retarget)
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof using
  (value-no-step)


------------------------------------------------------------------------
-- The two proven non-Lambda statements, verbatim from the checked probe
------------------------------------------------------------------------

NonΛSourceTargetRevealKeepᵀ : Set
NonΛSourceTargetRevealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {N N₁ : Term Δᴿ}
    {P : Term Δᴸ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
  → NonΛBareValue P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↑ c′ ∶ q
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q


NonΛSourceTargetConcealKeepᵀ : Set
NonΛSourceTargetConcealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {N N₁ : Term Δᴿ}
    {P : Term Δᴸ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
  → NonΛBareValue P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↓ c′ ∶ q
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q


------------------------------------------------------------------------
-- Exact body goals left by the two Lambda heads
------------------------------------------------------------------------

ΛPlainTargetRevealBodyKeepᵀ : Set
ΛPlainTargetRevealBodyKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {γᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W)}
    {V : Term (suc Δᴸ)} {N N₁ : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ B′}
    {q : `∀ A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtxᴸ X⊑★ γ γᴸ
  → Value V
  → ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
      ⊢ N ↑ c′ ⦂ B′
  → CTI2.liftWorldLeft X⊑★ W ∣ γᴸ ⊢² V ⊑ N ↑ c′ ∶ p
  → Value N
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → CTI2.liftWorldLeft X⊑★ W ∣ γᴸ ⊢² V ⊑ N₁ ∶ p


ΛPlainTargetConcealBodyKeepᵀ : Set
ΛPlainTargetConcealBodyKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {γᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W)}
    {V : Term (suc Δᴸ)} {N N₁ : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ B′}
    {q : `∀ A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtxᴸ X⊑★ γ γᴸ
  → Value V
  → ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
      ⊢ N ↓ c′ ⦂ B′
  → CTI2.liftWorldLeft X⊑★ W ∣ γᴸ ⊢² V ⊑ N ↓ c′ ∶ p
  → Value N
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → CTI2.liftWorldLeft X⊑★ W ∣ γᴸ ⊢² V ⊑ N₁ ∶ p


ΛSmartTargetRevealBodyKeepᵀ : Set
ΛSmartTargetRevealBodyKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ} {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CtxImp W} {γᵐ : CtxImp Wᵐ}
    {V : Term (suc Δᴸ)} {N N₁ : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ Wᵐ ⟩ B′} {q : `∀ A ⊑ᵂ⟨ W ⟩ B′}
    {c′ : Conv↑ Δᴿ B B′}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → SmartCommaLiftᴸ W Wᵐ
  → SmartLiftCtxᴸ γ γᵐ
  → Value V
  → ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
      ⊢ N ↑ c′ ⦂ B′
  → Wᵐ ∣ γᵐ ⊢² V ⊑ N ↑ c′ ∶ p
  → Value N
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → Wᵐ ∣ γᵐ ⊢² V ⊑ N₁ ∶ p


ΛSmartTargetConcealBodyKeepᵀ : Set
ΛSmartTargetConcealBodyKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ} {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CtxImp W} {γᵐ : CtxImp Wᵐ}
    {V : Term (suc Δᴸ)} {N N₁ : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ Wᵐ ⟩ B′} {q : `∀ A ⊑ᵂ⟨ W ⟩ B′}
    {c′ : Conv↓ Δᴿ B B′}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → SmartCommaLiftᴸ W Wᵐ
  → SmartLiftCtxᴸ γ γᵐ
  → Value V
  → ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
      ⊢ N ↓ c′ ⦂ B′
  → Wᵐ ∣ γᵐ ⊢² V ⊑ N ↓ c′ ∶ p
  → Value N
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → Wᵐ ∣ γᵐ ⊢² V ⊑ N₁ ∶ p


------------------------------------------------------------------------
-- Option (a): Lambda-source-only supplied certificates
------------------------------------------------------------------------

record SourceΛTargetRevealKeepCertificateᵀ : Set₁ where
  field
    source-Λ-target-reveal-keep :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V : Term (suc Δᴸ)} {N N₁ : Term Δᴿ}
        {Aᵛ : Ty (suc Δᴸ)} {B B′ : Ty Δᴿ}
        {q : `∀ Aᵛ ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
      → Value V
      → Value N
      → W ∣ γ ⊢² Λ V ⊑ N ↑ c′ ∶ q
      → (N ↑ c′) —→[ keep ] N₁
      → Value N₁
      → W ∣ γ ⊢² Λ V ⊑ N₁ ∶ q


record SourceΛTargetConcealKeepCertificateᵀ : Set₁ where
  field
    source-Λ-target-conceal-keep :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V : Term (suc Δᴸ)} {N N₁ : Term Δᴿ}
        {Aᵛ : Ty (suc Δᴸ)} {B B′ : Ty Δᴿ}
        {q : `∀ Aᵛ ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
      → Value V
      → Value N
      → W ∣ γ ⊢² Λ V ⊑ N ↓ c′ ∶ q
      → (N ↓ c′) —→[ keep ] N₁
      → Value N₁
      → W ∣ γ ⊢² Λ V ⊑ N₁ ∶ q


record TargetRevealKeepOutcomeContinuationsD14aᵀ : Set₁ where
  field
    paired-conceal-reveal : PairedConcealRevealPeelᵀ
    source-opened-conceal-reveal : SourceOnlyConcealRevealPeelᵀ
    plain-source-Λ : SourceΛTargetRevealKeepCertificateᵀ


record TargetConcealKeepOutcomeContinuationsD14aᵀ : Set₁ where
  field
    paired-id-conceal :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → Value V₀
      → Value V₀′
      → W ∣ γ ⊢²
          (V₀ ↓ id↓ A) ⊑ (V₀′ ↓ id↓ B) ∶ q
      → (V₀ ↓ id↓ A) —→[ keep ] V₀
      → (V₀′ ↓ id↓ B) —→[ keep ] V₀′
      → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q

    source-opened-id-conceal :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → Value V₀
      → Value V₀′
      → W ∣ γ ⊢² (V₀ ↓ id↓ A) ⊑ V₀′ ∶ q
      → (V₀ ↓ id↓ A) —→[ keep ] V₀
      → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q

    plain-source-Λ : SourceΛTargetConcealKeepCertificateᵀ


------------------------------------------------------------------------
-- Option (b): one recursive theorem for every source Value and every world
------------------------------------------------------------------------

RecursiveSourceValueTargetRevealKeepᵀ : Set
RecursiveSourceValueTargetRevealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {N N₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↑ Δᴿ B B′}
  → Value P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↑ c′ ∶ q
  → (N ↑ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q


RecursiveSourceValueTargetConcealKeepᵀ : Set
RecursiveSourceValueTargetConcealKeepᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {N N₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′} {c′ : Conv↓ Δᴿ B B′}
  → Value P
  → Value N
  → W ∣ γ ⊢² P ⊑ N ↓ c′ ∶ q
  → (N ↓ c′) —→[ keep ] N₁
  → Value N₁
  → W ∣ γ ⊢² P ⊑ N₁ ∶ q


------------------------------------------------------------------------
-- Option (c): route the keep obligation with a SourceLambdaReplayStack
------------------------------------------------------------------------

SourceΛStackTargetRevealKeepᵀ : Set₁
SourceΛStackTargetRevealKeepᵀ =
  ∀ {Δᴸ₀ Δᴿ Δ₀}
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


SourceΛStackTargetConcealKeepᵀ : Set₁
SourceΛStackTargetConcealKeepᵀ =
  ∀ {Δᴸ₀ Δᴿ Δ₀}
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


SourceΛReplayTransportedKeepGlueᵀ : Set₁
SourceΛReplayTransportedKeepGlueᵀ =
  ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
    (stack : SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q)
    {Δᴿ′ Δ₀′} {χs : StoreChanges Δᴿ Δᴿ′}
    {W₀′ : World Δᴸ₀ Δᴿ′ Δ₀′}
    (plan₀ : StructuralWorldExtendᴿ χs W₀ W₀′)
    (transported : SourceΛReplayStackTransport stack plan₀)
  → ∀ {N′ : Term Δᴿ′}
  → SourceΛReplayStackTransport.W′ transported ∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (SourceΛReplayStackTransport.current-plan transported))
        γ
      ⊢² M ⊑ N′ ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (SourceΛReplayStackTransport.current-plan transported))
          q
  → W₀′ ∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan₀) γ₀
      ⊢² M₀ ⊑ N′ ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan₀) q₀


------------------------------------------------------------------------
-- Migrated source-conceal replay at a target identity-conceal keep
------------------------------------------------------------------------

data SourceConcealOKTargetIdOutcome {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (P : Term Δᴸ)
    (Xᴿ? : Maybe (TyVar Δᴿ)) (N : Term Δᴿ) (B : Ty Δᴿ) :
    ∀ {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′ → Set where
  endpoint-ok : ∀ {A A′ : Ty Δᴸ} {c : Conv↓ Δᴸ A A′}
    → CTI2.SourceConcealOK W P c Xᴿ? N
    → SourceConcealOKTargetIdOutcome W P Xᴿ? N B c

  seal-nonstar-plain-residual : ∀ {X : TyVar Δᴸ} {R : Ty Δᴸ}
    → NonStar R
    → SourceConcealOKTargetIdOutcome W P Xᴿ? N B (seal X R)


source-conceal-ok-target-id-view : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A A′ : Ty Δᴸ} {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {N : Term Δᴿ} {B : Ty Δᴿ}
  → CTI2.SourceConcealOK W P c Xᴿ? (N ↓ id↓ B)
  → SourceConcealOKTargetIdOutcome W P Xᴿ? N B c
source-conceal-ok-target-id-view
    (CTI2.seal-nonstar-plain-ok Rns nt) =
  seal-nonstar-plain-residual Rns
source-conceal-ok-target-id-view CTI2.fun-conceal-ok =
  endpoint-ok CTI2.fun-conceal-ok
source-conceal-ok-target-id-view CTI2.all-conceal-ok =
  endpoint-ok CTI2.all-conceal-ok
source-conceal-ok-target-id-view CTI2.id-conceal-ok =
  endpoint-ok CTI2.id-conceal-ok


data SourceConcealOKTargetIdRevealOutcome {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (P : Term Δᴸ)
    (Xᴿ? : Maybe (TyVar Δᴿ)) (N : Term Δᴿ) (B : Ty Δᴿ) :
    ∀ {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′ → Set where
  reveal-endpoint-ok : ∀ {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′}
    → CTI2.SourceConcealOK W P c Xᴿ? N
    → SourceConcealOKTargetIdRevealOutcome W P Xᴿ? N B c

  reveal-seal-nonstar-plain-residual : ∀
      {X : TyVar Δᴸ} {R : Ty Δᴸ}
    → NonStar R
    → SourceConcealOKTargetIdRevealOutcome W P Xᴿ? N B (seal X R)


source-conceal-ok-target-id-reveal-view : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A A′ : Ty Δᴸ} {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {N : Term Δᴿ} {B : Ty Δᴿ}
  → CTI2.SourceConcealOK W P c Xᴿ? (N ↑ id↑ B)
  → SourceConcealOKTargetIdRevealOutcome W P Xᴿ? N B c
source-conceal-ok-target-id-reveal-view
    (CTI2.seal-nonstar-plain-ok Rns nt) =
  reveal-seal-nonstar-plain-residual Rns
source-conceal-ok-target-id-reveal-view CTI2.fun-conceal-ok =
  reveal-endpoint-ok CTI2.fun-conceal-ok
source-conceal-ok-target-id-reveal-view CTI2.all-conceal-ok =
  reveal-endpoint-ok CTI2.all-conceal-ok
source-conceal-ok-target-id-reveal-view CTI2.id-conceal-ok =
  reveal-endpoint-ok CTI2.id-conceal-ok


record SourceConcealTargetIdResidualsᵀ : Set₁ where
  field
    migrated-nonstar-endpoint : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {P : Term Δᴸ} {N : Term Δᴿ}
        {X : TyVar Δᴸ} {R : Ty Δᴸ} {B : Ty Δᴿ}
        {q : ＇ X ⊑ᵂ⟨ W ⟩ B}
      → Value P
      → Value N
      → NonStar R
      → W ∣ γ ⊢² P ↓ seal X R ⊑ N ↓ id↓ B ∶ q
      → CTI2.NotTopTag N

    migrated-nonstar-reveal-endpoint : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {P : Term Δᴸ} {N : Term Δᴿ}
        {X : TyVar Δᴸ} {R : Ty Δᴸ} {B : Ty Δᴿ}
        {q : ＇ X ⊑ᵂ⟨ W ⟩ B}
      → Value P
      → Value N
      → NonStar R
      → W ∣ γ ⊢² P ↓ seal X R ⊑ N ↑ id↑ B ∶ q
      → CTI2.NotTopTag N

    legacy-seal-endpoint : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ}
        {P : Term Δᴸ} {N : Term Δᴿ}
        {X : TyVar Δᴸ} {R : Ty Δᴸ}
        {Xᴿ? : Maybe (TyVar Δᴿ)} {B : Ty Δᴿ}
      → Value P
      → Value N
      → CTI2.SealPartnerOK W X P R Xᴿ? (N ↓ id↓ B)
      → CTI2.SealPartnerOK W X P R Xᴿ? N

    legacy-seal-reveal-endpoint : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ}
        {P : Term Δᴸ} {N : Term Δᴿ}
        {X : TyVar Δᴸ} {R : Ty Δᴸ}
        {Xᴿ? : Maybe (TyVar Δᴿ)} {B : Ty Δᴿ}
      → Value P
      → Value N
      → CTI2.SealPartnerOK W X P R Xᴿ? (N ↑ id↑ B)
      → CTI2.SealPartnerOK W X P R Xᴿ? N

    target-conceal-reveal-endpoint : ∀ {Δᴸ₀ Δᴿ Δ₀}
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


legacy-source-conceal-target-id-endpoint : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A A′ : Ty Δᴸ} {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {N : Term Δᴿ} {B : Ty Δᴿ}
  → SourceConcealTargetIdResidualsᵀ
  → Value P
  → Value N
  → CTI2.SourceConcealPartnerOK W P c Xᴿ? (N ↓ id↓ B)
  → CTI2.SourceConcealPartnerOK W P c Xᴿ? N
legacy-source-conceal-target-id-endpoint residuals vP vN
    (CTI2.seal-partner-ok ok) =
  CTI2.seal-partner-ok
    (SourceConcealTargetIdResidualsᵀ.legacy-seal-endpoint
      residuals vP vN ok)
legacy-source-conceal-target-id-endpoint residuals vP vN
    CTI2.fun-conceal-target =
  CTI2.fun-conceal-target
legacy-source-conceal-target-id-endpoint residuals vP vN
    CTI2.all-conceal-target =
  CTI2.all-conceal-target
legacy-source-conceal-target-id-endpoint residuals vP vN
    CTI2.id-conceal-target =
  CTI2.id-conceal-target


legacy-source-conceal-target-id-reveal-endpoint : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {P : Term Δᴸ}
    {A A′ : Ty Δᴸ} {c : Conv↓ Δᴸ A A′}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {N : Term Δᴿ} {B : Ty Δᴿ}
  → SourceConcealTargetIdResidualsᵀ
  → Value P
  → Value N
  → CTI2.SourceConcealPartnerOK W P c Xᴿ? (N ↑ id↑ B)
  → CTI2.SourceConcealPartnerOK W P c Xᴿ? N
legacy-source-conceal-target-id-reveal-endpoint residuals vP vN
    (CTI2.seal-partner-ok ok) =
  CTI2.seal-partner-ok
    (SourceConcealTargetIdResidualsᵀ.legacy-seal-reveal-endpoint
      residuals vP vN ok)
legacy-source-conceal-target-id-reveal-endpoint residuals vP vN
    CTI2.fun-conceal-target =
  CTI2.fun-conceal-target
legacy-source-conceal-target-id-reveal-endpoint residuals vP vN
    CTI2.all-conceal-target =
  CTI2.all-conceal-target
legacy-source-conceal-target-id-reveal-endpoint residuals vP vN
    CTI2.id-conceal-target =
  CTI2.id-conceal-target


source-conceal-ok-target-id-replay : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {N : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {c : Conv↓ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → CTI2.SourceConcealOK Wᵖ P c Xᴿ? N
  → CTI2.ImpEnvMono W Wᵖ
  → CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
  → CTI2.SameCtx γ γᵖ
  → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
  → Wᵖ ∣ γᵖ ⊢² P ⊑ N ∶ p
  → W ∣ γ ⊢² P ↓ c ⊑ N ∶ q
source-conceal-ok-target-id-replay ok mono rb sc c⊢ rel =
  CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ rel _


source-conceal-seal-star-target-id-replay : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {N : Term Δᴿ}
    {B : Ty Δᴿ} {X : TyVar Δᴸ}
    {p : ★ ⊑ᵂ⟨ Wᵖ ⟩ B} {q : ＇ X ⊑ᵂ⟨ W ⟩ B}
  → CTI2.NoTargetOccupantAtSource Wᵖ X
  → CTI2.ImpEnvMono W Wᵖ
  → CTI2.TagRebaseAtᴸ Wᵖ W (just X) nothing
  → CTI2.SameCtx γ γᵖ
  → CTI2.sourceStoreʷ W CTI2.⊢↓[ just X ] seal X ★
  → Wᵖ ∣ γᵖ ⊢² P ⊑ N ∶ p
  → W ∣ γ ⊢² P ↓ seal X ★ ⊑ N ∶ q
source-conceal-seal-star-target-id-replay no-target mono rb sc c⊢ rel =
  CTI2.conceal⊑²-seal-star-open no-target mono rb sc c⊢ rel _


source-Λ-stack-target-id-reveal-strip : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B} {N : Term Δᴿ}
  → SourceConcealTargetIdResidualsᵀ
  → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → Value M
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↑ id↑ B ∶ q
  → W₀ ∣ γ₀ ⊢² M₀ ⊑ N ∶ q₀
source-Λ-stack-target-id-reveal-strip residuals stack vM vN
    (CTI2.⊑reveal² {p = p} mono CTI2.rebase-idᴿ sc
      CTI2.⊢↑-idˣ rel q) =
  source-Λ-stack-replay-here stack
    (⊢²-retarget (sameCtx-transport sc rel))
source-Λ-stack-target-id-reveal-strip residuals stack (CT.ƛ M) vN rel =
  source-Λ-stack-replay-here stack
    (nonΛ-source-target-reveal-keep (bare-nonΛ-ƛ M) vN rel
      (pure-step (id-reveal vN)) vN)
source-Λ-stack-target-id-reveal-strip residuals stack (CT.$ κ) vN rel =
  source-Λ-stack-replay-here stack
    (nonΛ-source-target-reveal-keep (bare-nonΛ-$ κ) vN rel
      (pure-step (id-reveal vN)) vN)
source-Λ-stack-target-id-reveal-strip residuals stack (CT.Λ vU) vN
    (CTI2.Λ⊑² Anv z∈A liftγ vU′ target⊢ prem q) =
  source-Λ-stack-target-id-reveal-strip residuals
    (source-Λ-stack-plain stack Anv z∈A liftγ vU) vU vN prem
source-Λ-stack-target-id-reveal-strip residuals stack (CT.Λ vU) vN
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vU′ target⊢ prem q) =
  source-Λ-stack-target-id-reveal-strip residuals
    (source-Λ-stack-smart stack Anv z∈A liftW liftγ vU) vU vN prem
source-Λ-stack-target-id-reveal-strip residuals stack
    (vU CT.《 inert 》) vN (CTI2.cast⊑² c prem q) =
  source-Λ-stack-replay-here stack
    (CTI2.cast⊑² c
      (source-Λ-stack-target-id-reveal-strip residuals
        source-Λ-stack-id vU vN prem)
      q)
source-Λ-stack-target-id-reveal-strip residuals stack
    (vU CT.↑ rv) vN (CTI2.reveal⊑² mono rb sc c⊢ prem q) =
  source-Λ-stack-replay-here stack
    (CTI2.reveal⊑² mono rb sc c⊢
      (source-Λ-stack-target-id-reveal-strip residuals
        source-Λ-stack-id vU vN prem)
      q)
source-Λ-stack-target-id-reveal-strip residuals stack
    (vU CT.↓ cv) vN
    (CTI2.conceal⊑² partner mono rb sc c⊢ prem q) =
  source-Λ-stack-replay-here stack
    (CTI2.conceal⊑²
      (legacy-source-conceal-target-id-reveal-endpoint
        residuals vU vN partner)
      mono rb sc c⊢
      (source-Λ-stack-target-id-reveal-strip residuals
        source-Λ-stack-id vU vN prem)
      q)
source-Λ-stack-target-id-reveal-strip residuals stack
    (vU CT.↓ cv) vN
    (CTI2.conceal⊑²-seal-star-open no-target mono rb sc c⊢ prem q) =
  source-Λ-stack-replay-here stack
    (source-conceal-seal-star-target-id-replay no-target mono rb sc c⊢
      (source-Λ-stack-target-id-reveal-strip residuals
        source-Λ-stack-id vU vN prem))
source-Λ-stack-target-id-reveal-strip residuals stack
    (vU CT.↓ cv) vN
    D@(CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ prem q)
    with source-conceal-ok-target-id-reveal-view ok
source-Λ-stack-target-id-reveal-strip residuals stack
    (vU CT.↓ cv) vN
    D@(CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ prem q)
    | reveal-endpoint-ok endpoint =
  source-Λ-stack-replay-here stack
    (source-conceal-ok-target-id-replay endpoint mono rb sc c⊢
      (source-Λ-stack-target-id-reveal-strip residuals
        source-Λ-stack-id vU vN prem))
source-Λ-stack-target-id-reveal-strip residuals stack
    (vU CT.↓ cv) vN
    D@(CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ prem q)
    | reveal-seal-nonstar-plain-residual Rns =
  source-Λ-stack-replay-here stack
    (source-conceal-ok-target-id-replay
      (CTI2.seal-nonstar-plain-ok Rns endpoint-not-top)
      mono rb sc c⊢
      (source-Λ-stack-target-id-reveal-strip residuals
        source-Λ-stack-id vU vN prem))
  where
  endpoint-not-top =
    SourceConcealTargetIdResidualsᵀ.migrated-nonstar-reveal-endpoint
      residuals vU vN Rns D


source-Λ-stack-target-id-conceal-strip : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B} {N : Term Δᴿ}
  → SourceConcealTargetIdResidualsᵀ
  → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → Value M
  → Value N
  → W ∣ γ ⊢² M ⊑ N ↓ id↓ B ∶ q
  → W₀ ∣ γ₀ ⊢² M₀ ⊑ N ∶ q₀
source-Λ-stack-target-id-conceal-strip residuals stack vM vN
    (CTI2.⊑conceal² {p = p} mono CTI2.rebase-idᴿ sc
      CTI2.⊢↓-idˣ rel q) =
  source-Λ-stack-replay-here stack
    (⊢²-retarget (sameCtx-transport sc rel))
source-Λ-stack-target-id-conceal-strip residuals stack (CT.ƛ M) vN rel =
  source-Λ-stack-replay-here stack
    (nonΛ-source-target-conceal-keep (bare-nonΛ-ƛ M) vN rel
      (pure-step (id-conceal vN)) vN)
source-Λ-stack-target-id-conceal-strip residuals stack (CT.$ κ) vN rel =
  source-Λ-stack-replay-here stack
    (nonΛ-source-target-conceal-keep (bare-nonΛ-$ κ) vN rel
      (pure-step (id-conceal vN)) vN)
source-Λ-stack-target-id-conceal-strip residuals stack (CT.Λ vU) vN
    (CTI2.Λ⊑² Anv z∈A liftγ vU′ target⊢ prem q) =
  source-Λ-stack-target-id-conceal-strip residuals
    (source-Λ-stack-plain stack Anv z∈A liftγ vU) vU vN prem
source-Λ-stack-target-id-conceal-strip residuals stack (CT.Λ vU) vN
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vU′ target⊢ prem q) =
  source-Λ-stack-target-id-conceal-strip residuals
    (source-Λ-stack-smart stack Anv z∈A liftW liftγ vU) vU vN prem
source-Λ-stack-target-id-conceal-strip residuals stack
    (vU CT.《 inert 》) vN (CTI2.cast⊑² c prem q) =
  source-Λ-stack-replay-here stack
    (CTI2.cast⊑² c
      (source-Λ-stack-target-id-conceal-strip residuals
        source-Λ-stack-id vU vN prem)
      q)
source-Λ-stack-target-id-conceal-strip residuals stack
    (vU CT.↑ rv) vN (CTI2.reveal⊑² mono rb sc c⊢ prem q) =
  source-Λ-stack-replay-here stack
    (CTI2.reveal⊑² mono rb sc c⊢
      (source-Λ-stack-target-id-conceal-strip residuals
        source-Λ-stack-id vU vN prem)
      q)
source-Λ-stack-target-id-conceal-strip residuals stack
    (vU CT.↓ cv) vN
    (CTI2.conceal⊑² partner mono rb sc c⊢ prem q) =
  source-Λ-stack-replay-here stack
    (CTI2.conceal⊑²
      (legacy-source-conceal-target-id-endpoint residuals vU vN partner)
      mono rb sc c⊢
      (source-Λ-stack-target-id-conceal-strip residuals
        source-Λ-stack-id vU vN prem)
      q)
source-Λ-stack-target-id-conceal-strip residuals stack
    (vU CT.↓ cv) vN
    (CTI2.conceal⊑²-seal-star-open no-target mono rb sc c⊢ prem q) =
  source-Λ-stack-replay-here stack
    (source-conceal-seal-star-target-id-replay no-target mono rb sc c⊢
      (source-Λ-stack-target-id-conceal-strip residuals
        source-Λ-stack-id vU vN prem))
source-Λ-stack-target-id-conceal-strip residuals stack
    (vU CT.↓ cv) vN
    D@(CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ prem q)
    with source-conceal-ok-target-id-view ok
source-Λ-stack-target-id-conceal-strip residuals stack
    (vU CT.↓ cv) vN
    D@(CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ prem q)
    | endpoint-ok endpoint =
  source-Λ-stack-replay-here stack
    (source-conceal-ok-target-id-replay endpoint mono rb sc c⊢
      (source-Λ-stack-target-id-conceal-strip residuals
        source-Λ-stack-id vU vN prem))
source-Λ-stack-target-id-conceal-strip residuals stack
    (vU CT.↓ cv) vN
    D@(CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ prem q)
    | seal-nonstar-plain-residual Rns =
  source-Λ-stack-replay-here stack
    (source-conceal-ok-target-id-replay
      (CTI2.seal-nonstar-plain-ok Rns endpoint-not-top)
      mono rb sc c⊢
      (source-Λ-stack-target-id-conceal-strip residuals
        source-Λ-stack-id vU vN prem))
  where
  endpoint-not-top =
    SourceConcealTargetIdResidualsᵀ.migrated-nonstar-endpoint
      residuals vU vN Rns D


source-Λ-stack-target-reveal-keep :
  SourceConcealTargetIdResidualsᵀ
  → SourceΛStackTargetRevealKeepᵀ
source-Λ-stack-target-reveal-keep residuals stack vM vN rel
    (pure-step (id-reveal vN′)) finalV =
  source-Λ-stack-target-id-reveal-strip residuals stack vM vN rel
source-Λ-stack-target-reveal-keep residuals stack vM vN rel
    (pure-step (conceal-reveal vN′)) finalV =
  SourceConcealTargetIdResidualsᵀ.target-conceal-reveal-endpoint
    residuals stack vM vN′ rel
source-Λ-stack-target-reveal-keep residuals stack vM () rel
    (pure-step blame-reveal) finalV
source-Λ-stack-target-reveal-keep residuals stack vM vN rel
    (ξ-reveal step refl) finalV =
  ⊥-elim (value-no-step vN step)


source-Λ-stack-target-conceal-keep :
  SourceConcealTargetIdResidualsᵀ
  → SourceΛStackTargetConcealKeepᵀ
source-Λ-stack-target-conceal-keep residuals stack vM vN rel
    (pure-step (id-conceal vN′)) finalV =
  source-Λ-stack-target-id-conceal-strip residuals stack vM vN rel
source-Λ-stack-target-conceal-keep residuals stack vM () rel
    (pure-step blame-conceal) finalV
source-Λ-stack-target-conceal-keep residuals stack vM vN rel
    (ξ-conceal step refl) finalV =
  ⊥-elim (value-no-step vN step)


recursive-source-value-target-conceal-keep-with-residuals :
  SourceConcealTargetIdResidualsᵀ
  → RecursiveSourceValueTargetConcealKeepᵀ
recursive-source-value-target-conceal-keep-with-residuals residuals
    vP vN rel step finalV =
  source-Λ-stack-target-conceal-keep residuals source-Λ-stack-id
    vP vN rel step finalV


recursive-source-value-target-reveal-keep-with-residuals :
  SourceConcealTargetIdResidualsᵀ
  → RecursiveSourceValueTargetRevealKeepᵀ
recursive-source-value-target-reveal-keep-with-residuals residuals
    vP vN rel step finalV =
  source-Λ-stack-target-reveal-keep residuals source-Λ-stack-id
    vP vN rel step finalV
