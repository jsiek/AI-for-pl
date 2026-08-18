module proof.DGG.notes.probes.T1D14OptionsProbe where

-- File Charter:
--   * Checks the exact statement surfaces considered by the T1 D14 options.
--   * Restates the proven non-Lambda source theorem, the four Lambda-head
--     residuals, narrowed certificates, generalized recursive theorems, and
--     hereditary SourceLambdaReplayStack routing.
--   * Declares Sets and records only; it supplies no inhabitants.

open import Data.Nat using (suc)
import Data.Fin as Fin

open import Types using (Ty; TyCtx; NonVar; _∈ᵗ_; `∀)
open import Conversion using (Conv↑; Conv↓; id↓)
open import CastTerms using
  (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; Λ_; _↑_; _↓_)
open import Reduction using (StoreChanges; keep; _—→[_]_)
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
   SourceΛReplayStack; SourceΛReplayStackTransport)
open import proof.DGG.notes.probes.T1PlainSourceKeepProbe using
  (NonΛBareValue)


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
