module proof.DGG.Inversion.SourceStripDef where

-- File Charter:
--   * States the source-spine strip surface used to derive the target
--     tag/seal walk.
--   * Packages core rebuilds with the boundary rebases needed by source
--     re-emission and an existential target-chain terminus.
--   * Keeps the statement independent of the proof script and exposes only
--     the source-spine surface consumed by the core rebuild proof.

open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open CTI2 using
  (World; CtxImp; RebaseAt; RebaseAtᴸ; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; sourceStoreʷ; targetStoreʷ)

-- Core branch packages
------------------------------------------------------------------------

data SourceTagSealCoreBranch {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (P : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ)
    (Y : TyVar Δᴿ) (S : Ty Δᴿ)
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★)
    (Wᵖ : World Δᴸ Δᴿ Δ) (γᵖ : CtxImp Wᵖ)
    (pᵖ : A ⊑ᵂ⟨ Wᵖ ⟩ ★) : Set where
  core-sealed :
    (Σ[ Wʳ ∈ World Δᴸ Δᴿ Δ ]
     Σ[ γʳ ∈ CtxImp Wʳ ]
     Σ[ qʳ ∈ A ⊑ᵂ⟨ Wʳ ⟩ (＇ Y) ]
       (CTI2.ImpEnvMono Wᵒ Wʳ
        × CTI2.SameCtx γᵒ γʳ
        × RebaseAtᴸ Wʳ Wᵒ (just Xᴸ)
        × targetStoreʷ Wʳ ∋ Y ⦂ S
        × Wʳ ∣ γʳ ⊢² P ⊑ U ↓ seal Y S ∶ qʳ))
    → SourceTagSealCoreBranch Wᵒ γᵒ P A U Xᴸ Y S cY
        Wᵖ γᵖ pᵖ

  core-terminus :
    A ≡ ★
    → (Σ[ U★ ∈ Term Δᴿ ]
     Σ[ Y★ ∈ TyVar Δᴿ ]
     Σ[ S★ ∈ Ty Δᴿ ]
     (S★ ≡ ★
      × Σ[ W★ ∈ World Δᴸ Δᴿ Δ ]
      Σ[ γ★ ∈ CtxImp W★ ]
      (CTI2.ImpEnvMono Wᵒ W★
       × CTI2.SameCtx γᵒ γ★
       × RebaseAt W★ Wᵒ Xᴸ Y
       × targetStoreʷ W★ ∋ Y★ ⦂ S★
       × Σ[ q★ ∈ A ⊑ᵂ⟨ W★ ⟩ S★ ]
       (W★ ∣ γ★ ⊢² P ⊑ U★ ∶ q★
        × (W★ ∣ γ★ ⊢² P ⊑ U★ ∶ q★
           → Wᵖ ∣ γᵖ ⊢² P
               ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ pᵖ)))))
    → SourceTagSealCoreBranch Wᵒ γᵒ P A U Xᴸ Y S cY
        Wᵖ γᵖ pᵖ

  core-terminus-nonstar :
    NonStar A
    → (Σ[ U★ ∈ Term Δᴿ ]
       Σ[ Y★ ∈ TyVar Δᴿ ]
       Σ[ S★ ∈ Ty Δᴿ ]
       (S★ ≡ ★
        × Σ[ W★ ∈ World Δᴸ Δᴿ Δ ]
        Σ[ γ★ ∈ CtxImp W★ ]
        (CTI2.ImpEnvMono Wᵒ W★
         × CTI2.SameCtx γᵒ γ★
         × RebaseAt W★ Wᵒ Xᴸ Y
         × targetStoreʷ W★ ∋ Y★ ⦂ S★
         × Σ[ q★ ∈ A ⊑ᵂ⟨ W★ ⟩ S★ ]
         (W★ ∣ γ★ ⊢² P ⊑ U★ ∶ q★
          × (W★ ∣ γ★ ⊢² P ⊑ U★ ∶ q★
             → Wᵖ ∣ γᵖ ⊢² P
                 ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ pᵖ)))))
    → SourceTagSealCoreBranch Wᵒ γᵒ P A U Xᴸ Y S cY
        Wᵖ γᵖ pᵖ

data SourcePairedBranch {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (P : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ)
    (Y : TyVar Δᴿ) (S : Ty Δᴿ) : Set where
  core-paired :
    (Σ[ Wᵖ ∈ World Δᴸ Δᴿ Δ ]
     Σ[ γᵖ ∈ CtxImp Wᵖ ]
     Σ[ rᵖ ∈ A ⊑ᵂ⟨ Wᵖ ⟩ S ]
       (CTI2.ImpEnvMono Wᵒ Wᵖ
        × CTI2.SameCtx γᵒ γᵖ
        × RebaseAt Wᵖ Wᵒ Xᴸ Y
        × sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ A
        × targetStoreʷ Wᵒ ∋ Y ⦂ S
        × CTI2.StoreRepImp Wᵒ Xᴸ Y
        × Wᵖ ∣ γᵖ ⊢² P ⊑ U ∶ rᵖ))
    → SourcePairedBranch Wᵒ γᵒ P A U Xᴸ Y S

data SourceCorePremise {Δᴸ Δᴿ Δ}
    (Wᶜ : World Δᴸ Δᴿ Δ) (γᶜ : CtxImp Wᶜ)
    (P : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (Y : TyVar Δᴿ) (S : Ty Δᴿ)
    (pᶜ : A ⊑ᵂ⟨ Wᶜ ⟩ ★)
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★) : Set where
  core-tagged :
    Wᶜ ∣ γᶜ ⊢² P ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ pᶜ
    → SourceCorePremise Wᶜ γᶜ P A U Y S pᶜ cY

  core-untagged :
      (rᶜ : A ⊑ᵂ⟨ Wᶜ ⟩ (＇ Y))
    → Wᶜ ∣ γᶜ ⊢² P ⊑ U ↓ seal Y S ∶ rᶜ
    → SourceCorePremise Wᶜ γᶜ P A U Y S pᶜ cY

data SourceSpineStripBranch {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (V : Term Δᴸ) (R : Ty Δᴸ)
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ)
    (Y : TyVar Δᴿ) (S : Ty Δᴿ)
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★)
    (q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y))
    (Core : Term Δᴸ) (CoreTy : Ty Δᴸ) (Xᵒ : TyVar Δᴸ)
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (qᵒ : (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y)) : Set where
  spine-sealed :
      (Premise : Term Δᴸ)
      (PremiseTy : Ty Δᴸ)
    → SpineValue Premise
    → (sealed :
        Σ[ Wʳ ∈ World Δᴸ Δᴿ Δ ]
        Σ[ γʳ ∈ CtxImp Wʳ ]
        Σ[ qʳ ∈ PremiseTy ⊑ᵂ⟨ Wʳ ⟩ (＇ Y) ]
          (CTI2.ImpEnvMono Wᵒ Wʳ
           × CTI2.SameCtx γᵒ γʳ
           × RebaseAtᴸ Wʳ Wᵒ (just Xᵒ)
           × targetStoreʷ Wʳ ∋ Y ⦂ S
           × Wʳ ∣ γʳ ⊢² Premise ⊑ U ↓ seal Y S ∶ qʳ))
    → ((Σ[ Wʳ ∈ World Δᴸ Δᴿ Δ ]
        Σ[ γʳ ∈ CtxImp Wʳ ]
        Σ[ qʳ ∈ PremiseTy ⊑ᵂ⟨ Wʳ ⟩ (＇ Y) ]
          (CTI2.ImpEnvMono Wᵒ Wʳ
           × CTI2.SameCtx γᵒ γʳ
           × RebaseAtᴸ Wʳ Wᵒ (just Xᵒ)
           × targetStoreʷ Wʳ ∋ Y ⦂ S
           × Wʳ ∣ γʳ ⊢² Premise ⊑ U ↓ seal Y S ∶ qʳ))
       → W ∣ γ ⊢² V ↓ seal Xᴸ R ⊑ U ↓ seal Y S ∶ q)
    → SourceSpineStripBranch W γ V R U Xᴸ Y S cY q
        Core CoreTy Xᵒ Wᵒ γᵒ qᵒ

  spine-tagged :
      (Premise : Term Δᴸ)
      (PremiseTy : Ty Δᴸ)
    → SpineValue Premise
    → (Wᵖ : World Δᴸ Δᴿ Δ)
      (γᵖ : CtxImp Wᵖ)
    → (pᵖ : PremiseTy ⊑ᵂ⟨ Wᵖ ⟩ ★)
    → CTI2.ImpEnvMono Wᵒ Wᵖ
    → CTI2.SameCtx γᵒ γᵖ
    → RebaseAt Wᵖ Wᵒ Xᵒ Y
    → sourceStoreʷ Wᵒ ∋ Xᵒ ⦂ ★
    → targetStoreʷ Wᵒ ∋ Y ⦂ S
    → Wᵖ ∣ γᵖ ⊢² Premise ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ pᵖ
    → (SourceTagSealCoreBranch Wᵒ γᵒ Premise PremiseTy U Xᵒ Y S
          cY Wᵖ γᵖ pᵖ
       → W ∣ γ ⊢² V ↓ seal Xᴸ R ⊑ U ↓ seal Y S ∶ q)
    → SourceSpineStripBranch W γ V R U Xᴸ Y S cY q
        Core CoreTy Xᵒ Wᵒ γᵒ qᵒ

  spine-paired :
      (Premise : Term Δᴸ)
      (PremiseTy : Ty Δᴸ)
    → SpineValue Premise
    → (paired : SourcePairedBranch Wᵒ γᵒ Premise PremiseTy U Xᵒ Y S)
    → (SourcePairedBranch Wᵒ γᵒ Premise PremiseTy U Xᵒ Y S
       → W ∣ γ ⊢² V ↓ seal Xᴸ R ⊑ U ↓ seal Y S ∶ q)
    → SourceSpineStripBranch W γ V R U Xᴸ Y S cY q
        Core CoreTy Xᵒ Wᵒ γᵒ qᵒ

data SourceColumnStripBranch {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (V : Term Δᴸ)
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ)
    (Y : TyVar Δᴿ) (S : Ty Δᴿ)
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★)
    (q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y))
    (Core : Term Δᴸ) (CoreTy : Ty Δᴸ) (Xᵒ : TyVar Δᴸ)
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (qᵒ : (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y)) : Set where
  column-sealed :
      (Premise : Term Δᴸ)
      (PremiseTy : Ty Δᴸ)
    → SpineValue Premise
    → (sealed :
        Σ[ Wʳ ∈ World Δᴸ Δᴿ Δ ]
        Σ[ γʳ ∈ CtxImp Wʳ ]
        Σ[ qʳ ∈ PremiseTy ⊑ᵂ⟨ Wʳ ⟩ (＇ Y) ]
          (CTI2.ImpEnvMono Wᵒ Wʳ
           × CTI2.SameCtx γᵒ γʳ
           × RebaseAtᴸ Wʳ Wᵒ (just Xᵒ)
           × targetStoreʷ Wʳ ∋ Y ⦂ S
           × Wʳ ∣ γʳ ⊢² Premise ⊑ U ↓ seal Y S ∶ qʳ))
    → ((Σ[ Wʳ ∈ World Δᴸ Δᴿ Δ ]
        Σ[ γʳ ∈ CtxImp Wʳ ]
        Σ[ qʳ ∈ PremiseTy ⊑ᵂ⟨ Wʳ ⟩ (＇ Y) ]
          (CTI2.ImpEnvMono Wᵒ Wʳ
           × CTI2.SameCtx γᵒ γʳ
           × RebaseAtᴸ Wʳ Wᵒ (just Xᵒ)
           × targetStoreʷ Wʳ ∋ Y ⦂ S
           × Wʳ ∣ γʳ ⊢² Premise ⊑ U ↓ seal Y S ∶ qʳ))
       → W ∣ γ ⊢² V ⊑ U ↓ seal Y S ∶ q)
    → SourceColumnStripBranch W γ V U Xᴸ Y S cY q
        Core CoreTy Xᵒ Wᵒ γᵒ qᵒ

  column-tagged :
      (Premise : Term Δᴸ)
      (PremiseTy : Ty Δᴸ)
    → SpineValue Premise
    → (Wᵖ : World Δᴸ Δᴿ Δ)
      (γᵖ : CtxImp Wᵖ)
    → (pᵖ : PremiseTy ⊑ᵂ⟨ Wᵖ ⟩ ★)
    → CTI2.ImpEnvMono Wᵒ Wᵖ
    → CTI2.SameCtx γᵒ γᵖ
    → RebaseAt Wᵖ Wᵒ Xᵒ Y
    → sourceStoreʷ Wᵒ ∋ Xᵒ ⦂ ★
    → targetStoreʷ Wᵒ ∋ Y ⦂ S
    → Wᵖ ∣ γᵖ ⊢² Premise ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ pᵖ
    → (SourceTagSealCoreBranch Wᵒ γᵒ Premise PremiseTy U Xᵒ Y S
          cY Wᵖ γᵖ pᵖ
       → W ∣ γ ⊢² V ⊑ U ↓ seal Y S ∶ q)
    → SourceColumnStripBranch W γ V U Xᴸ Y S cY q
        Core CoreTy Xᵒ Wᵒ γᵒ qᵒ

  column-paired :
      (Premise : Term Δᴸ)
      (PremiseTy : Ty Δᴸ)
    → SpineValue Premise
    → (paired : SourcePairedBranch Wᵒ γᵒ Premise PremiseTy U Xᵒ Y S)
    → (SourcePairedBranch Wᵒ γᵒ Premise PremiseTy U Xᵒ Y S
       → W ∣ γ ⊢² V ⊑ U ↓ seal Y S ∶ q)
    → SourceColumnStripBranch W γ V U Xᴸ Y S cY q
        Core CoreTy Xᵒ Wᵒ γᵒ qᵒ

------------------------------------------------------------------------
-- Source strip surfaces
------------------------------------------------------------------------

SourceSpineStrip : Set
SourceSpineStrip =
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {R : Ty Δᴸ} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p₀ : R ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ R
  → targetStoreʷ W ∋ Y ⦂ S
  → W′ ∣ γ′ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p₀
  → Σ[ Core ∈ Term Δᴸ ]
    Σ[ CoreTy ∈ Ty Δᴸ ]
    Σ[ Xᵒ ∈ TyVar Δᴸ ]
    Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ γᵒ ∈ CtxImp Wᵒ ]
    Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
      (SpineValue Core
       × SourceSpineStripBranch W γ V R U Xᴸ Y S cY q
           Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)

SourceColumnStrip : Set
SourceColumnStrip =
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {S : Ty Δᴿ} {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → targetStoreʷ W ∋ Y ⦂ S
  → W′ ∣ γ′ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → Σ[ Core ∈ Term Δᴸ ]
    Σ[ CoreTy ∈ Ty Δᴸ ]
    Σ[ Xᵒ ∈ TyVar Δᴸ ]
    Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ]
    Σ[ γᵒ ∈ CtxImp Wᵒ ]
    Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y) ]
      (SpineValue Core
       × SourceColumnStripBranch W γ V U Xᴸ Y S cY q
           Core CoreTy Xᵒ Wᵒ γᵒ qᵒ)

SourceSpineStripWorker : Set
SourceSpineStripWorker = SourceSpineStrip

SourceColumnStripWorker : Set
SourceColumnStripWorker = SourceColumnStrip

SourceTagSealCore : Set
SourceTagSealCore =
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {S : Ty Δᴿ} {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ ★}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y)}
  → SpineValue P
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → SourceCorePremise Wᵖ γᵖ P A U Y S p cY
  → SourceTagSealCoreBranch Wᵒ γᵒ P A U Xᴸ Y S cY Wᵖ γᵖ p
