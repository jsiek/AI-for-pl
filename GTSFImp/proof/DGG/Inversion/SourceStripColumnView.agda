module proof.DGG.Inversion.SourceStripColumnView where

-- File Charter:
--   * Provides the small column-source seal extraction view used by
--     `SourceStripWorkerProof`.
--   * Keeps the non-covering extraction clauses separate from the large
--     branch-producing worker proof to avoid Agda compiled-clause pressure.
--   * Exposes only the view and its constructor cases.

open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms using (Term; _↓_; _⟨_⟩)
open import Imprecision
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.SealPeelToolkit as SPT

open CTX using
  (World;
   CtxImp;
   RebaseAt;
   _⊑ᵂ⟨_⟩_;
   sourceStoreʷ)
open CTI2 using (_∣_⊢²_⊑_∶_)

data SourceColumnSealDCase {Δᴸ Δᴿ Δ}
    (W′ : World Δᴸ Δᴿ Δ) (γ′ : CtxImp W′)
    (V : Term Δᴸ) (U : Term Δᴿ)
    (R : Ty Δᴸ) (S : Ty Δᴿ)
    (Xᴸ : TyVar Δᴸ) (Y : TyVar Δᴿ)
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★)
    (p : (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ ★) : Set where
  column-seal-target-cast-case :
      {pᵤ : (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
    → W′ ∣ γ′ ⊢² V ↓ seal Xᴸ R ⊑ U ↓ seal Y S ∶ pᵤ
    → SourceColumnSealDCase W′ γ′ V U R S Xᴸ Y cY p

  column-seal-source-case :
      {Wᵢ : World Δᴸ Δᴿ Δ}
      {γᵢ : CtxImp Wᵢ}
      {pᵤ : R ⊑ᵂ⟨ Wᵢ ⟩ (＇ Y)}
    → CTX.ImpEnvMono W′ Wᵢ
    → RebaseAt Wᵢ W′ Xᴸ Y
    → CTX.SameCtx γ′ γᵢ
    → sourceStoreʷ W′ ∋ Xᴸ ⦂ R
    → Wᵢ ∣ γᵢ ⊢² V ⊑ U ↓ seal Y S ∶ pᵤ
    → SourceColumnSealDCase W′ γ′ V U R S Xᴸ Y cY p

source-column-seal-D-case : ∀ {Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ Δ}
    {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {R : Ty Δᴸ} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ ★}
  → W′ ∣ γ′ ⊢² V ↓ seal Xᴸ R
      ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → SourceColumnSealDCase W′ γ′ V U R S Xᴸ Y cY p
{-# NON_COVERING #-}
source-column-seal-D-case (CTI2.⊑cast² {p = pᵤ} cY′ prem p) =
  column-seal-target-cast-case prem
source-column-seal-D-case
    (CTI2.conceal⊑²-source-ok
      (CTX.seal-nonstar-name-protected-ok Rns aligned)
      monoᵢ (CTX.tag-rebase-varᴸ link) scᵢ
      (Conv.⊢↓-sealˣ X∈)
      (CTI2.⊑cast² {p = pᵤ} cY prem p★) p) =
  column-seal-source-case monoᵢ link scᵢ X∈ prem
