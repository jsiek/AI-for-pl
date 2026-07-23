module
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameClosingProof
  where

-- File Charter:
--   * Implements the recursive outer-`∀ⁱ` source-generic frame handler from
--     one fused generic-beta commutation theorem.
--   * Projects exact endpoint evidence from the inner frame view and
--     reconstructs the authoritative generic-cast QTI relation.
--   * Contains no handler assembly, broad simulation import, postulate, hole,
--     or permissive option.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; genᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
import NarrowWiden as NW
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using (cast⊒⊑ᵀ)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; WfTy; `∀; occurs; ⇑ᵗ; ⟰ᵗ)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewProperties
  using
  ( paired-lambda-target-closing-frame-view-relation
  ; paired-lambda-target-closing-frame-view-source-no-bullet
  ; paired-lambda-target-closing-frame-view-source-value
  ; paired-lambda-target-closing-frame-view-target-no-bullet
  ; paired-lambda-target-closing-frame-view-target-value
  )
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameCommutationDef
  using (PairedLambdaTargetClosingSourceGenFrameCommutationᵀ)


paired-lambda-target-closing-source-gen-frame-closing-proofᵀ :
  PairedLambdaTargetClosingSourceGenFrameCommutationᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V N′ : Term} {F B B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ `∀ B′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {c : Coercion} {μ : ModeEnv} →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    V N′ F (`∀ B′) q →
  PairedLambdaTargetClosingFrameView ρ
    V N′ (`∀ F) (`∀ B′) q →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  (hA : WfTy Δᴸ (`∀ F)) →
  (occ : occurs zero B ≡ true) →
  genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
    ⊢ c ∶ ⇑ᵗ (`∀ F) =⇒ B →
  NW.Narrowing c →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (V ⟨ C.gen (`∀ F) c ⟩) N′ B (`∀ B′) (∀ⁱ r)
paired-lambda-target-closing-source-gen-frame-closing-proofᵀ
    commutation {r = r} inner view mode seal★ hA occ c⊢ cⁿ
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion =
  commutation
    (paired-lambda-target-closing-frame-view-source-value view)
    (paired-lambda-target-closing-frame-view-source-no-bullet view)
    (paired-lambda-target-closing-frame-view-target-value view)
    (paired-lambda-target-closing-frame-view-target-no-bullet view)
    relation
    (cast⊒⊑ᵀ mode seal★ (C.cast-gen hA occ c⊢ , NW.gen cⁿ)
      relation (∀ⁱ r))
    inner
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion
  where
  relation = paired-lambda-target-closing-frame-view-relation view
