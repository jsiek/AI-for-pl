module proof.DGG.Catchup.StructuralTargetInstantiationProof where

-- File Charter:
--   * Constructs target-only normalization for empty and framed spines.
--   * Composes pure keep and allocating bind steps with completed packages.

open import Types using (Ty)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import CastTerms using (Term; Value)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores;
   _—→[_]_; ↠-refl; ↠-step)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof
open import proof.DGG.Catchup.StructuralFrameOutcomeDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralTargetInstantiationDef


structural-target-zero : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {V : Term Δᴿ} {B : Ty Δᴿ}
  → Value V
  → StructuralTargetInstantiationPackage W V {B = B} []ⁱ
structural-target-zero {W = W} vV = record
  { Δᴿ′ = _
  ; χs = []
  ; Δ′ = _
  ; W′ = W
  ; structural-ext = structural-[]
  ; final = _
  ; final-value = vV
  ; post-reduction = ↠-refl
  }


structural-target-frame : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V : Term Δᴿ} {A B E : Ty Δᴿ}
    {frame : InstantiationFrame A B}
    {spine : InstantiationSpine B E}
  → StructuralTargetInstantiationPackage W
      (applyInstantiationFrame V frame) spine
  → StructuralTargetInstantiationPackage W V (frame ▻ⁱ spine)
structural-target-frame child = record
  { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ child
  ; χs = StructuralTargetInstantiationPackage.χs child
  ; Δ′ = StructuralTargetInstantiationPackage.Δ′ child
  ; W′ = StructuralTargetInstantiationPackage.W′ child
  ; structural-ext =
      StructuralTargetInstantiationPackage.structural-ext child
  ; final = StructuralTargetInstantiationPackage.final child
  ; final-value = StructuralTargetInstantiationPackage.final-value child
  ; post-reduction =
      StructuralTargetInstantiationPackage.post-reduction child
  }


structural-target-keep-step : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V V₁ : Term Δᴿ} {B E B₁ E₁ : Ty Δᴿ}
    {spine : InstantiationSpine B E}
    {spine₁ : InstantiationSpine B₁ E₁}
  → applyInstantiationSpine V spine —→[ keep ]
      applyInstantiationSpine V₁ spine₁
  → StructuralTargetInstantiationPackage W V₁ spine₁
  → StructuralTargetInstantiationPackage W V spine
structural-target-keep-step step child = record
  { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ child
  ; χs = keep ∷ StructuralTargetInstantiationPackage.χs child
  ; Δ′ = StructuralTargetInstantiationPackage.Δ′ child
  ; W′ = StructuralTargetInstantiationPackage.W′ child
  ; structural-ext = structural-keep
      (StructuralTargetInstantiationPackage.structural-ext child)
  ; final = StructuralTargetInstantiationPackage.final child
  ; final-value = StructuralTargetInstantiationPackage.final-value child
  ; post-reduction = ↠-step step
      (StructuralTargetInstantiationPackage.post-reduction child)
  }


structural-target-frame-keep-step : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V V₁ : Term Δᴿ} {A B E : Ty Δᴿ}
    {frame : InstantiationFrame A B}
    {spine : InstantiationSpine B E}
  → applyInstantiationFrame V frame —→[ keep ] V₁
  → StructuralTargetInstantiationPackage W V₁
      (mapInstantiationSpine keep spine)
  → StructuralTargetInstantiationPackage W V (frame ▻ⁱ spine)
structural-target-frame-keep-step {spine = spine} step child =
  structural-target-frame
    (structural-target-keep-step
      (lift-instantiation-spine-keep step spine) child)


structural-target-frame-outcome : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V : Term Δᴿ} {A B E : Ty Δᴿ}
    {frame : InstantiationFrame A B}
    {spine : InstantiationSpine B E}
  → StructuralFrameOutcome (applyInstantiationFrame V frame)
  → (Value (applyInstantiationFrame V frame)
      → StructuralTargetInstantiationPackage W
          (applyInstantiationFrame V frame) spine)
  → (∀ {V₁}
      → applyInstantiationFrame V frame —→[ keep ] V₁
      → Value V₁
      → StructuralTargetInstantiationPackage W V₁
          (mapInstantiationSpine keep spine))
  → StructuralTargetInstantiationPackage W V (frame ▻ⁱ spine)
structural-target-frame-outcome (structural-frame-value vF)
    value-child keep-child =
  structural-target-frame (value-child vF)
structural-target-frame-outcome (structural-frame-keep step vF)
    value-child keep-child =
  structural-target-frame-keep-step step (keep-child step vF)


structural-target-bind-step : ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {R : Ty Δᴿ} {π : Δ ↪ᵗ Δ₁}
    {V : Term Δᴿ} {V₁ : Term (suc Δᴿ)}
    {B E : Ty Δᴿ} {B₁ E₁ : Ty (suc Δᴿ)}
    {spine : InstantiationSpine B E}
    {spine₁ : InstantiationSpine B₁ E₁}
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → CTI2.targetStoreʷ W₁ ≡
      applyStores (bind R ∷ []) (CTI2.targetStoreʷ W)
  → applyInstantiationSpine V spine —→[ bind R ]
      applyInstantiationSpine V₁ spine₁
  → StructuralTargetInstantiationPackage W₁ V₁ spine₁
  → StructuralTargetInstantiationPackage W V spine
structural-target-bind-step ins follows step child = record
  { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ child
  ; χs = bind _ ∷ StructuralTargetInstantiationPackage.χs child
  ; Δ′ = StructuralTargetInstantiationPackage.Δ′ child
  ; W′ = StructuralTargetInstantiationPackage.W′ child
  ; structural-ext = structural-bind ins follows
      (StructuralTargetInstantiationPackage.structural-ext child)
  ; final = StructuralTargetInstantiationPackage.final child
  ; final-value = StructuralTargetInstantiationPackage.final-value child
  ; post-reduction = ↠-step step
      (StructuralTargetInstantiationPackage.post-reduction child)
  }
