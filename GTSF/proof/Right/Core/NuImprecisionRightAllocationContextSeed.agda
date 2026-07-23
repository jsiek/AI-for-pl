module proof.Right.Core.NuImprecisionRightAllocationContextSeed where

-- File Charter:
--   * Constructs context and target-only store-lineage seeds for the ordinary
--     and casted right-allocation weak steps.
--   * Connects the completed allocation simulations to the strengthened
--     contextual catch-up boundary.
--   * Contains no recursive catch-up, result/view/outcome type, postulate,
--     hole, permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_; Σ-syntax)

open import Coercions using (instᵈ)
open import Conversion using (RevealConversion)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; ⇑ᴿᵢ)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using (bind)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using (No•; Term; Value)
open import QuotientedTermImprecision using
  ( prefix-reflⁱ
  ; prefix-∷ⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; WfTy; ★; `∀; ⟰ᵗ; ⇑ᵗ)
open import proof.NuCore.Misc.NuImprecisionAllocationSimulation using
  ( weak-one-step-right-νcastᵀ
  ; weak-one-step-right-ν↑ᵀ
  )
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (lift-right-store-embeddingⁱ)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  ( right-only-prefix-refl
  ; right-only-prefix-right
  ; RightOnlyStoreImpPrefix
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  (resultCtx; resultStore; WeakOneStepResult)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( WeakOneStepStoreLineage
  ; lineageStore
  ; weak-step-store-lineage
  )


weak-one-step-right-ν↑-context-seedᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A B B′ C′ : Ty} {N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  (s′↑ : RevealConversion μ (suc Δᴿ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A) s C′ (⇑ᵗ B′)) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q) →
  let result = weak-one-step-right-ν↑ᵀ
        vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′
  in
  Σ[ lineage ∈ WeakOneStepStoreLineage result ]
    (resultCtx result ≡
      applyRightImpCtxChanges (bind A ∷ []) Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore lineage) (resultStore result)
weak-one-step-right-ν↑-context-seedᵀ
    vN′ noN′ h⇑A s′↑ pB pC liftρ N⊑N′ =
  weak-step-store-lineage
      _
      (lift-right-store-embeddingⁱ liftρ)
      (prefix-∷ⁱ prefix-reflⁱ) ,
  refl ,
  right-only-prefix-right right-only-prefix-refl


weak-one-step-right-νcast-context-seedᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {B B′ C′ : Ty} {N N′ s μ q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
  (vN′ : Value N′) →
  (noN′ : No• N′) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ))) →
  (s⊑ : instᵈ μ ∣ suc Δᴿ
    ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
    ⊢ s ∶ C′ ⊑ ⇑ᵗ B′) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  (pC : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
  (liftρ : LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′) →
  (N⊑N′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ `∀ C′ ∶ q) →
  let result = weak-one-step-right-νcastᵀ
        vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′
  in
  Σ[ lineage ∈ WeakOneStepStoreLineage result ]
    (resultCtx result ≡
      applyRightImpCtxChanges (bind ★ ∷ []) Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore lineage) (resultStore result)
weak-one-step-right-νcast-context-seedᵀ
    vN′ noN′ mode seal★ s⊑ pB pC liftρ N⊑N′ =
  weak-step-store-lineage
      _
      (lift-right-store-embeddingⁱ liftρ)
      (prefix-∷ⁱ prefix-reflⁱ) ,
  refl ,
  right-only-prefix-right right-only-prefix-refl
