module proof.DGG.Catchup.StructuralInstantiationDescentDef where

-- File Charter:
--   * Records target-spine descent with a structural world-extension trace.
--   * Retains insertion history until source wrappers have been rebuilt.

open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Types using (Ty; TyCtx; TyVar; ＇_; `∀; _[_]ᵗ)
open import CastTerms using (Term; Value)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import Imprecision using (X⊑★)
open import Reduction using (StoreChanges; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)


record StructuralInstantiationDescentPackage {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (γ : CTI2.CtxImp W)
    (M : Term Δᴸ) (V : Term Δᴿ) {A : Ty Δᴸ} {B E : Ty Δᴿ}
    (spine : InstantiationSpine B E)
    (q : A CTI2.⊑ᵂ⟨ W ⟩ E) : Set₁ where
  field
    target-descent : StructuralTargetInstantiationPackage W V spine
    final-relation :
      StructuralTargetInstantiationPackage.W′ target-descent CTI2.∣
        ECR.mapCtxᴿ (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext
            target-descent)) γ
        ⊢² M ⊑
          StructuralTargetInstantiationPackage.final target-descent ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext
                target-descent)) q


record StructuralNamePostPlan {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (A : Ty Δᴸ) (E : Ty Δᴿ)
    (q : A CTI2.⊑ᵂ⟨ W ⟩ E) : Set₁ where
  inductive
  field
    cast-child : ∀ {A₀ : Ty Δᴸ} {ν : Env∼ Δᴸ}
      → ν ⊢ A₀ ∼ A
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ W ⟩ E ]
          StructuralNamePostPlan W A₀ E q₀

    plain-Λ-child : ∀ {A₀ : Ty (suc Δᴸ)}
      → A ≡ `∀ A₀
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ E ]
          StructuralNamePostPlan
            (CTI2.liftWorldLeft X⊑★ W) A₀ E q₀

    smart-Λ-child : ∀ {Δᵐ} {A₀ : Ty (suc Δᴸ)}
        {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
      → A ≡ `∀ A₀
      → CTI2.SmartCommaLiftᴸ W Wᵐ
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ Wᵐ ⟩ E ]
          StructuralNamePostPlan Wᵐ A₀ E q₀

    reveal-child : ∀ {A₀ : Ty Δᴸ} {Wᵖ Xᴸ?}
        {c : Conv↑ Δᴸ A₀ A}
      → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ Wᵖ ⟩ E ]
          StructuralNamePostPlan Wᵖ A₀ E q₀

    conceal-child : ∀ {A₀ : Ty Δᴸ} {Wᵖ Xᴸ? Xᴿ?}
        {c : Conv↓ Δᴸ A₀ A}
      → CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ Wᵖ ⟩ E ]
          StructuralNamePostPlan Wᵖ A₀ E q₀


StructuralNameInstantiationᵀ : Set₁
StructuralNameInstantiationᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → StructuralNamePostPlan W A E q
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → Value M
  → Value V
  → AllValueView V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → StructuralTargetInstantiationPackage.W′ target CTI2.∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        γ
      ⊢² M ⊑ StructuralTargetInstantiationPackage.final target ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          q
