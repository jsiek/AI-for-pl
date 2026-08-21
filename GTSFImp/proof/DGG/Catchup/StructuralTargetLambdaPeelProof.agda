module proof.DGG.Catchup.StructuralTargetLambdaPeelProof where

-- File Charter:
--   * Peels a completed target package whose first strict head is β-Λ.
--   * Returns the caller's inserted target world and the opened child
--     package.
--   * This is the inverse package decomposition for
--     structural-target-Λ-step, without forcing a canonical insert proof.

import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
  renaming (subst to subst≡)

open import Types using (Ty; TyCtx; TyVar; ＇_; _[_]ᵗ; ⇑ᵗ)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import CastTerms using (Term; Value; Λ_; _⦂∀_[_]; _↑_)
open import Conversion using (〖_,_↑_〗)
open import Reduction using
  (bind; keep; applyStores; _∷_; []; β-Λ; ξ-•; _—→[_]_;
   _—↠[_]_; ↠-refl; ↠-step)
open import proof.TypeSafety.Preservation using (replace-zero-open)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.FuelSupportProof using (mapCtxᴿ-compose)
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof using
  (structural-target-frame)
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof
  using (no-value-type-app; no-value-apply-spine; value-no-step)
open import
  proof.DGG.Catchup.StructuralTargetSpineStepInversionProof
    using (spine-bind-step-inversion; spine-keep-step-inversion)


lambda-head-keep-impossible : ∀ {Δ} {B : Ty (suc Δ)}
    {V : Term (suc Δ)} {X : TyVar Δ} {N : Term Δ}
  → Value V
  → ((Λ V) ⦂∀ B [ ＇ X ]) —→[ keep ] N
  → ⊥
lambda-head-keep-impossible vV (ξ-• step refl refl) =
  value-no-step (Λ vV) step


data LambdaHeadBindView {Δ} {B : Ty (suc Δ)}
    {V : Term (suc Δ)} {X : TyVar Δ}
    : {R : Ty Δ} → Term (suc Δ) → Set where

  lambda-bind-target :
    LambdaHeadBindView {B = B} {V = V} {X = X}
      {R = ＇ X} (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)


lambda-head-bind-view : ∀ {Δ} {B : Ty (suc Δ)}
    {V : Term (suc Δ)} {X : TyVar Δ} {R : Ty Δ}
    {N : Term (suc Δ)}
  → Value V
  → ((Λ V) ⦂∀ B [ ＇ X ]) —→[ bind R ] N
  → LambdaHeadBindView {B = B} {V = V} {X = X} {R = R} N
lambda-head-bind-view vV (β-Λ vW) = lambda-bind-target
lambda-head-bind-view vV (ξ-• step refl refl) =
  ⊥-elim (value-no-step (Λ vV) step)


structural-target-Λ-peel : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {V : Term (suc Δᴿ)} {X : TyVar Δᴿ}
    (vV : Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (target : StructuralTargetInstantiationPackage W (Λ V)
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → Σ[ Δ₁ ∈ TyCtx ]
    Σ[ π ∈ Δ ↪ᵗ Δ₁ ]
    Σ[ W₁ ∈ CTI2.World Δᴸ (suc Δᴿ) Δ₁ ]
    Σ[ ins ∈ TE.TargetInsert wk↪ᵗ π W W₁ ]
    Σ[ follows ∈
      CTI2.targetStoreʷ W₁ ≡
        applyStores (bind (＇ X) ∷ []) (CTI2.targetStoreʷ W) ]
      Σ[ child-target ∈ StructuralTargetInstantiationPackage W₁ V
        (lambda-ready-child-spine {B = B} {X = X} spine) ]
        (∀ {γ : CTI2.CtxImp W} {M : Term Δᴸ}
           {L : Ty Δᴸ} {q : L CTI2.⊑ᵂ⟨ W ⟩ E}
         → let ext₁ = target-insert-bind-world-extendᴿ ins follows
            in StructuralTargetInstantiationPackage.W′ child-target CTIR.∣
              ECR.mapCtxᴿ
                (structural-world-extendᴿ
                  (StructuralTargetInstantiationPackage.structural-ext
                    child-target))
                (ECR.mapCtxᴿ ext₁ γ)
              ⊢² M ⊑ StructuralTargetInstantiationPackage.final child-target
                ∶ ECR.transport⊑ᵂ
                  (structural-world-extendᴿ
                    (StructuralTargetInstantiationPackage.structural-ext
                      child-target))
                  (ECR.transport⊑ᵂ ext₁ q)
         → StructuralTargetInstantiationPackage.W′ target CTIR.∣
             ECR.mapCtxᴿ
               (structural-world-extendᴿ
                 (StructuralTargetInstantiationPackage.structural-ext target))
               γ
             ⊢² M ⊑ StructuralTargetInstantiationPackage.final target
               ∶ ECR.transport⊑ᵂ
                 (structural-world-extendᴿ
                   (StructuralTargetInstantiationPackage.structural-ext
                     target))
                 q)
structural-target-Λ-peel vV spine target
    with StructuralTargetInstantiationPackage.post-reduction target
structural-target-Λ-peel vV spine target | ↠-refl =
  ⊥-elim
    (no-value-apply-spine spine no-value-type-app
      (StructuralTargetInstantiationPackage.final-value target))
structural-target-Λ-peel vV spine target
    | ↠-step {N = N} {χ = keep} first rest
    with spine-keep-step-inversion spine (β-Λ vV)
      no-value-type-app first
structural-target-Λ-peel vV spine target
    | ↠-step {N = N} {χ = keep} first rest
    | M₂ , (head-step , eq) =
  ⊥-elim (lambda-head-keep-impossible vV head-step)
structural-target-Λ-peel vV spine target
    | ↠-step {N = N} {χ = bind R} {χs = χs} first rest
    with spine-bind-step-inversion spine no-value-type-app first
structural-target-Λ-peel {B = B} {X = X} vV spine target
    | ↠-step {N = N} {χ = bind R} {χs = χs} first rest
    | M₂ , (head-step , eq)
    with lambda-head-bind-view vV head-step
structural-target-Λ-peel {W = W} {B = B} {V = V} {X = X}
    vV spine target
    | ↠-step {N = N} {χ = bind .(＇ X)} {χs = χs} first rest
    | .(V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) , (head-step , eq)
    | lambda-bind-target
    with StructuralTargetInstantiationPackage.structural-ext target
structural-target-Λ-peel {B = B} {V = V} {X = X} vV spine target
    | ↠-step {χ = bind .(＇ X)} {χs = χs} first rest
    | .(V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) , (head-step , eq)
    | lambda-bind-target
    | structural-bind {π = π} {W₁ = W₁} ins follows child-ext =
  _ , π , W₁ , ins , follows , child-target ,
    (λ {γ = γ} child-rel →
      subst≡
        (λ γ′ → _ CTIR.∣ γ′ ⊢² _ ⊑ _ ∶ _)
        (mapCtxᴿ-compose ext₁ (structural-world-extendᴿ child-ext) γ)
        child-rel)
  where
  raw-child-target =
    record
      { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ target
      ; χs = χs
      ; Δ′ = StructuralTargetInstantiationPackage.Δ′ target
      ; W′ = StructuralTargetInstantiationPackage.W′ target
      ; structural-ext = child-ext
      ; final = StructuralTargetInstantiationPackage.final target
      ; final-value = StructuralTargetInstantiationPackage.final-value target
      ; post-reduction =
          subst≡ (λ T → T —↠[ χs ]
            StructuralTargetInstantiationPackage.final target)
            eq
            rest
      }

  child-target =
    structural-target-frame {V = V}
      {frame = reveal-frame
        (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)} raw-child-target

  ext₁ = target-insert-bind-world-extendᴿ ins follows
