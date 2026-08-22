module proof.DGG.Catchup.StructuralTargetRevealPeelProof where

-- File Charter:
--   * Peels a completed target package whose first strict head is
--     β-reveal-∀.
--   * Returns the caller's inserted target world and the child package
--     beneath the exposed type application and reveal frames.
--   * This is proof support for strict structural name-instantiation cases.

import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  renaming (subst to subst≡)

open import Types using (Ty; TyCtx; TyVar; ＇_; _[_]ᵗ; ⇑ᵗ)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import Conversion using (Conv↑; `∀↑_; 〖_,_↑_〗)
import CastTerms as CT
open import CastTerms using (Term; Value; _⦂∀_[_]; _↑_; ⇑ᵗᵐ)
open import Reduction using
  (bind; keep; applyBody; applyStores; _∷_; []; β-reveal-∀; ξ-•;
   _—→[_]_; _—↠[_]_; ↠-refl; ↠-step)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.FuelSupportProof using (mapCtxᴿ-compose)
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof
  using (no-value-type-app; no-value-apply-spine; value-no-step)
open import
  proof.DGG.Catchup.StructuralTargetSpineStepInversionProof
    using (spine-bind-step-inversion; spine-keep-step-inversion)


reveal-head-keep-impossible : ∀ {Δ} {B C : Ty (suc Δ)}
    {c : Conv↑ (suc Δ) C B}
    {V : Term Δ} {X : TyVar Δ} {N : Term Δ}
  → Value V
  → ((V ↑ `∀↑ c) ⦂∀ B [ ＇ X ]) —→[ keep ] N
  → ⊥
reveal-head-keep-impossible vV (ξ-• step refl refl) =
  value-no-step (vV CT.↑ CT.all) step


data RevealHeadBindView {Δ} {B C : Ty (suc Δ)}
    {c : Conv↑ (suc Δ) C B}
    {V : Term Δ} {X : TyVar Δ}
    : {R : Ty Δ} → Term (suc Δ) → Set where

  reveal-bind-target :
    RevealHeadBindView {c = c} {V = V} {X = X} {R = ＇ X}
      (((⇑ᵗᵐ V ⦂∀ applyBody (bind (＇ X)) C [ ＇ Fin.zero ]) ↑ c)
        ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)


reveal-head-bind-view : ∀ {Δ} {B C : Ty (suc Δ)}
    {c : Conv↑ (suc Δ) C B}
    {V : Term Δ} {X : TyVar Δ} {R : Ty Δ}
    {N : Term (suc Δ)}
  → Value V
  → ((V ↑ `∀↑ c) ⦂∀ B [ ＇ X ]) —→[ bind R ] N
  → RevealHeadBindView {c = c} {V = V} {X = X} {R = R} N
reveal-head-bind-view vV (β-reveal-∀ vW) = reveal-bind-target
reveal-head-bind-view vV (ξ-• step refl refl) =
  ⊥-elim (value-no-step (vV CT.↑ CT.all) step)


structural-target-reveal-peel : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {c : Conv↑ (suc Δᴿ) C B}
    {V : Term Δᴿ} {X : TyVar Δᴿ}
    (vV : Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (target : StructuralTargetInstantiationPackage W (V ↑ `∀↑ c)
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → Σ[ Δ₁ ∈ TyCtx ]
    Σ[ π ∈ Δ ↪ᵗ Δ₁ ]
    Σ[ W₁ ∈ CTI2.World Δᴸ (suc Δᴿ) Δ₁ ]
    Σ[ ins ∈ TE.TargetInsert wk↪ᵗ π W W₁ ]
    Σ[ follows ∈
      CTI2.targetStoreʷ W₁ ≡
        applyStores (bind (＇ X) ∷ []) (CTI2.targetStoreʷ W) ]
      Σ[ child-target ∈
        StructuralTargetInstantiationPackage W₁ (⇑ᵗᵐ V)
        (name-type-app-frame (applyBody (bind (＇ X)) C)
            Fin.zero refl refl ▻ⁱ
          type-transport-frame (applyBody-open-zero C) ▻ⁱ
          reveal-frame c ▻ⁱ
          reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
          type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
          mapInstantiationSpine (bind (＇ X)) spine) ]
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
structural-target-reveal-peel vV spine target
    with StructuralTargetInstantiationPackage.post-reduction target
structural-target-reveal-peel vV spine target | ↠-refl =
  ⊥-elim
    (no-value-apply-spine spine no-value-type-app
      (StructuralTargetInstantiationPackage.final-value target))
structural-target-reveal-peel vV spine target
    | ↠-step {N = N} {χ = keep} first rest
    with spine-keep-step-inversion spine (β-reveal-∀ vV)
      no-value-type-app first
structural-target-reveal-peel vV spine target
    | ↠-step {N = N} {χ = keep} first rest
    | M₂ , (head-step , eq) =
  ⊥-elim (reveal-head-keep-impossible vV head-step)
structural-target-reveal-peel vV spine target
    | ↠-step {N = N} {χ = bind R} {χs = χs} first rest
    with spine-bind-step-inversion spine no-value-type-app first
structural-target-reveal-peel {B = B} {C = C} {c = c}
    {V = V} {X = X} vV spine target
    | ↠-step {N = N} {χ = bind R} {χs = χs} first rest
    | M₂ , (head-step , eq)
    with reveal-head-bind-view vV head-step
structural-target-reveal-peel {B = B} {C = C} {c = c}
    {V = V} {X = X} vV spine target
    | ↠-step {N = N} {χ = bind .(＇ X)} {χs = χs} first rest
    | .(((⇑ᵗᵐ V ⦂∀ applyBody (bind (＇ X)) C [ ＇ Fin.zero ]) ↑ c)
        ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ,
      (head-step , eq)
    | reveal-bind-target
    with StructuralTargetInstantiationPackage.structural-ext target
structural-target-reveal-peel {B = B} {C = C} {V = V} {X = X}
    vV spine target
    | ↠-step {χ = bind .(＇ X)} {χs = χs} first rest
    | .(((⇑ᵗᵐ V ⦂∀ applyBody (bind (＇ X)) C [ ＇ Fin.zero ]) ↑ _)
        ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ,
      (head-step , eq)
    | reveal-bind-target
    | structural-bind {π = π} {W₁ = W₁} ins follows child-ext =
  _ , π , W₁ , ins , follows , child-target ,
    (λ {γ = γ} child-rel →
      subst≡
        (λ γ′ → _ CTIR.∣ γ′ ⊢² _ ⊑ _ ∶ _)
        (mapCtxᴿ-compose ext₁ (structural-world-extendᴿ child-ext) γ)
        child-rel)
  where
  child-target =
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

  ext₁ = target-insert-bind-world-extendᴿ ins follows
