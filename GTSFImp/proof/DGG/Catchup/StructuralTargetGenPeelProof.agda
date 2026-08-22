module proof.DGG.Catchup.StructuralTargetGenPeelProof where

-- File Charter:
--   * Peels a completed target package whose first strict head is β-gen.
--   * Returns the caller's inserted target world and the smaller child
--     package beneath the generated cast/reveal/transport frames.
--   * This is proof support for strict structural name-instantiation cases.

import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyCtx; TyVar; NonVar; _∈ᵗ_; ＇_; ★; _[_]ᵗ; ⇑ᵗ)
open import Consistency using (Env∼; _↪ᵗ_; wk↪ᵗ; _⊢_∼_; genᵐ; gen_)
import CastTerms as CT
open import CastTerms using
  (Term; Value; GenSafe; _⟨_⟩; _⦂∀_[_]; _↑_; ⇑ᵗᵐ)
open import Conversion using (〖_,_↑_〗)
open import Reduction using
  (bind; keep; applyStores; _∷_; []; β-gen; ξ-•; _—→[_]_;
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
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof
  using (no-value-type-app; no-value-apply-spine; value-no-step)
open import
  proof.DGG.Catchup.StructuralTargetSpineStepInversionProof
    using (spine-bind-step-inversion; spine-keep-step-inversion)


gen-head-keep-impossible : ∀ {Δ} {A : Ty Δ} {B : Ty (suc Δ)}
    {μ : Env∼ Δ} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    {V : Term Δ} {X : TyVar Δ} {N : Term Δ}
  → Value V
  → (A≠★ : A ≢ ★)
  → GenSafe c
  → ((V ⟨ (gen c) A≠★ ⟩) ⦂∀ B [ ＇ X ]) —→[ keep ] N
  → ⊥
gen-head-keep-impossible vV A≠★ safe (ξ-• step refl refl) =
  value-no-step (vV CT.《 CT.genᵥ A≠★ safe 》) step


data GenHeadBindView {Δ} {A : Ty Δ} {B : Ty (suc Δ)}
    {μ : Env∼ Δ} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    {V : Term Δ} {X : TyVar Δ}
    : {R : Ty Δ} → Term (suc Δ) → Set where

  gen-bind-target :
    GenHeadBindView {c = c} {V = V} {X = X} {R = ＇ X}
      ((⇑ᵗᵐ V ⟨ c ⟩) ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)


gen-head-bind-view : ∀ {Δ} {A : Ty Δ} {B : Ty (suc Δ)}
    {μ : Env∼ Δ} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    {V : Term Δ} {X : TyVar Δ} {R : Ty Δ}
    {N : Term (suc Δ)}
  → Value V
  → (A≠★ : A ≢ ★)
  → (safe : GenSafe c)
  → ((V ⟨ (gen c) A≠★ ⟩) ⦂∀ B [ ＇ X ]) —→[ bind R ] N
  → GenHeadBindView {c = c} {V = V} {X = X} {R = R} N
gen-head-bind-view vV A≠★ safe (β-gen vW A≢★′ safe′) =
  gen-bind-target
gen-head-bind-view vV A≠★ safe (ξ-• step refl refl) =
  ⊥-elim (value-no-step (vV CT.《 CT.genᵥ A≠★ safe 》) step)


structural-target-gen-peel : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴿ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {μ : Env∼ Δᴿ} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    {V : Term Δᴿ} {X : TyVar Δᴿ}
    (vV : Value V)
    (A≠★ : A ≢ ★)
    (safe : GenSafe c)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (target : StructuralTargetInstantiationPackage W
      (V ⟨ (gen c) A≠★ ⟩)
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
        (cast-frame c ▻ⁱ
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
structural-target-gen-peel vV A≠★ safe spine target
    with StructuralTargetInstantiationPackage.post-reduction target
structural-target-gen-peel vV A≠★ safe spine target | ↠-refl =
  ⊥-elim
    (no-value-apply-spine spine no-value-type-app
      (StructuralTargetInstantiationPackage.final-value target))
structural-target-gen-peel vV A≠★ safe spine target
    | ↠-step {N = N} {χ = keep} first rest
    with spine-keep-step-inversion spine (β-gen vV A≠★ safe)
      no-value-type-app first
structural-target-gen-peel vV A≠★ safe spine target
    | ↠-step {N = N} {χ = keep} first rest
    | M₂ , (head-step , eq) =
  ⊥-elim (gen-head-keep-impossible vV A≠★ safe head-step)
structural-target-gen-peel vV A≠★ safe spine target
    | ↠-step {N = N} {χ = bind R} {χs = χs} first rest
    with spine-bind-step-inversion spine no-value-type-app first
structural-target-gen-peel {B = B} {c = c} {V = V} {X = X}
    vV A≠★ safe spine target
    | ↠-step {N = N} {χ = bind R} {χs = χs} first rest
    | M₂ , (head-step , eq)
    with gen-head-bind-view vV A≠★ safe head-step
structural-target-gen-peel {B = B} {c = c} {V = V} {X = X}
    vV A≠★ safe spine target
    | ↠-step {N = N} {χ = bind .(＇ X)} {χs = χs} first rest
    | .((⇑ᵗᵐ V ⟨ c ⟩) ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ,
      (head-step , eq)
    | gen-bind-target
    with StructuralTargetInstantiationPackage.structural-ext target
structural-target-gen-peel {B = B} {V = V} {X = X}
    vV A≠★ safe spine target
    | ↠-step {χ = bind .(＇ X)} {χs = χs} first rest
    | .((⇑ᵗᵐ V ⟨ _ ⟩) ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ,
      (head-step , eq)
    | gen-bind-target
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
