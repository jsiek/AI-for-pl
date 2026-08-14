module proof.DGG.Catchup.StructuralTargetAllPeelProof where

-- File Charter:
--   * Peels a completed target package whose first strict head is β-∀.
--   * Extracts the opened-cast child package from the caller's trace.
--   * Uses generic spine one-step inversion for the arbitrary tail spine.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
  renaming (subst to subst≡)

open import Types using (Ty; TyVar; ＇_; _[_]ᵗ)
open import Consistency using (Env∼; extᵐ; _⊢_∼_; ∀ᶜ_; _[_]ᶜ)
import CastTerms as CT
open import CastTerms using (Term; Value; _⟨_⟩; _⦂∀_[_])
open import Reduction using
  (keep; bind; pure-step; β-∀; _—→[_]_; _—↠[_]_;
   ↠-refl; ↠-step; ξ-•)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof
  using (no-value-type-app; no-value-apply-spine; value-no-step)
open import
  proof.DGG.Catchup.StructuralTargetSpineStepInversionProof
    using (spine-step-inversion; spine-bind-step-inversion)


all-head-keep-target : ∀ {Δ} {A B : Ty (suc Δ)}
    {μ : Env∼ Δ} {d : extᵐ μ ⊢ A ∼ B}
    {V N : Term Δ} {X : TyVar Δ}
  → Value V
  → ((V ⟨ ∀ᶜ d ⟩) ⦂∀ B [ ＇ X ]) —→[ keep ] N
  → N ≡ (V ⦂∀ A [ ＇ X ]) ⟨ d [ ＇ X ]ᶜ ⟩
all-head-keep-target vV (pure-step (β-∀ vW refl)) = refl
all-head-keep-target vV (ξ-• step refl refl) =
  ⊥-elim (value-no-step (vV CT.《 CT.all 》) step)


all-head-bind-impossible : ∀ {Δ} {A B : Ty (suc Δ)}
    {μ : Env∼ Δ} {d : extᵐ μ ⊢ A ∼ B}
    {V : Term Δ} {X : TyVar Δ} {R : Ty Δ} {N : Term (suc Δ)}
  → Value V
  → ((V ⟨ ∀ᶜ d ⟩) ⦂∀ B [ ＇ X ]) —→[ bind R ] N
  → ⊥
all-head-bind-impossible vV (ξ-• step refl refl) =
  value-no-step (vV CT.《 CT.all 》) step


structural-target-all-peel : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {μ : Env∼ Δᴿ} {d : extᵐ μ ⊢ A ∼ B}
    {V : Term Δᴿ} {X : TyVar Δᴿ}
    (vV : Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → StructuralTargetInstantiationPackage W (V ⟨ ∀ᶜ d ⟩)
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → StructuralTargetInstantiationPackage W V
      (name-type-app-frame A X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine)
structural-target-all-peel vV spine target
    with StructuralTargetInstantiationPackage.post-reduction target
structural-target-all-peel vV spine target | ↠-refl =
  ⊥-elim
    (no-value-apply-spine spine no-value-type-app
      (StructuralTargetInstantiationPackage.final-value target))
structural-target-all-peel vV spine target
    | ↠-step {N = N} {χ = keep} {χs = χs} first rest
    with StructuralTargetInstantiationPackage.structural-ext target
       | spine-step-inversion spine no-value-type-app first
           (pure-step (β-∀ vV refl))
structural-target-all-peel vV spine target
    | ↠-step {N = N} {χ = keep} {χs = χs} first rest
    | structural-keep child-ext
    | M₂ , (head-step , eq) =
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
          (trans eq
            (cong (λ T →
              applyInstantiationSpine T (mapInstantiationSpine keep spine))
              (all-head-keep-target vV head-step)))
          rest
    }
structural-target-all-peel vV spine target
    | ↠-step {N = N} {χ = bind R} {χs = χs} first rest
    with spine-bind-step-inversion spine no-value-type-app first
structural-target-all-peel vV spine target
    | ↠-step {N = N} {χ = bind R} {χs = χs} first rest
    | M₂ , (head-step , eq) =
  ⊥-elim (all-head-bind-impossible vV head-step)
