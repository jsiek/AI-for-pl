module proof.DGG.Catchup.StructuralTargetInstPeelProof where

-- File Charter:
--   * Peels a completed target package whose first non-name head is β-inst.
--   * Returns the caller's inserted target world and the strictly smaller
--     structural child package.
--   * This is proof support for the cast-frame safe-inst branch of the
--     structural value-spine worker.

import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
  renaming (subst to subst≡)

open import Types using (Ty; TyCtx; NonVar; _∈ᵗ_; ＇_; ★; _[_]ᵗ; ⇑ᵗ)
open import Consistency using
  (_↪ᵗ_; wk↪ᵗ; Env∼; _⊢_∼_; instᵐ; inst_; ↑ᶜ_; close-instᶜ)
import CastTerms as CT
open import CastTerms using (Term; Value; _⟨_⟩; _⦂∀_[_]; _↑_; ⇑ᵗᵐ)
open import Conversion using (〖_,_↑_〗)
open import Reduction using
  (bind; keep; applyBody; applyStores; _∷_; []; β-inst; ξ-⟨⟩;
   pure-step; blame-⟨⟩; _—→[_]_; _—↠[_]_; ↠-refl; ↠-step)
open import proof.TypeInTermSubst using (renameᵗ-wk-eq)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof
  using (no-value-apply-spine; value-no-step; no-value-blame)
open import
  proof.DGG.Catchup.StructuralTargetSpineStepInversionProof
    using (spine-bind-step-inversion; spine-keep-step-inversion)


no-value-inst-cast : ∀ {Δ} {A : Ty (suc Δ)} {B : Ty Δ}
    {μ : Env∼ Δ} {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
    {V : Term Δ} {B≢★ : B ≢ ★}
  → Value (V ⟨ (inst c) B≢★ ⟩)
  → ⊥
no-value-inst-cast (vV CT.《 () 》)


inst-head-keep-impossible : ∀ {Δ} {A : Ty (suc Δ)}
    {B : Ty Δ} {μ : Env∼ Δ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
    {V N : Term Δ} {B≢★ : B ≢ ★}
  → Value V
  → (V ⟨ (inst c) B≢★ ⟩) —→[ keep ] N
  → ⊥
inst-head-keep-impossible vV (pure-step blame-⟨⟩) =
  no-value-blame vV
inst-head-keep-impossible vV (ξ-⟨⟩ step refl) =
  value-no-step vV step


data InstHeadBindView {Δ} {A : Ty (suc Δ)}
    {B : Ty Δ} {μ : Env∼ Δ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
    {V : Term Δ} {B≢★ : B ≢ ★}
    : {R : Ty Δ} → Term (suc Δ) → Set where

  inst-bind-target :
    InstHeadBindView {c = c} {V = V} {B≢★ = B≢★} {R = ★}
      ((⇑ᵗᵐ V ⦂∀ applyBody (bind ★) A [ ＇ Fin.zero ])
        ↑ 〖 Fin.zero , ★ ↑ A 〗
        ⟨ ↑ᶜ (close-instᶜ c) ⟩)


inst-head-bind-view : ∀ {Δ} {A : Ty (suc Δ)}
    {B : Ty Δ} {μ : Env∼ Δ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
    {V : Term Δ} {R : Ty Δ} {N : Term (suc Δ)}
    {B≢★ : B ≢ ★}
  → Value V
  → (V ⟨ (inst c) B≢★ ⟩) —→[ bind R ] N
  → InstHeadBindView {c = c} {V = V} {B≢★ = B≢★} {R = R} N
inst-head-bind-view vV (β-inst vW B≢★) = inst-bind-target
inst-head-bind-view vV (ξ-⟨⟩ step refl) =
  ⊥-elim (value-no-step vV step)


structural-target-inst-peel : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴿ)} {B E : Ty Δᴿ}
    {μ : Env∼ Δᴿ} {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
    {V : Term Δᴿ}
    (vV : Value V)
    (B≢★ : B ≢ ★)
    (spine : InstantiationSpine B E)
  → StructuralTargetInstantiationPackage W V
      (cast-frame ((inst c) B≢★) ▻ⁱ spine)
  → Σ[ Δ₁ ∈ TyCtx ]
    Σ[ π ∈ Δ ↪ᵗ Δ₁ ]
    Σ[ W₁ ∈ CTI2.World Δᴸ (suc Δᴿ) Δ₁ ]
    Σ[ ins ∈ TE.TargetInsert wk↪ᵗ π W W₁ ]
    Σ[ follows ∈
      CTI2.targetStoreʷ W₁ ≡
        applyStores (bind ★ ∷ []) (CTI2.targetStoreʷ W) ]
      StructuralTargetInstantiationPackage W₁ (⇑ᵗᵐ V)
        (name-type-app-frame (applyBody (bind ★) A) Fin.zero
            refl refl ▻ⁱ
          type-transport-frame (applyBody-open-zero A) ▻ⁱ
          reveal-frame (〖 Fin.zero , ★ ↑ A 〗) ▻ⁱ
          type-transport-frame
            (trans (replace-zero-open A ★)
              (sym (renameᵗ-wk-eq (A [ ★ ]ᵗ)))) ▻ⁱ
          cast-frame (↑ᶜ (close-instᶜ c)) ▻ⁱ
          type-transport-frame (renameᵗ-wk-eq B) ▻ⁱ
          mapInstantiationSpine (bind ★) spine)
structural-target-inst-peel vV B≢★ spine target
    with StructuralTargetInstantiationPackage.post-reduction target
structural-target-inst-peel vV B≢★ spine target | ↠-refl =
  ⊥-elim
    (no-value-apply-spine spine no-value-inst-cast
      (StructuralTargetInstantiationPackage.final-value target))
structural-target-inst-peel vV B≢★ spine target
    | ↠-step {N = N} {χ = keep} first rest
    with spine-keep-step-inversion spine (β-inst vV B≢★)
      no-value-inst-cast first
structural-target-inst-peel vV B≢★ spine target
    | ↠-step {N = N} {χ = keep} first rest
    | M₂ , (head-step , eq) =
  ⊥-elim (inst-head-keep-impossible vV head-step)
structural-target-inst-peel vV B≢★ spine target
    | ↠-step {N = N} {χ = bind R} {χs = χs} first rest
    with spine-bind-step-inversion spine no-value-inst-cast first
structural-target-inst-peel {A = A} {B = B} {c = c} {V = V}
    vV B≢★ spine target
    | ↠-step {N = N} {χ = bind R} {χs = χs} first rest
    | M₂ , (head-step , eq)
    with inst-head-bind-view vV head-step
structural-target-inst-peel {A = A} {B = B} {V = V}
    vV B≢★ spine target
    | ↠-step {N = N} {χ = bind .★} {χs = χs} first rest
    | .(((⇑ᵗᵐ V ⦂∀ applyBody (bind ★) A [ ＇ Fin.zero ])
        ↑ 〖 Fin.zero , ★ ↑ A 〗) ⟨ _ ⟩) ,
      (head-step , eq)
    | inst-bind-target
    with StructuralTargetInstantiationPackage.structural-ext target
structural-target-inst-peel {A = A} {B = B} {V = V}
    vV B≢★ spine target
    | ↠-step {χ = bind .★} {χs = χs} first rest
    | .(((⇑ᵗᵐ V ⦂∀ applyBody (bind ★) A [ ＇ Fin.zero ])
        ↑ 〖 Fin.zero , ★ ↑ A 〗) ⟨ _ ⟩) ,
      (head-step , eq)
    | inst-bind-target
    | structural-bind {π = π} {W₁ = W₁} ins follows child-ext =
  _ , π , W₁ , ins , follows ,
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
