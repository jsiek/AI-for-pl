module
  proof.DGG.Catchup.StructuralTargetFrameDecompositionProof where

-- File Charter:
--   * Inverts completed target packages through non-name instantiation
--     frames.
--   * Value-forming frames reuse the caller trace unchanged.
--   * Reveal/conceal keep-step frames peel the caller's leading keep step
--     and return the tail package with the caller's final endpoint.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types using (Ty)
import CastTerms as CT
open import CastTerms using (Term; Value; _↑_; _↓_)
open import Conversion using (Conv↑; Conv↓)
open import Reduction using
  (keep; bind; _—→[_]_; _—↠[_]_; ↠-refl; ↠-step;
   pure-step; id-reveal; id-conceal; conceal-reveal; blame-reveal;
   blame-conceal; ξ-reveal; ξ-conceal)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision2 as CTIR
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof
  using (no-value-apply-spine; value-no-step; no-value-blame)
open import
  proof.DGG.Catchup.StructuralTargetSpineStepInversionProof
    using (spine-step-inversion; spine-bind-step-inversion)


structural-target-frame-value-peel : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V : Term Δᴿ} {A B E : Ty Δᴿ}
    {frame : InstantiationFrame A B}
    {spine : InstantiationSpine B E}
  → Value (applyInstantiationFrame V frame)
  → StructuralTargetInstantiationPackage W V (frame ▻ⁱ spine)
  → StructuralTargetInstantiationPackage W
      (applyInstantiationFrame V frame) spine
structural-target-frame-value-peel vF target = record
  { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ target
  ; χs = StructuralTargetInstantiationPackage.χs target
  ; Δ′ = StructuralTargetInstantiationPackage.Δ′ target
  ; W′ = StructuralTargetInstantiationPackage.W′ target
  ; structural-ext =
      StructuralTargetInstantiationPackage.structural-ext target
  ; final = StructuralTargetInstantiationPackage.final target
  ; final-value = StructuralTargetInstantiationPackage.final-value target
  ; post-reduction =
      StructuralTargetInstantiationPackage.post-reduction target
  }


reveal-value-bind-impossible : ∀ {Δ A B R}
    {V : Term Δ} {N : Term (suc Δ)}
    {c : Conv↑ Δ A B}
  → Value V
  → (V ↑ c) —→[ bind R ] N
  → ⊥
reveal-value-bind-impossible vV (ξ-reveal step refl) =
  value-no-step vV step


conceal-value-bind-impossible : ∀ {Δ A B R}
    {V : Term Δ} {N : Term (suc Δ)}
    {c : Conv↓ Δ A B}
  → Value V
  → (V ↓ c) —→[ bind R ] N
  → ⊥
conceal-value-bind-impossible vV (ξ-conceal step refl) =
  value-no-step vV step


reveal-value-keep-unique : ∀ {Δ A B}
    {V N N′ : Term Δ} {c : Conv↑ Δ A B}
  → Value V
  → (V ↑ c) —→[ keep ] N
  → (V ↑ c) —→[ keep ] N′
  → N ≡ N′
reveal-value-keep-unique vV (pure-step (id-reveal vW))
    (pure-step (id-reveal vW′)) = refl
reveal-value-keep-unique vV (pure-step (id-reveal vW))
    (ξ-reveal step refl) =
  ⊥-elim (value-no-step vV step)
reveal-value-keep-unique vV (pure-step (conceal-reveal vW))
    (pure-step (conceal-reveal vW′)) = refl
reveal-value-keep-unique vV (pure-step (conceal-reveal vW))
    (ξ-reveal step refl) =
  ⊥-elim (value-no-step vV step)
reveal-value-keep-unique vV (pure-step blame-reveal) step′ =
  ⊥-elim (no-value-blame vV)
reveal-value-keep-unique vV (ξ-reveal step refl) step′ =
  ⊥-elim (value-no-step vV step)


conceal-value-keep-unique : ∀ {Δ A B}
    {V N N′ : Term Δ} {c : Conv↓ Δ A B}
  → Value V
  → (V ↓ c) —→[ keep ] N
  → (V ↓ c) —→[ keep ] N′
  → N ≡ N′
conceal-value-keep-unique vV (pure-step (id-conceal vW))
    (pure-step (id-conceal vW′)) = refl
conceal-value-keep-unique vV (pure-step (id-conceal vW))
    (ξ-conceal step refl) =
  ⊥-elim (value-no-step vV step)
conceal-value-keep-unique vV (pure-step blame-conceal) step′ =
  ⊥-elim (no-value-blame vV)
conceal-value-keep-unique vV (ξ-conceal step refl) step′ =
  ⊥-elim (value-no-step vV step)


structural-target-reveal-frame-keep-peel : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V V₁ : Term Δᴿ} {A B E : Ty Δᴿ}
    {c : Conv↑ Δᴿ A B}
    (vV : Value V)
    (spine : InstantiationSpine B E)
  → (head : (V ↑ c) —→[ keep ] V₁)
  → Value V₁
  → (target : StructuralTargetInstantiationPackage W V
      (reveal-frame c ▻ⁱ spine)
    )
  → Σ[ child-target ∈
      StructuralTargetInstantiationPackage W V₁
        (mapInstantiationSpine keep spine) ]
      (∀ {γ : CTI2.CtxImp W} {M : Term Δᴸ}
         {L : Ty Δᴸ} {q : L CTI2.⊑ᵂ⟨ W ⟩ E}
       → StructuralTargetInstantiationPackage.W′ child-target CTIR.∣
           ECR.mapCtxᴿ
             (structural-world-extendᴿ
               (StructuralTargetInstantiationPackage.structural-ext
                 child-target))
             γ
           ⊢² M ⊑ StructuralTargetInstantiationPackage.final child-target
             ∶ ECR.transport⊑ᵂ
               (structural-world-extendᴿ
                 (StructuralTargetInstantiationPackage.structural-ext
                   child-target))
               q
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
structural-target-reveal-frame-keep-peel vV spine head vV₁ target
    with StructuralTargetInstantiationPackage.post-reduction target
structural-target-reveal-frame-keep-peel vV spine head vV₁ target
    | ↠-refl =
  ⊥-elim
    (no-value-apply-spine spine
      (λ vF → value-no-step vF head)
      (StructuralTargetInstantiationPackage.final-value target))
structural-target-reveal-frame-keep-peel vV spine head vV₁ target
    | ↠-step {N = N} {χ = keep} {χs = χs} first rest
    with StructuralTargetInstantiationPackage.structural-ext target
       | spine-step-inversion spine
           (λ vF → value-no-step vF head) first head
structural-target-reveal-frame-keep-peel vV spine head vV₁ target
    | ↠-step {N = N} {χ = keep} {χs = χs} first rest
    | structural-keep child-ext
    | V₂ , (head′ , eq) =
  child-target ,
    (λ {γ = γ} child-rel →
      subst≡
        (λ γ′ → _ CTIR.∣ γ′ ⊢² _ ⊑ _ ∶ _)
        (sym (mapCtxᴿ-structural-keep child-ext γ))
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
          (trans eq
            (cong (λ T →
              applyInstantiationSpine T
                (mapInstantiationSpine keep spine))
              (reveal-value-keep-unique vV head′ head)))
          rest
    }
structural-target-reveal-frame-keep-peel vV spine head vV₁ target
    | ↠-step {χ = bind R} first rest
    with spine-bind-step-inversion spine
      (λ vF → value-no-step vF head) first
structural-target-reveal-frame-keep-peel vV spine head vV₁ target
    | ↠-step {χ = bind R} first rest
    | V₂ , (head′ , eq) =
  ⊥-elim (reveal-value-bind-impossible vV head′)


structural-target-conceal-frame-keep-peel : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {V V₁ : Term Δᴿ} {A B E : Ty Δᴿ}
    {c : Conv↓ Δᴿ A B}
    (vV : Value V)
    (spine : InstantiationSpine B E)
  → (head : (V ↓ c) —→[ keep ] V₁)
  → Value V₁
  → (target : StructuralTargetInstantiationPackage W V
      (conceal-frame c ▻ⁱ spine)
    )
  → Σ[ child-target ∈
      StructuralTargetInstantiationPackage W V₁
        (mapInstantiationSpine keep spine) ]
      (∀ {γ : CTI2.CtxImp W} {M : Term Δᴸ}
         {L : Ty Δᴸ} {q : L CTI2.⊑ᵂ⟨ W ⟩ E}
       → StructuralTargetInstantiationPackage.W′ child-target CTIR.∣
           ECR.mapCtxᴿ
             (structural-world-extendᴿ
               (StructuralTargetInstantiationPackage.structural-ext
                 child-target))
             γ
           ⊢² M ⊑ StructuralTargetInstantiationPackage.final child-target
             ∶ ECR.transport⊑ᵂ
               (structural-world-extendᴿ
                 (StructuralTargetInstantiationPackage.structural-ext
                   child-target))
               q
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
structural-target-conceal-frame-keep-peel vV spine head vV₁ target
    with StructuralTargetInstantiationPackage.post-reduction target
structural-target-conceal-frame-keep-peel vV spine head vV₁ target
    | ↠-refl =
  ⊥-elim
    (no-value-apply-spine spine
      (λ vF → value-no-step vF head)
      (StructuralTargetInstantiationPackage.final-value target))
structural-target-conceal-frame-keep-peel vV spine head vV₁ target
    | ↠-step {N = N} {χ = keep} {χs = χs} first rest
    with StructuralTargetInstantiationPackage.structural-ext target
       | spine-step-inversion spine
           (λ vF → value-no-step vF head) first head
structural-target-conceal-frame-keep-peel vV spine head vV₁ target
    | ↠-step {N = N} {χ = keep} {χs = χs} first rest
    | structural-keep child-ext
    | V₂ , (head′ , eq) =
  child-target ,
    (λ {γ = γ} child-rel →
      subst≡
        (λ γ′ → _ CTIR.∣ γ′ ⊢² _ ⊑ _ ∶ _)
        (sym (mapCtxᴿ-structural-keep child-ext γ))
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
          (trans eq
            (cong (λ T →
              applyInstantiationSpine T
                (mapInstantiationSpine keep spine))
              (conceal-value-keep-unique vV head′ head)))
          rest
    }
structural-target-conceal-frame-keep-peel vV spine head vV₁ target
    | ↠-step {χ = bind R} first rest
    with spine-bind-step-inversion spine
      (λ vF → value-no-step vF head) first
structural-target-conceal-frame-keep-peel vV spine head vV₁ target
    | ↠-step {χ = bind R} first rest
    | V₂ , (head′ , eq) =
  ⊥-elim (conceal-value-bind-impossible vV head′)
