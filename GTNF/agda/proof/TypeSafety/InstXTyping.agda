module proof.TypeSafety.InstXTyping where

-- File Charter:
--   * Types `InstX` at the represented binder introduced by `TyBeta`.
--   * The proof follows the four layers of a canonical polymorphic value.

open import Data.Nat using (zero; suc)
open import Data.List using ([]; _∷_; length)
open import Data.List.Properties using (length-map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import Types
open import Ctx
open import proof.Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import Reduction
open import proof.TypeSafety.PreservationSupport
open import proof.TypeSafety.RepWeaken using (cross-Λ-⊢)
open import proof.TypeSafety.CoercionTyping using (coercion-src)

private
  variable
    Δ Δᵢ Δᶜ : Ctxᵗ
    V N : Term
    C R : Ty

represented-wfᴿ : WfCtx Δ → reps Δ ⊢ᴿ R → WfCtx (reprCtx R Δ)
represented-wfᴿ {Δ = Δ} {R = R} w wR =
  wf-ctx (wf-bindR wR (wf-reps w)) valid
         (unique-underΛ {Γ = Δ} (name-fn w))
  where
  valid : ValidNames (bindR R ∷ reps Δ)
                     (zero ∷ shiftReps (names Δ))
  valid here = bindR R , here
  valid (there d) with shiftReps-∋⁻ d
  valid (there d) | α , refl , d′ with wf-names w d′
  valid (there d) | α , refl , d′ | b , db = b , there db

instX-⊢ : WfCtx Δ
  → reps Δ ⊢ᴿ R
  → InstX V N
  → Δ ∣ [] ⊢ V ⦂ `∀ C
  → reprCtx R Δ ∣ [] ⊢ N ⦂ C
instX-⊢ wfΔ wR (inst-Λ vN) (⊢Λ vN′ ⊢N) =
  ⊢refine (rr-represent rr-refl) (represented-wfᴿ wfΔ wR) ⊢N
instX-⊢ {Δ = Δ} wfΔ wR (inst-gen vW)
    (⊢cast W⊢ (⊢gen {A = A} ⊢p wA nv occ ns safe) len)
    with coercion-src (⊢gen ⊢p wA nv occ ns safe)
instX-⊢ {Δ = Δ} wfΔ wR (inst-gen vW)
    (⊢cast W⊢ (⊢gen {A = A} ⊢p wA nv occ ns safe) len) | refl =
  ⊢cast crossed (coercion-refine (rr-represent rr-refl) ⊢p)
        (trans (cong suc len)
               (cong suc (sym (length-map suc (names Δ)))))
  where
  crossed = ⊢refine (rr-represent rr-refl) (represented-wfᴿ wfΔ wR)
                    (cross-Λ-⊢ wfΔ wA W⊢)
instX-⊢ {Δ = Δ} wfΔ wR (inst-∀ _ inst)
    (⊢cast W⊢ (⊢all ⊢p) len) =
  ⊢cast (instX-⊢ wfΔ wR inst W⊢)
        (coercion-refine (rr-represent rr-refl) ⊢p)
        (trans (cong suc len)
               (cong suc (sym (length-map suc (names Δ)))))
instX-⊢ {Δ = Δ} {R = R} wfΔ wR (inst-⟪⟫ _ inst)
    (boundary {Δᵢ = Δᵢ} mwΘ U⊢ ⊢allc sameᵢ sameₑ wE)
    with conv-all-inv ⊢allc
instX-⊢ {Δ = Δ} {R = R} wfΔ wR (inst-⟪⟫ _ inst)
    (boundary {Δᵢ = Δᵢ} mwΘ U⊢ ⊢allc sameᵢ sameₑ wE)
    | A₀ , B₀ , refl , refl , ⊢s
    with sameTy-target-∀⁻ sameᵢ
instX-⊢ {Δ = Δ} {R = R} wfΔ wR (inst-⟪⟫ _ inst)
    (boundary {Δᵢ = Δᵢ} mwΘ U⊢ ⊢allc sameᵢ sameₑ wE)
    | A₀ , B₀ , refl , refl , ⊢s | C₀ , refl , sameᵢ′ =
  boundary mw₁ inner
      (conv-refine (rr-represent rr-refl) ⊢s)
      sameᵢ′ (sameTy-∀⁻ sameₑ)
      (wf-refine (rr-represent rr-refl) (wf-∀⁻ wE))
  where
  wRᵢ : reps Δᵢ ⊢ᴿ R
  wRᵢ = subst (λ Ξ → Ξ ⊢ᴿ R) (sym (interior-reps (bw-interior mwΘ))) wR

  mw₁ = bw (represented-wfᴿ wfΔ wR)
           (liftᴮ-interior (bw-interior mwΘ))
           (liftᴮ-conversion (bw-conversion mwΘ))

  inner = instX-⊢ (bw-interior-wf mwΘ) wRᵢ inst U⊢
