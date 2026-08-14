module
  proof.DGG.Catchup.StructuralTargetSpineStepInversionProof where

-- File Charter:
--   * Inverts one store-changing step through a pending instantiation spine.
--   * If the spine head is known to have a strict step and is not a value,
--     any caller first step is the lift of some head step.
--   * This is proof support only; it does not change the reduction relation.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Types using (Ty)
import CastTerms as CT
open import CastTerms using
  (Term; Value; Λ_; blame; _《_》; _↑_; _↓_)
open import Reduction using
  (StoreChange; keep; bind; _—→[_]_; pure-step; β-id; β-∀; ground;
   expand; tag-untag; tag-untag-bad; blame-bot-intro; id-reveal;
   id-conceal; conceal-reveal; blame-•; blame-⟨⟩; blame-reveal;
   blame-conceal; β-Λ; β-inst; β-gen; β-reveal-∀; β-conceal-∀;
   ξ-•; ξ-⟨⟩; ξ-reveal; ξ-conceal)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof
    using
      (renamed↑-to-normalized-term; renamed↓-to-normalized-term;
       lift-instantiation-frame-keep; lift-instantiation-frame-bind)
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof
  using (no-value-type-app)


no-value-frame : ∀ {Δ} {M : Term Δ} {A B : Ty Δ}
  → (frame : InstantiationFrame A B)
  → (Value M → ⊥)
  → Value (applyInstantiationFrame M frame)
  → ⊥
no-value-frame (type-transport-frame eq) noM vM = noM vM
no-value-frame (name-type-app-frame B X eqA eqC) noM v =
  no-value-type-app v
no-value-frame (cast-frame c) noM (vM 《 inert 》) = noM vM
no-value-frame (reveal-frame c) noM (vM ↑ rv) = noM vM
no-value-frame (conceal-frame c) noM (vM ↓ cv) = noM vM


no-step-blame : ∀ {Δ Δ′} {N : Term Δ′} {χ : StoreChange Δ Δ′}
  → blame {Δ = Δ} —→[ χ ] N
  → ⊥
no-step-blame {χ = keep} (pure-step ())
no-step-blame {χ = bind R} ()


frame-step-inversion : ∀ {Δ Δ′ A B}
    {M : Term Δ} {M₁ N : Term Δ′}
    {χ : StoreChange Δ Δ′}
  → (frame : InstantiationFrame A B)
  → (Value M → ⊥)
  → applyInstantiationFrame M frame —→[ χ ] N
  → M —→[ χ ] M₁
  → Σ[ M₂ ∈ Term Δ′ ]
      ((M —→[ χ ] M₂)
      × (N ≡ applyInstantiationFrame M₂ (mapInstantiationFrame χ frame)))
frame-step-inversion (type-transport-frame eq) noM step head =
  _ , step , refl
frame-step-inversion (name-type-app-frame B X eqA eqC) noM
    (pure-step (β-∀ vM refl)) head =
  ⊥-elim (noM (vM CT.《 CT.all 》))
frame-step-inversion (name-type-app-frame B X eqA eqC) noM
    (pure-step blame-•) head =
  ⊥-elim (no-step-blame head)
frame-step-inversion (name-type-app-frame B X eqA eqC) noM
    (β-Λ vM) head =
  ⊥-elim (noM (Λ vM))
frame-step-inversion (name-type-app-frame B X eqA eqC) noM
    (β-gen vM A≢★ safe) head =
  ⊥-elim (noM (vM CT.《 CT.genᵥ A≢★ safe 》))
frame-step-inversion (name-type-app-frame B X eqA eqC) noM
    (β-reveal-∀ vM) head =
  ⊥-elim (noM (vM CT.↑ CT.all))
frame-step-inversion (name-type-app-frame B X eqA eqC) noM
    (β-conceal-∀ vM) head =
  ⊥-elim (noM (vM CT.↓ CT.all))
frame-step-inversion {χ = keep}
    (name-type-app-frame B X eqA eqC) noM
    (ξ-• step refl refl) head =
  _ , step , refl
frame-step-inversion {χ = bind R}
    (name-type-app-frame B X eqA eqC) noM
    (ξ-• step refl refl) head =
  _ , step , refl
frame-step-inversion (cast-frame c) noM
    (pure-step (β-id vM)) head =
  ⊥-elim (noM vM)
frame-step-inversion (cast-frame c) noM
    (pure-step (ground vM A≢G)) head =
  ⊥-elim (noM vM)
frame-step-inversion (cast-frame c) noM
    (pure-step (expand vM G≢B)) head =
  ⊥-elim (noM vM)
frame-step-inversion (cast-frame c) noM
    (pure-step (tag-untag vM)) head =
  ⊥-elim (noM (vM CT.《 CT.inj 》))
frame-step-inversion (cast-frame c) noM
    (pure-step (tag-untag-bad vM G≢H)) head =
  ⊥-elim (noM (vM CT.《 CT.inj 》))
frame-step-inversion (cast-frame c) noM
    (pure-step (blame-bot-intro vM)) head =
  ⊥-elim (noM vM)
frame-step-inversion (cast-frame c) noM
    (pure-step blame-⟨⟩) head =
  ⊥-elim (no-step-blame head)
frame-step-inversion (cast-frame c) noM
    (β-inst vM B≢★) head =
  ⊥-elim (noM vM)
frame-step-inversion {χ = keep} (cast-frame c) noM
    (ξ-⟨⟩ step refl) head =
  _ , step , refl
frame-step-inversion {χ = bind R} (cast-frame c) noM
    (ξ-⟨⟩ step refl) head =
  _ , step , refl
frame-step-inversion {χ = keep} (reveal-frame c) noM
    (ξ-reveal step refl) head =
  _ , step , renamed↑-to-normalized-term _ c
frame-step-inversion {χ = bind R} (reveal-frame c) noM
    (ξ-reveal step refl) head =
  _ , step , refl
frame-step-inversion (reveal-frame c) noM
    (pure-step (id-reveal vM)) head =
  ⊥-elim (noM vM)
frame-step-inversion (reveal-frame c) noM
    (pure-step (conceal-reveal vM)) head =
  ⊥-elim (noM (vM CT.↓ CT.seal))
frame-step-inversion (reveal-frame c) noM
    (pure-step blame-reveal) head =
  ⊥-elim (no-step-blame head)
frame-step-inversion {χ = keep} (conceal-frame c) noM
    (ξ-conceal step refl) head =
  _ , step , renamed↓-to-normalized-term _ c
frame-step-inversion {χ = bind R} (conceal-frame c) noM
    (ξ-conceal step refl) head =
  _ , step , refl
frame-step-inversion (conceal-frame c) noM
    (pure-step (id-conceal vM)) head =
  ⊥-elim (noM vM)
frame-step-inversion (conceal-frame c) noM
    (pure-step blame-conceal) head =
  ⊥-elim (no-step-blame head)


spine-step-inversion : ∀ {Δ Δ′ A B}
    {M : Term Δ} {M₁ N : Term Δ′}
    {χ : StoreChange Δ Δ′}
  → (spine : InstantiationSpine A B)
  → (Value M → ⊥)
  → applyInstantiationSpine M spine —→[ χ ] N
  → M —→[ χ ] M₁
  → Σ[ M₂ ∈ Term Δ′ ]
      ((M —→[ χ ] M₂)
      × (N ≡ applyInstantiationSpine M₂ (mapInstantiationSpine χ spine)))
spine-step-inversion []ⁱ noM step head =
  _ , step , refl
spine-step-inversion (frame ▻ⁱ spine) noM step head
    with spine-step-inversion spine
      (no-value-frame frame noM)
      step
      (lift-instantiation-frame head frame)
  where
  lift-instantiation-frame : ∀ {Δ Δ′ A B}
      {M : Term Δ} {M₁ : Term Δ′} {χ : StoreChange Δ Δ′}
    → M —→[ χ ] M₁
    → (frame : InstantiationFrame A B)
    → applyInstantiationFrame M frame —→[ χ ]
        applyInstantiationFrame M₁ (mapInstantiationFrame χ frame)
  lift-instantiation-frame {χ = keep} step frame =
    lift-instantiation-frame-keep step frame
  lift-instantiation-frame {χ = bind R} step frame =
    lift-instantiation-frame-bind step frame
spine-step-inversion (frame ▻ⁱ spine) noM step head
    | F₁ , frame-step , eq-tail
    with frame-step-inversion frame noM frame-step head
spine-step-inversion (frame ▻ⁱ spine) noM step head
    | F₁ , frame-step , eq-tail
    | M₂ , head-step , eq-frame =
  M₂ , head-step ,
    trans eq-tail
      (cong (λ N → applyInstantiationSpine N
        (mapInstantiationSpine _ spine)) eq-frame)
