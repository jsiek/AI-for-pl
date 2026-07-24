module
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  where

-- File Charter:
--   * Defines typed hereditary pending target-cast spines and their term
--     action, used only as private recursion control for administration.
--   * Retains each node's conversion or narrow/widen evidence so inert and
--     sequence plans do not erase the semantic framing justification.
--   * Classifies the four allocation/unseal/eager plans left to the residual
--     branch of the private accessibility-indexed worker.
--   * Applies casts from the head outward, matching the pending-list order
--     used by `targetPendingAdministrationRank`.
--   * Contains no semantic theorem, result/view/outcome type, postulate,
--     hole, permissive option, termination bypass, or compatibility shim.

open import Coercions using
  (Coercion; id-onlyᵈ; _∣_∣_⊢_∶_=⇒_)
open import Conversion using
  (ConcealConversion; RevealConversion)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef
  using
  ( TargetAdministrationPlan
  ; plan-fun-untag-gen
  ; plan-inst
  ; plan-inst-fun-tag
  ; plan-unseal
  )


applyTargetPendingCasts : Term → List Coercion → Term
applyTargetPendingCasts M [] = M
applyTargetPendingCasts M (c ∷ cs) =
  applyTargetPendingCasts (M ⟨ c ⟩) cs


data TargetAdministrationSpine
    {Φ Δᴸ Δᴿ}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (A : Ty) :
    ∀ {B D} →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    (q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ) →
    List Coercion →
    Set where

  pending-empty :
    ∀ {B} {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    TargetAdministrationSpine ρ A p p []

  pending-cons :
    ∀ {μ B C D c cs}
      {c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
    TargetAdministrationPlan ρ A c⊢ p r →
    ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ c B C)
     ⊎
     (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
        ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ c B C)
     ⊎
     (∃[ μ′ ]
        CastMode μ′ ×
        SealModeStore★ μ′ (rightStoreⁱ ρ) ×
        (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊒ C))
     ⊎
     (∃[ μ′ ]
        CastMode μ′ ×
        SealModeStore★ μ′ (rightStoreⁱ ρ) ×
        (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊑ C))
     ⊎
     (SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) ×
      (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
        ⊢ c ∶ B ⊑ C))) →
    TargetAdministrationSpine ρ A r q cs →
    TargetAdministrationSpine ρ A p q (c ∷ cs)


data ResidualTargetAdministrationPlan
    {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {A : Ty} :
    ∀ {μ B C c}
      {c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    TargetAdministrationPlan ρ A c⊢ p q →
    Set where

  residual-unseal :
    ∀ {μ α B hB αB∈Σ ok p q} →
    ResidualTargetAdministrationPlan
      (plan-unseal
        {μ = μ} {α = α} {B = B}
        {hB = hB} {αB∈Σ = αB∈Σ} {ok = ok}
        {p = p} {q = q})

  residual-inst :
    ∀ {μ B C s hB occ s⊢ p q} →
    ResidualTargetAdministrationPlan
      (plan-inst
        {μ = μ} {B = B} {C = C} {s = s}
        {hB = hB} {occ = occ} {s⊢ = s⊢}
        {p = p} {q = q})

  residual-fun-untag-gen :
    ∀ {μ C s hG gG tag-ok hFun occ s⊢ p q} →
    ResidualTargetAdministrationPlan
      (plan-fun-untag-gen
        {μ = μ} {C = C} {s = s}
        {hG = hG} {gG = gG} {tag-ok = tag-ok}
        {hFun = hFun} {occ = occ} {s⊢ = s⊢}
        {p = p} {q = q})

  residual-inst-fun-tag :
    ∀ {μ C s hFun occ s⊢ hG gG tag-ok p q} →
    ResidualTargetAdministrationPlan
      (plan-inst-fun-tag
        {μ = μ} {C = C} {s = s}
        {hFun = hFun} {occ = occ} {s⊢ = s⊢}
        {hG = hG} {gG = gG} {tag-ok = tag-ok}
        {p = p} {q = q})
