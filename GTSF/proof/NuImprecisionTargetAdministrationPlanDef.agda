module proof.NuImprecisionTargetAdministrationPlanDef where

-- File Charter:
--   * Defines cast-local hereditary evidence for target administration.
--   * Records the intermediate precision index at every coercion sequence;
--     `inst` is a boundary where the post-allocation QTI relation supplies a
--     fresh plan.
--   * Contains no simulation result, outcome carrier, implementation,
--     postulate, hole, permissive option, or compatibility wrapper.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using
  ( Inert
  ; cast-id
  ; cast-inst
  ; cast-seq
  ; cast-unseal
  ; cast-untag
  ; instᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  ( StoreImp
  ; rightStoreⁱ
  )
open import Types using
  ( Ty
  ; WfTy
  ; occurs
  ; ★
  ; ＇_
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )


data TargetAdministrationPlan
    {Φ Δᴸ Δᴿ}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (A : Ty) :
    ∀ {μ B C c}
      (c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C)
      (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ)
      (q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ) →
    Set where

  plan-inert :
    ∀ {μ B C c}
      {c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
    Inert c →
    TargetAdministrationPlan ρ A c⊢ p q

  plan-id :
    ∀ {μ B hB ok}
      {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    TargetAdministrationPlan ρ A (cast-id {μ = μ} hB ok) p q

  plan-untag :
    ∀ {μ H hH gH ok}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ} →
    TargetAdministrationPlan ρ A
      (cast-untag {μ = μ} hH gH ok) p q

  plan-unseal :
    ∀ {μ α B hB αB∈Σ ok}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ α ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    TargetAdministrationPlan ρ A
      (cast-unseal {μ = μ} {α = α} hB αB∈Σ ok) p q

  plan-inst :
    ∀ {μ B C s}
      {hB : WfTy Δᴿ B}
      {occ : occurs zero C ≡ true}
      {s⊢ : instᵈ μ ∣ suc Δᴿ
        ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
        ⊢ s ∶ C =⇒ ⇑ᵗ B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    TargetAdministrationPlan ρ A
      (cast-inst {μ = μ} {A = C} hB occ s⊢) p q

  plan-seq :
    ∀ {μ B C D s t}
      {s⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ B =⇒ C}
      {t⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C =⇒ D}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
    TargetAdministrationPlan ρ A s⊢ p r →
    TargetAdministrationPlan ρ A t⊢ r q →
    TargetAdministrationPlan ρ A (cast-seq s⊢ t⊢) p q
