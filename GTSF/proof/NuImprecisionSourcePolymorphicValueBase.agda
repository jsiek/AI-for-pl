module proof.NuImprecisionSourcePolymorphicValueBase where

-- File Charter:
--   * Provides source polymorphic-value base facts for post-allocation
--     runtime-bullet steps and source-side shape inversion.
--   * Exports `post-allocation-β-∀•-bare`,
--     `post-allocation-β-gen•-bare`,
--     `post-allocation-polymorphic-value-step`, and
--     `left-polymorphic-value-shapeᵀ`.
--   * Keeps the remaining beta-step and value-shape helper proofs private.

open import Agda.Builtin.Equality using (refl)
open import Coercions using (gen; `∀)
open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Product using (_,_; ∃-syntax)
open import NuReduction using
  ( keep
  ; pure-step
  ; β-gen•
  ; β-Λ•
  ; β-∀•
  ; _—→[_]_
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  ( Value
  ; Λ_
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( nu-term-imprecision-source-typing
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Relation.Binary.PropositionalEquality using (subst)
open import TermTyping using (_∣_∣_⊢_⦂_; forget)
open import Types using (Store; TyCtx; `∀; extᵗ)
open import proof.CoercionProperties using (open0-ext-suc-cancelᶜ)
open import proof.NuProgress using
  (AllView; av-gen; av-Λ; av-∀; canonical-∀)
open import proof.NuTermProperties using
  ( open0-ext-suc-cancelᵐ
  ; renameᵗᵐ-preserves-Value
  )

private
  post-allocation-β-Λ•-bare :
    ∀ {V} →
    Value V →
    (⇑ᵗᵐ (Λ V)) • —→[ keep ] V
  post-allocation-β-Λ•-bare {V = V} vV =
    subst
      (λ W → (⇑ᵗᵐ (Λ V)) • —→[ keep ] W)
      (open0-ext-suc-cancelᵐ V)
      (pure-step
        (β-Λ• (renameᵗᵐ-preserves-Value (extᵗ suc) vV)))

post-allocation-β-∀•-bare :
  ∀ {V c} →
  Value V →
  (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •
    —→[ keep ] ((⇑ᵗᵐ V) •) ⟨ c ⟩
post-allocation-β-∀•-bare {V = V} {c = c} vV =
  subst
    (λ d → (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •
      —→[ keep ] ((⇑ᵗᵐ V) •) ⟨ d ⟩)
    (open0-ext-suc-cancelᶜ c)
    (pure-step
      (β-∀• (renameᵗᵐ-preserves-Value suc vV)))

post-allocation-β-gen•-bare :
  ∀ {V A c} →
  Value V →
  (⇑ᵗᵐ (V ⟨ gen A c ⟩)) •
    —→[ keep ] (⇑ᵗᵐ V) ⟨ c ⟩
post-allocation-β-gen•-bare {V = V} {c = c} vV =
  subst
    (λ d → (⇑ᵗᵐ (V ⟨ gen _ c ⟩)) •
      —→[ keep ] (⇑ᵗᵐ V) ⟨ d ⟩)
    (open0-ext-suc-cancelᶜ c)
    (pure-step
      (β-gen• (renameᵗᵐ-preserves-Value suc vV)))

private
  Λ-value-body :
    ∀ {V} →
    Value (Λ V) →
    Value V
  Λ-value-body (Λ vV) = vV

post-allocation-polymorphic-value-step :
  ∀ {Δ : TyCtx} {Σ : Store} {L A} →
  Value L →
  Δ ∣ Σ ∣ [] ⊢ L ⦂ `∀ A →
  ∃[ N ] ((⇑ᵗᵐ L) • —→[ keep ] N)
post-allocation-polymorphic-value-step
    {Δ = Δ} {Σ = Σ} {L = L} {A = A} vL L⊢
    with canonical-∀ {Δ = Δ} {Σ = Σ} {V = L} {A = A}
      vL (forget L⊢)
post-allocation-polymorphic-value-step {L = .(Λ V)} vL L⊢
    | av-Λ {W = V} refl =
  V , post-allocation-β-Λ•-bare (Λ-value-body vL)
post-allocation-polymorphic-value-step
    {L = .(V ⟨ `∀ c ⟩)} vL L⊢ | av-∀ {W = V} {c = c} vV refl =
  ((⇑ᵗᵐ V) •) ⟨ c ⟩ , post-allocation-β-∀•-bare vV
post-allocation-polymorphic-value-step
    {L = .(V ⟨ gen A c ⟩)} vL L⊢
    | av-gen {W = V} {A = A} {c = c} vV refl =
  (⇑ᵗᵐ V) ⟨ c ⟩ , post-allocation-β-gen•-bare vV

left-polymorphic-value-shapeᵀ :
  ∀ {Φ Δᴸ Δᴿ L N′ A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ N′ ⦂ `∀ A ⊑ B ∶ p →
  AllView L
left-polymorphic-value-shapeᵀ vL L⊑N′ =
  canonical-∀ vL
    (forget (nu-term-imprecision-source-typing L⊑N′))
