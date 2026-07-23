module proof.Source.NuPaired.NuImprecisionSourceNuPairedBinderSupport where

-- File Charter:
--   * Owns focused source-`ν`/`∀` paired-binder lifting support extracted from
--     `NuImprecisionSimulationCore`.
--   * Constructs term-context lift witnesses and the source-left/forall store
--     and context commuting squares.
--   * Exports `left-source-lift-Λᵀ`, the focused term-imprecision lift for
--     source-`ν` paired binder support.
--   * Depends only on syntax, store/context imprecision, type-imprecision
--     lifting, store-lift construction, and quotiented term imprecision.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Types using (extᵗ; renameᵗ; ⇑ᵗ; ⟰ᵗ; `∀)
open import Ctx using (⤊ᵗ)
open import ImprecisionWf using (ImpCtx; _ˣ⊑★; ⇑ᴸᵢ; ∀ⁱ_)
open import NuTerms using (Value; Λ_; renameᵗᵐ; ⇑ᵗᵐ)
open import NuTermImprecision using
  ( StoreImp
  ; CtxImp
  ; ctx-imp
  ; LiftStoreⁱ
  ; LiftLeftStoreⁱ
  ; LiftCtxⁱ
  ; lift-ctx-[]
  ; lift-ctx-∷
  ; LiftLeftCtxⁱ
  ; lift-left-ctx-[]
  ; lift-left-ctx-∷
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; leftStoreⁱ-lift
  ; rightStoreⁱ-lift
  ; leftStoreⁱ-lift-left
  ; rightStoreⁱ-lift-left
  ; leftCtxⁱ
  ; rightCtxⁱ
  ; leftCtxⁱ-lift
  ; rightCtxⁱ-lift
  ; leftCtxⁱ-lift-left
  ; rightCtxⁱ-lift-left
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_; Λ⊑Λᵀ)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ; ⊑-source-liftνᵢ)
open import proof.Store.Core.NuImprecisionStoreLift using
  (lift-store-result; lift-left-store-result)
open import proof.Core.Properties.NuTermProperties using (renameᵗᵐ-preserves-Value)


lift-ctx-result :
  ∀ {Φ Δᴸ Δᴿ} (γ : CtxImp Φ Δᴸ Δᴿ) →
  ∃[ γ′ ] LiftCtxⁱ (∀ᵢᶜ Φ) γ γ′
lift-ctx-result [] = [] , lift-ctx-[]
lift-ctx-result (ctx-imp A B p ∷ γ) with lift-ctx-result γ
lift-ctx-result (ctx-imp A B p ∷ γ) | γ′ , liftγ =
  ctx-imp (⇑ᵗ A) (⇑ᵗ B) (⊑-lift∀ᵢ p) ∷ γ′ ,
  lift-ctx-∷ liftγ

lift-left-ctx-result :
  ∀ {Φ Δᴸ Δᴿ} (γ : CtxImp Φ Δᴸ Δᴿ) →
  ∃[ γ′ ] LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
lift-left-ctx-result [] = [] , lift-left-ctx-[]
lift-left-ctx-result (ctx-imp A B p ∷ γ)
    with lift-left-ctx-result γ
lift-left-ctx-result (ctx-imp A B p ∷ γ) | γ′ , liftγ =
  ctx-imp (⇑ᵗ A) B (⊑-source-liftνᵢ p) ∷ γ′ ,
  lift-left-ctx-∷ liftγ

left-forall-store-square :
  ∀ {Φ Δᴸ Δᴿ} (ρ : StoreImp Φ Δᴸ Δᴿ) →
  ∃[ ρν ] ∃[ ρ∀ ] ∃[ ρν∀ ] ∃[ ρ∀ν ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν ×
    LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ∀ ×
    LiftStoreⁱ (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) ρν ρν∀ ×
    LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (∀ᵢᶜ Φ)) ρ∀ ρ∀ν ×
    leftStoreⁱ ρν∀ ≡ leftStoreⁱ ρ∀ν ×
    rightStoreⁱ ρν∀ ≡ rightStoreⁱ ρ∀ν
left-forall-store-square ρ with lift-left-store-result ρ
left-forall-store-square ρ | ρν , liftν
    with lift-store-result ρ
left-forall-store-square ρ | ρν , liftν | ρ∀ , lift∀
    with lift-store-result ρν
left-forall-store-square ρ | ρν , liftν | ρ∀ , lift∀
    | ρν∀ , liftν∀ with lift-left-store-result ρ∀
left-forall-store-square ρ | ρν , liftν | ρ∀ , lift∀
    | ρν∀ , liftν∀ | ρ∀ν , lift∀ν =
  ρν , ρ∀ , ρν∀ , ρ∀ν ,
  liftν , lift∀ , liftν∀ , lift∀ν ,
  trans
    (leftStoreⁱ-lift liftν∀)
    (trans
      (cong ⟰ᵗ (leftStoreⁱ-lift-left liftν))
      (sym
        (trans
          (leftStoreⁱ-lift-left lift∀ν)
          (cong ⟰ᵗ (leftStoreⁱ-lift lift∀))))) ,
  trans
    (rightStoreⁱ-lift liftν∀)
    (trans
      (cong ⟰ᵗ (rightStoreⁱ-lift-left liftν))
      (sym
        (trans
          (rightStoreⁱ-lift-left lift∀ν)
          (rightStoreⁱ-lift lift∀))))

left-forall-ctx-square :
  ∀ {Φ Δᴸ Δᴿ} (γ : CtxImp Φ Δᴸ Δᴿ) →
  ∃[ γν ] ∃[ γ∀ ] ∃[ γν∀ ] ∃[ γ∀ν ]
    LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν ×
    LiftCtxⁱ (∀ᵢᶜ Φ) γ γ∀ ×
    LiftCtxⁱ (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) γν γν∀ ×
    LiftLeftCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ (∀ᵢᶜ Φ)) γ∀ γ∀ν ×
    leftCtxⁱ γν∀ ≡ leftCtxⁱ γ∀ν ×
    rightCtxⁱ γν∀ ≡ rightCtxⁱ γ∀ν
left-forall-ctx-square γ with lift-left-ctx-result γ
left-forall-ctx-square γ | γν , liftν with lift-ctx-result γ
left-forall-ctx-square γ | γν , liftν | γ∀ , lift∀
    with lift-ctx-result γν
left-forall-ctx-square γ | γν , liftν | γ∀ , lift∀
    | γν∀ , liftν∀ with lift-left-ctx-result γ∀
left-forall-ctx-square γ | γν , liftν | γ∀ , lift∀
    | γν∀ , liftν∀ | γ∀ν , lift∀ν =
  γν , γ∀ , γν∀ , γ∀ν ,
  liftν , lift∀ , liftν∀ , lift∀ν ,
  trans
    (leftCtxⁱ-lift liftν∀)
    (trans
      (cong ⤊ᵗ (leftCtxⁱ-lift-left liftν))
      (sym
        (trans
          (leftCtxⁱ-lift-left lift∀ν)
          (cong ⤊ᵗ (leftCtxⁱ-lift lift∀))))) ,
  trans
    (rightCtxⁱ-lift liftν∀)
    (trans
      (cong ⤊ᵗ (rightCtxⁱ-lift-left liftν))
      (sym
        (trans
          (rightCtxⁱ-lift-left lift∀ν)
          (rightCtxⁱ-lift lift∀))))

left-source-lift-Λᵀ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {γν : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρν∀ : StoreImp (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      (suc (suc Δᴸ)) (suc Δᴿ)}
    {γν∀ : CtxImp (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ))
      (suc (suc Δᴸ)) (suc Δᴿ)}
    {V V′ A B q} →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γν →
  LiftStoreⁱ (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) ρν ρν∀ →
  LiftCtxⁱ (∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) γν γν∀ →
  Value V →
  Value V′ →
  ∀ᵢᶜ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc (suc Δᴸ) ∣ suc Δᴿ ∣ ρν∀ ∣ γν∀
    ⊢ᴺ renameᵗᵐ (extᵗ suc) V ⊑ V′
    ⦂ renameᵗ (extᵗ suc) A ⊑ B ∶ q →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρν ∣ γν
    ⊢ᴺ ⇑ᵗᵐ (Λ V) ⊑ Λ V′
    ⦂ ⇑ᵗ (`∀ A) ⊑ `∀ B ∶ ∀ⁱ q
left-source-lift-Λᵀ
    liftνρ liftνγ liftν∀ρ liftν∀γ vV vV′ V⊑V′ =
  Λ⊑Λᵀ liftν∀ρ liftν∀γ
    (renameᵗᵐ-preserves-Value (extᵗ suc) vV) vV′ V⊑V′
