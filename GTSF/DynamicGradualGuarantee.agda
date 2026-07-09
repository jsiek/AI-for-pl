module DynamicGradualGuarantee where

-- File Charter:
--   * Top-level gradual-term dynamic gradual guarantee statement.
--   * Starts from closed source gradual term imprecision, compiles both sides,
--     and classifies the compiled runs as related final values, left blame, or
--     mutual divergence.
--   * This is a checked statement surface only; the proof is expected to factor
--     through compile monotonicity into `NuTermImprecision` and then a ν-term
--     simulation theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; proj₁; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx using (ctxWf-[])
open import Compile using (compile)
open import GradualTermImprecision
  using
    ( _∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_
    ; gradual-term-imprecision-source-typing
    ; gradual-term-imprecision-target-typing
    )
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction
  using
    ( StoreChanges
    ; applyStores
    ; applyTyCtxs
    ; applyTys
    ; _—→[_]_
    ; _—↠[_]_
    )
open import NuTermImprecision
  using
    ( StoreImp
    ; leftStoreⁱ
    ; rightStoreⁱ
    ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
    )
open import NuTerms using (Term; Value; blame)

------------------------------------------------------------------------
-- Local aliases for applying store changes
------------------------------------------------------------------------

infixl 8 _∙Δ_ _∙Σ_ _∙ᵀ_

_∙Δ_ : StoreChanges → TyCtx → TyCtx
χs ∙Δ Δ = applyTyCtxs χs Δ

_∙Σ_ : StoreChanges → Store → Store
χs ∙Σ Σ = applyStores χs Σ

_∙ᵀ_ : StoreChanges → Ty → Ty
χs ∙ᵀ A = applyTys χs A

------------------------------------------------------------------------
-- Convergence and divergence for compiled Nu terms
------------------------------------------------------------------------

Convergesᶜ : Term → Set
Convergesᶜ M =
  ∃[ W ] (Σ[ χs ∈ StoreChanges ]
    ((M —↠[ χs ] W) × (Value W ⊎ (W ≡ blame))))

Divergesᶜ : Term → Set
Divergesᶜ M = ¬ Convergesᶜ M

------------------------------------------------------------------------
-- Runtime observations for compiled closed programs
------------------------------------------------------------------------

DivergeOrBlameᶜ : Term → Set
DivergeOrBlameᶜ M =
  ∀ N →
  ∀ {χs} →
  M —↠[ χs ] N →
  (N ≡ blame) ⊎ (∃[ χ ] (∃[ N′ ] (N —→[ χ ] N′)))

------------------------------------------------------------------------
-- Closed gradual-term statement
------------------------------------------------------------------------

compiled-left :
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Term
compiled-left M⊑M′ =
  proj₁
    (compile ctxWf-[]
      (gradual-term-imprecision-source-typing M⊑M′))

compiled-right :
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Term
compiled-right M⊑M′ =
  proj₁
    (compile ctxWf-[]
      (gradual-term-imprecision-target-typing M⊑M′))

GradualDGG : Set₁
GradualDGG =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
    -- Part 1: if the more precise side reaches a value, the less precise
    -- side reaches a related value.
    (∀ V χs →
      compiled-left M⊑M′ —↠[ χs ] V →
      Value V →
      ∃[ V′ ] (Σ[ χs′ ∈ StoreChanges ]
      (∃[ Φ ] (Σ[ ρ ∈ StoreImp Φ (χs ∙Δ 0) (χs′ ∙Δ 0) ]
      (Σ[ q ∈
          (Φ ∣ χs ∙Δ 0 ⊢ χs ∙ᵀ A ⊑ χs′ ∙ᵀ B ⊣ χs′ ∙Δ 0) ]
        ((compiled-right M⊑M′ —↠[ χs′ ] V′) ×
         Value V′ ×
         (leftStoreⁱ ρ ≡ χs ∙Σ []) ×
         (rightStoreⁱ ρ ≡ χs′ ∙Σ []) ×
         Φ ∣ χs ∙Δ 0 ∣ χs′ ∙Δ 0 ∣ ρ ∣ []
           ⊢ᴺ V ⊑ V′ ⦂ χs ∙ᵀ A ⊑ χs′ ∙ᵀ B ∶ q))))))
    -- Part 2: if the more precise side diverges, the less precise side
    -- diverges.
    × (Divergesᶜ (compiled-left M⊑M′) →
       Divergesᶜ (compiled-right M⊑M′))
    -- Part 3: if the less precise side reaches a value, the more precise side
    -- reaches a related value or blames.
    × (∀ V′ χs′ →
      compiled-right M⊑M′ —↠[ χs′ ] V′ →
      Value V′ →
        (∃[ V ] (Σ[ χs ∈ StoreChanges ]
        (∃[ Φ ] (Σ[ ρ ∈ StoreImp Φ (χs ∙Δ 0) (χs′ ∙Δ 0) ]
        (Σ[ q ∈
            (Φ ∣ χs ∙Δ 0 ⊢ χs ∙ᵀ A ⊑ χs′ ∙ᵀ B ⊣ χs′ ∙Δ 0) ]
          ((compiled-left M⊑M′ —↠[ χs ] V) ×
           Value V ×
           (leftStoreⁱ ρ ≡ χs ∙Σ []) ×
           (rightStoreⁱ ρ ≡ χs′ ∙Σ []) ×
           Φ ∣ χs ∙Δ 0 ∣ χs′ ∙Δ 0 ∣ ρ ∣ []
             ⊢ᴺ V ⊑ V′ ⦂ χs ∙ᵀ A ⊑ χs′ ∙ᵀ B ∶ q)))))
        ⊎ (∃[ χs ] (compiled-left M⊑M′ —↠[ χs ] blame))))
    -- Part 4: if the less precise side diverges, the more precise side keeps
    -- stepping forever unless it has already reached blame.
    × (Divergesᶜ (compiled-right M⊑M′) →
       DivergeOrBlameᶜ (compiled-left M⊑M′))
