module
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  where

-- File Charter:
--   * Defines the exact residual evidence preserved while a target
--     instantiation allocates a fresh seal and completes its administrative
--     reduction.
--   * Retains the matched pre-allocation body relation, the cast/index
--     creation equation, and the store lineage joining that body world to
--     the final right-extended world.
--   * Omits arbitrary endpoint renaming, store embedding, and endpoint
--     equality transport; those belong in separate admissibility lemmas.
--   * Does not construct or re-export a term-imprecision edge.

open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion; Inert; ModeEnv; inst)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Imprecision using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴿᵢ
  )
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; ∀ⁱ_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  (No•; Term; Value; Λ_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using
  (Ty; TyCtx; ★; wf★; `∀; ⇑ᵗ)


record TargetInstantiationCreation
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {W W′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {f : Φ ∣ Δᴸ ⊢ `∀ D ⊑ B ⊣ Δᴿ}
    {body-shape : ImprecisionShape} : Set₁ where
  constructor target-instantiation-creation
  field
    store-prefix : StoreImpPrefix ρ₀ ρ⁺
    cast-mode : CastMode μ
    seal-mode : SealModeStore★ μ (rightStoreⁱ ρ₀)
    instantiation-typing :
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ inst B s ∶ `∀ C ⊑ B
    matched-store-lift :
      LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ∀
    right-store-lift :
      LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ⁺ ρᴿ⁺
    source-body-value : Value W
    source-body-no-bullet : No• W
    target-body-value : Value W′
    target-body-no-bullet : No• W′
    body-cast-inert : Inert s
    matched-body-relation :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
        ⊢ᴺ W ⊑ W′ ⦂ D ⊑ C ∶ r
    instantiation-shape :
      widening ⊢ᶜ inst B s ⦂ νˢ body-shape
    index-composition :
      ⌊ ∀ⁱ r ⌋ ； νˢ body-shape ≋ ⌊ f ⌋
    source-result-typing :
      Δᴸ
        ∣ leftStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
        ∣ [] ⊢ Λ W ⦂ `∀ D
    target-result-typing :
      suc Δᴿ
        ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
        ∣ [] ⊢ W′ ⟨ s ⟩ ⦂ ⇑ᵗ B
