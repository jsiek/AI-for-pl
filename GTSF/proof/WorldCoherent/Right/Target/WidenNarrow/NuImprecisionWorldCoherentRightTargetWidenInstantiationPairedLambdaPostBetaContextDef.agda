module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextDef
  where

-- File Charter:
--   * Defines the exact relation exposed after target `ν ★` allocation and
--     the administrative `β-Λ•` step in the direct paired-lambda
--     target-instantiation case.
--   * Retains the matched body world, the ambient-prefix world, the exact
--     right lift, arbitrary universal root, closed final endpoints, inert
--     cast, and endpoint typings required by exact creation.
--   * Repairs the former full-catch-up contract, which discarded these
--     witnesses and was refuted by the focused post-beta regression.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
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
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; ∀ⁱ_)
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
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
open import
  proof.Core.Properties.NuImprecisionIndexedRenamingProperties
  using (⊑-target-lift-rightᵢ)
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (TargetInstantiationCreation)


WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ :
  Set₁
WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {W W′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {f : Φ ∣ Δᴸ ⊢ `∀ D ⊑ B ⊣ Δᴿ}
    {body-shape : ImprecisionShape} →
  TargetInstantiationCreation
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape}
    (StoreImpPrefix ρ₀ ρ⁺)
    (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
      ⊢ᴺ W ⊑ W′ ⦂ D ⊑ C ∶ r) →
  ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ
    ∣ store-right zero ★ wf★ ∷ ρᴿ⁺ ∣ []
    ⊢ᴺ Λ W ⊑ W′ ⟨ s ⟩
      ⦂ `∀ D ⊑ ⇑ᵗ B
      ∶ ⊑-target-lift-rightᵢ f
