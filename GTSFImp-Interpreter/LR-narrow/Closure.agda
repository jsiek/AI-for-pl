module LR-narrow.Closure where

-- File Charter:
--   * Exposes the closure theorems of the three-context logical relation.
--   * States downward closure and Kripke monotonicity at the public boundary.
--   * Delegates proof scripts to proof.LR-narrow.Closure.

open import Data.Nat using (ℕ; suc; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.LogicalRelation
import proof.LR-narrow.Closure as Proof

typed-endpoints-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → TypedEndpoints W p Vᴵ Vᴾ
  → TypedEndpoints W′ (liftCenterImprecision W≼W′ p)
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
typed-endpoints-future = Proof.typed-endpoints-future

functions-related-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ}
    {k : ℕ} {Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → FunctionsRelated W p q k Vᴵ Vᴾ
  → FunctionsRelated W′ (liftCenterImprecision W≼W′ p)
      (liftCenterImprecision W≼W′ q) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
functions-related-future = Proof.functions-related-future

universals-related-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {k : ℕ} {Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → UniversalsRelated W p Bᴾ Bᴵ k Vᴵ Vᴾ
  → UniversalsRelated W′ (liftCenterBodyImprecision W≼W′ p)
      (liftPreciseBody W≼W′ Bᴾ) (liftImpreciseBody W≼W′ Bᴵ) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
universals-related-future {p = p} W≼W′ related =
  Proof.universals-related-future {p = p} W≼W′ related

right-universals-related-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {k : ℕ} {Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → RightUniversalsRelated W p Bᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W′
      (liftCenterDynamicBodyImprecision W≼W′ p)
      (liftPreciseBody W≼W′ Bᴾ) (liftImpreciseTy W≼W′ Bᴵ) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
right-universals-related-future {p = p} {Bᴵ = Bᴵ} W≼W′ related =
  Proof.right-universals-related-future {p = p} {Bᴵ = Bᴵ}
    W≼W′ related

value-imprecision-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision W′ (liftCenterImprecision W≼W′ p) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
value-imprecision-future = Proof.value-imprecision-future

value-imprecision-local→center : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
    {k Vᴵ Vᴾ}
  → ValueImprecision W′ (liftLocalImprecision W≼W′ p) k Vᴵ Vᴾ
  → ValueImprecision W′ (liftCenterImprecision W≼W′ p) k Vᴵ Vᴾ
value-imprecision-local→center = Proof.value-imprecision-local→center

value-imprecision-center→local : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
    {k Vᴵ Vᴾ}
  → ValueImprecision W′ (liftCenterImprecision W≼W′ p) k Vᴵ Vᴾ
  → ValueImprecision W′ (liftLocalImprecision W≼W′ p) k Vᴵ Vᴾ
value-imprecision-center→local = Proof.value-imprecision-center→local

right-dynamic-payload-related-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {k Vᴵ Vᴾ} (W≼W′ : Future W W′)
  → RightDynamicPayloadRelated W Aᴾ k Vᴵ Vᴾ
  → RightDynamicPayloadRelated W′ (liftCenterTy W≼W′ Aᴾ) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
right-dynamic-payload-related-future =
  Proof.right-dynamic-payload-related-future

value-imprecision-downward : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {k : ℕ} {Vᴵ Vᴾ}
  → ValueImprecision W p (suc k) Vᴵ Vᴾ
  → ValueImprecision W p k Vᴵ Vᴾ
value-imprecision-downward = Proof.value-imprecision-downward

value-imprecision-downward-to : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {j k : ℕ} {Vᴵ Vᴾ}
  → j ≤ k
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision W p j Vᴵ Vᴾ
value-imprecision-downward-to = Proof.value-imprecision-downward-to

right-dynamic-payload-downward : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ}
    {W : World Δᴾ Δᴵ Δᶜ} {k Vᴵ Vᴾ}
  → RightDynamicPayloadRelated W Aᴾ (suc k) Vᴵ Vᴾ
  → RightDynamicPayloadRelated W Aᴾ k Vᴵ Vᴾ
right-dynamic-payload-downward = Proof.right-dynamic-payload-downward

semantic-atom-value : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {X : TyVar Δᶜ} {k Vᴵ Vᴾ}
  → PairedAtomHolds (ValueImprecisionᵏ k W) (semanticEntry W X) Vᴵ Vᴾ
  → ValueImprecision W (I.X⊑X {X = X}) (suc k) Vᴵ Vᴾ
semantic-atom-value = Proof.semantic-atom-value

dynamic-semantic-atom-value : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {X : TyVar Δᶜ} {k Vᴵ Vᴾ}
    (eq : impEnv (core W) X ≡ I.X⊑★)
  → DynamicAtomHolds (ValueImprecisionᵏ k W) (semanticEntry W X) eq
      Vᴵ Vᴾ
  → ValueImprecision W (I.X⊑★ eq) (suc k) Vᴵ Vᴾ
dynamic-semantic-atom-value = Proof.dynamic-semantic-atom-value
