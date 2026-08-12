module LR-narrow.Closure where

-- File Charter:
--   * Exposes the closure theorems of the three-context logical relation.
--   * States downward closure and Kripke monotonicity at the public boundary.
--   * Delegates proof scripts to proof.LR-narrow.Closure.

open import Data.Nat using (ℕ; suc)

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
universals-related-future = Proof.universals-related-future

value-imprecision-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision W′ (liftCenterImprecision W≼W′ p) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
value-imprecision-future = Proof.value-imprecision-future

value-imprecision-downward : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {k : ℕ} {Vᴵ Vᴾ}
  → ValueImprecision W p (suc k) Vᴵ Vᴾ
  → ValueImprecision W p k Vᴵ Vᴾ
value-imprecision-downward = Proof.value-imprecision-downward

semantic-atom-value : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {X : TyVar Δᶜ} {k Vᴵ Vᴾ}
  → AtomHolds (semanticAtom W X) (suc k) Vᴵ Vᴾ
  → ValueImprecision W (I.X⊑X {X = X}) (suc k) Vᴵ Vᴾ
semantic-atom-value = Proof.semantic-atom-value
