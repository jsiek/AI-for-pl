module proof.LR-narrow.ValueExtraction where

-- File Charter:
--   * A future world that does not change either endpoint context is the
--     reflexive future: allocations strictly grow a context.
--   * Consequently a computation relation between two values collapses
--     to the value relation at the same index and the same world.
--   * Extracted from proof.LR-narrow.Cast so that developments that do
--     not depend on the cast obligations can use them.

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; 1+n≰n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Types
import Imprecision as I
open import TyStore
open import CastTerms
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import proof.LR-narrow.Application using (value-return-exact)

future-precise-monotone : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Δᴾ ≤ Δᴾ′
future-precise-monotone future-refl = ≤-refl
future-precise-monotone (future-paired W≼W′ related) =
  ≤-trans (future-precise-monotone W≼W′) (n≤1+n _)
future-precise-monotone (future-precise W≼W′ r★) =
  ≤-trans (future-precise-monotone W≼W′) (n≤1+n _)
future-precise-monotone (future-imprecise W≼W′) =
  future-precise-monotone W≼W′

future-imprecise-monotone : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Δᴵ ≤ Δᴵ′
future-imprecise-monotone future-refl = ≤-refl
future-imprecise-monotone (future-paired W≼W′ related) =
  ≤-trans (future-imprecise-monotone W≼W′) (n≤1+n _)
future-imprecise-monotone (future-precise W≼W′ r★) =
  future-imprecise-monotone W≼W′
future-imprecise-monotone (future-imprecise W≼W′) =
  ≤-trans (future-imprecise-monotone W≼W′) (n≤1+n _)

data ReflexiveFuture {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) :
    ∀ {Δᶜ′} {W′ : World Δᴾ Δᴵ Δᶜ′} → Future W W′ → Set where
  future-is-refl : ReflexiveFuture W future-refl

future-refl-view : ∀ {Δᴾ Δᴵ Δᶜ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ}
    {W′ : World Δᴾ Δᴵ Δᶜ′}
    (W≼W′ : Future W W′)
  → ReflexiveFuture W W≼W′
future-refl-view future-refl = future-is-refl
future-refl-view (future-paired W≼W′ related) =
  ⊥-elim (1+n≰n (future-precise-monotone W≼W′))
future-refl-view (future-precise W≼W′ r★) =
  ⊥-elim (1+n≰n (future-precise-monotone W≼W′))
future-refl-view (future-imprecise W≼W′) =
  ⊥-elim (1+n≰n (future-imprecise-monotone W≼W′))

related-computation-values : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {q : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ComputationsRelated W (FutureValueRelation q) (suc k) Vᴵ Vᴾ
  → Value Vᴵ
  → Value Vᴾ
  → ValueImprecision W q (suc k) Vᴵ Vᴾ
related-computation-values {W = W} {k = k} related vVᴵ vVᴾ
    with value-return-exact { Σ = impreciseStore (core W) } zero vVᴵ
related-computation-values {W = W} {k = k} related vVᴵ vVᴾ
    | imprecise-return
    with forward-return related (s≤s z≤n) imprecise-return
related-computation-values {W = W} {k = k} related vVᴵ vVᴾ
    | imprecise-return
    | inj₁ (m , resultᴾ , precise-return , paired)
    with value-return-exact { Σ = preciseStore (core W) } m vVᴾ
related-computation-values {W = W} {k = k} related vVᴵ vVᴾ
    | imprecise-return
    | inj₁ (m , resultᴾ , precise-return , paired)
    | precise-exact with trans (sym precise-exact) precise-return
related-computation-values {W = W} {k = k} related vVᴵ vVᴾ
    | imprecise-return
    | inj₁ (m , resultᴾ , precise-return , paired)
    | precise-exact | refl
    with paired
related-computation-values related vVᴵ vVᴾ
    | imprecise-return
    | inj₁ (m , resultᴾ , precise-return , paired)
    | precise-exact | refl
    | paired-returns W′ W≼W′ imprecise-store precise-store
        imprecise-terms precise-terms relation
    with future-refl-view W≼W′
related-computation-values related vVᴵ vVᴾ
    | imprecise-return
    | inj₁ (m , resultᴾ , precise-return , paired)
    | precise-exact | refl
    | paired-returns W′ W≼W′ imprecise-store precise-store
        imprecise-terms precise-terms relation
    | future-is-refl = relation
related-computation-values {W = W} {k = k} related vVᴵ vVᴾ
    | imprecise-return
    | inj₂ (m , Δ′ , changes , trace , precise-blame)
    with value-return-exact { Σ = preciseStore (core W) } m vVᴾ
related-computation-values {W = W} {k = k} related vVᴵ vVᴾ
    | imprecise-return
    | inj₂ (m , Δ′ , changes , trace , precise-blame)
    | precise-return with trans (sym precise-return) precise-blame
related-computation-values {W = W} {k = k} related vVᴵ vVᴾ
    | imprecise-return
    | inj₂ (m , Δ′ , changes , trace , precise-blame)
    | precise-return | ()

