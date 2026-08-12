module LR.LogicalRelation where

-- File Charter:
--   * Defines the draft step-indexed Kripke LR over GTSFImp imprecision.
--   * Relates imprecise-left and precise-right intrinsic cast values.
--   * Gives structural clauses for dynamic identity, functions, and paired
--     universals; remaining gradual boundaries retain typed endpoints.
--   * Reindexes the same relation over polarized narrowing via the proved
--     derivation isomorphism.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import CastTerms
open import Primitives
import Consistency as C
open C using (Env∼; _⊢_∼★; _⊢_∼_; idᵍ; _!; ground-nonstar)
import Imprecision as I
import NarrowWiden as NW
open import NarrowWidenIsomorphism using (narrowing→imprecision)
open import LR.World
open import LR.Computation

------------------------------------------------------------------------
-- Typed endpoints and observable value shapes
------------------------------------------------------------------------

record TypedEndpoints {Δ : TyCtx} {Aᴾ Aᴵ : Ty Δ}
    (W : World Δ) (p : impEnv W I.⊢ Aᴾ ⊑ Aᴵ)
    (Vᴵ Vᴾ : Term Δ) : Set₁ where
  constructor typed-endpoints
  field
    imprecise-value : Value Vᴵ
    precise-value : Value Vᴾ
    imprecise-typed : ⟨ Δ , impreciseStore W , [] ⟩ ⊢ Vᴵ ⦂ Aᴵ
    precise-typed : ⟨ Δ , preciseStore W , [] ⟩ ⊢ Vᴾ ⦂ Aᴾ

open TypedEndpoints public

data SameBaseValue {Δ : TyCtx} : Base → Term Δ → Term Δ → Set where
  same-natural : ∀ n
    → SameBaseValue `ℕ ($ (κℕ n)) ($ (κℕ n))

  same-boolean : ∀ b
    → SameBaseValue `𝔹 ($ (κ𝔹 b)) ($ (κ𝔹 b))

groundInjection : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ}
  → (g : Ground G)
  → μ ⊢ G ∼★
  → μ ⊢ G ∼ ★
groundInjection g G∼★ =
  let instance
        ground-instance = g
        ground-to-star-instance = G∼★
        ground-nonstar-instance = ground-nonstar g
  in idᵍ g !

record DynamicPayloadShape {Δ : TyCtx} (W : World Δ)
    (Vᴵ Vᴾ : Term Δ) : Set₁ where
  constructor dynamic-payload-shape
  field
    precise-ground : Ty Δ
    imprecise-ground : Ty Δ
    precise-ground-proof : Ground precise-ground
    imprecise-ground-proof : Ground imprecise-ground
    precise-consistency-env : Env∼ Δ
    imprecise-consistency-env : Env∼ Δ
    precise-ground-to-star :
      precise-consistency-env ⊢ precise-ground ∼★
    imprecise-ground-to-star :
      imprecise-consistency-env ⊢ imprecise-ground ∼★
    dynamic-precise-payload : Term Δ
    dynamic-imprecise-payload : Term Δ
    dynamic-imprecise-shape : Vᴵ ≡
      dynamic-imprecise-payload ⟨ groundInjection imprecise-ground-proof
        imprecise-ground-to-star ⟩
    dynamic-precise-shape : Vᴾ ≡
      dynamic-precise-payload ⟨ groundInjection precise-ground-proof
        precise-ground-to-star ⟩
    payload-imprecision : impEnv W I.⊢ precise-ground ⊑ imprecise-ground

open DynamicPayloadShape public

------------------------------------------------------------------------
-- Step-indexed value relation
------------------------------------------------------------------------

-- Dynamic identity decreases the step index while changing to the payload
-- derivation. Function and universal clauses recurse structurally as well.
{-# TERMINATING #-}
mutual
  ValueImprecisionᵏ : ∀ {Δ Aᴾ Aᴵ}
    → ℕ
    → (W : World Δ)
    → impEnv W I.⊢ Aᴾ ⊑ Aᴵ
    → Term Δ
    → Term Δ
    → Set₁

  ValueImprecisionᵏ zero W p Vᴵ Vᴾ = TypedEndpoints W p Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W I.★⊑★ Vᴵ Vᴾ =
    TypedEndpoints W I.★⊑★ Vᴵ Vᴾ ×
    DynamicPayloadRelated W k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.ι⊑ι {ι = ι}) Vᴵ Vᴾ =
    TypedEndpoints W (I.ι⊑ι {ι = ι}) Vᴵ Vᴾ ×
    SameBaseValue ι Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.X⊑X {X = X}) Vᴵ Vᴾ =
    TypedEndpoints W (I.X⊑X {X = X}) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.⇒⊑⇒ p q) Vᴵ Vᴾ =
    TypedEndpoints W (I.⇒⊑⇒ p q) Vᴵ Vᴾ ×
    FunctionsRelated W p q k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.∀⊑∀ p) Vᴵ Vᴾ =
    TypedEndpoints W (I.∀⊑∀ p) Vᴵ Vᴾ ×
    UniversalsRelated W p k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.⇒⊑★ p q) Vᴵ Vᴾ =
    TypedEndpoints W (I.⇒⊑★ p q) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.ι⊑★ {ι = ι}) Vᴵ Vᴾ =
    TypedEndpoints W (I.ι⊑★ {ι = ι}) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.X⊑★ eq) Vᴵ Vᴾ =
    TypedEndpoints W (I.X⊑★ eq) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.∀⊑ nonvar occurs p) Vᴵ Vᴾ =
    TypedEndpoints W (I.∀⊑ nonvar occurs p) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W I.∀★⊑★ Vᴵ Vᴾ =
    TypedEndpoints W I.∀★⊑★ Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.∀⊑★ nonstar p) Vᴵ Vᴾ =
    TypedEndpoints W (I.∀⊑★ nonstar p) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W I.bot-elim Vᴵ Vᴾ =
    TypedEndpoints W I.bot-elim Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W I.bot⊑★ Vᴵ Vᴾ =
    TypedEndpoints W I.bot⊑★ Vᴵ Vᴾ

  FutureValueRelation : ∀ {Δ Aᴾ Aᴵ} {W : World Δ}
    → impEnv W I.⊢ Aᴾ ⊑ Aᴵ
    → IndexedValueRelation W
  FutureValueRelation p W′ W≼W′ k Vᴵ Vᴾ =
    ValueImprecisionᵏ k W′ (liftImprecision W≼W′ p) Vᴵ Vᴾ

  FunctionsRelated : ∀ {Δ Aᴾ Aᴵ Bᴾ Bᴵ}
    → (W : World Δ)
    → impEnv W I.⊢ Aᴾ ⊑ Aᴵ
    → impEnv W I.⊢ Bᴾ ⊑ Bᴵ
    → ℕ
    → Term Δ
    → Term Δ
    → Set₁

  FunctionsRelated W p q zero Vᴵ Vᴾ = ⊤

  FunctionsRelated W p q (suc k) Vᴵ Vᴾ =
    (∀ {Δ′} (W′ : World Δ′) (W≼W′ : Future W W′) {Uᴵ Uᴾ}
      → ValueImprecisionᵏ (suc k) W′
          (liftImprecision W≼W′ p) Uᴵ Uᴾ
      → ComputationsRelated W′
          (FutureValueRelation (liftImprecision W≼W′ q)) (suc k)
          (liftTerm W≼W′ Vᴵ · Uᴵ) (liftTerm W≼W′ Vᴾ · Uᴾ))
    × FunctionsRelated W p q k Vᴵ Vᴾ

  UniversalsRelated : ∀ {Δ Aᴾ Aᴵ}
    → (W : World Δ)
    → I.extᵐ (impEnv W) I.⊢ Aᴾ ⊑ Aᴵ
    → ℕ
    → Term Δ
    → Term Δ
    → Set₁

  UniversalsRelated W p zero Vᴵ Vᴾ = ⊤

  UniversalsRelated {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} W p (suc k) Vᴵ Vᴾ =
    (∀ {Δ′} (W′ : World Δ′) (W≼W′ : Future W W′)
        (Rᴾ Rᴵ : Ty Δ′) (r : impEnv W′ I.⊢ Rᴾ ⊑ Rᴵ)
      → let bound = pairedBindWorld W′ Rᴾ Rᴵ
            W≼B = future-paired W≼W′ r
            body = openFreshImprecision {W = bound}
              (liftBodyImprecision W≼B p)
        in ComputationsRelated bound
            (FutureValueRelation {W = bound} body) (suc k)
            (liftTerm W≼B Vᴵ ⦂∀ liftBody W≼B Aᴵ [ ＇ Fin.zero ])
            (liftTerm W≼B Vᴾ ⦂∀ liftBody W≼B Aᴾ [ ＇ Fin.zero ]))
    × UniversalsRelated W p k Vᴵ Vᴾ

  DynamicPayloadRelated : ∀ {Δ}
    → (W : World Δ)
    → ℕ
    → Term Δ
    → Term Δ
    → Set₁
  DynamicPayloadRelated W k Vᴵ Vᴾ =
    Σ[ shape ∈ DynamicPayloadShape W Vᴵ Vᴾ ]
      ValueImprecisionᵏ k W (payload-imprecision shape)
        (dynamic-imprecise-payload shape) (dynamic-precise-payload shape)

ValueImprecision : ∀ {Δ Aᴾ Aᴵ}
  → (W : World Δ)
  → impEnv W I.⊢ Aᴾ ⊑ Aᴵ
  → ℕ
  → Term Δ
  → Term Δ
  → Set₁
ValueImprecision W p k = ValueImprecisionᵏ k W p

ValueNarrowing : ∀ {Δ Aᴾ Aᴵ}
  → (W : World Δ)
  → NW.Narrowing (impEnv W) Aᴵ Aᴾ
  → ℕ
  → Term Δ
  → Term Δ
  → Set₁
ValueNarrowing W narrowing =
  ValueImprecision W (narrowing→imprecision narrowing)

tags-and-payload : ∀ {Δ} {W : World Δ} {k}
    {Gᴾ Gᴵ : Ty Δ} (gᴾ : Ground Gᴾ) (gᴵ : Ground Gᴵ)
    {μᴾ μᴵ : Env∼ Δ}
    (Gᴾ∼★ : μᴾ ⊢ Gᴾ ∼★) (Gᴵ∼★ : μᴵ ⊢ Gᴵ ∼★)
    {Uᴵ Uᴾ : Term Δ}
    (q : impEnv W I.⊢ Gᴾ ⊑ Gᴵ)
  → ValueImprecision W q k Uᴵ Uᴾ
  → DynamicPayloadRelated W k
      (Uᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩)
      (Uᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
tags-and-payload gᴾ gᴵ Gᴾ∼★ Gᴵ∼★ q payload-related =
  dynamic-payload-shape _ _ gᴾ gᴵ _ _ Gᴾ∼★ Gᴵ∼★
    _ _ refl refl q , payload-related
