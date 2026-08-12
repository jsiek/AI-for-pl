module LR-narrow.LogicalRelation where

-- File Charter:
--   * Defines the draft step-indexed Kripke LR over center imprecision.
--   * Keeps precise and imprecise values in distinct endpoint contexts.
--   * Interprets X⊑X and X⊑★ center variables through mode-indexed atoms.
--   * Interprets paired and right-only universals through matching fresh
--     world extensions.
--   * Reindexes the relation over polarized narrowing via the proved
--     derivation isomorphism.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import CastTerms
open import Primitives
import Consistency as C
open C using (Env∼; _⊢_∼★; _⊢_∼_; idᵍ; _!; ground-nonstar)
import Imprecision as I
import NarrowWiden as NW
open import NarrowWidenIsomorphism using (narrowing→imprecision)
open import LR-narrow.World
open import LR-narrow.Computation

------------------------------------------------------------------------
-- Typed endpoints and observable value shapes
------------------------------------------------------------------------

record TypedEndpoints {Δᴾ Δᴵ Δᶜ} {Aᴾ Aᴵ : Ty Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ)
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set₁ where
  constructor typed-endpoints
  field
    impreciseType : Ty Δᴵ
    preciseType : Ty Δᴾ
    impreciseEmbedded : embedImprecise (core W) impreciseType ≡ Aᴵ
    preciseEmbedded : embedPrecise (core W) preciseType ≡ Aᴾ
    imprecise-value : Value Vᴵ
    precise-value : Value Vᴾ
    imprecise-typed :
      ⟨ Δᴵ , impreciseStore (core W) , [] ⟩ ⊢ Vᴵ ⦂ impreciseType
    precise-typed :
      ⟨ Δᴾ , preciseStore (core W) , [] ⟩ ⊢ Vᴾ ⦂ preciseType

open TypedEndpoints public

data SameBaseValue {Δᴾ Δᴵ : TyCtx} :
    Base → Term Δᴵ → Term Δᴾ → Set where
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

record DynamicPayloadShape {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set₁ where
  constructor dynamic-payload-shape
  field
    precise-ground : Ty Δᴾ
    imprecise-ground : Ty Δᴵ
    precise-ground-proof : Ground precise-ground
    imprecise-ground-proof : Ground imprecise-ground
    precise-consistency-env : Env∼ Δᴾ
    imprecise-consistency-env : Env∼ Δᴵ
    precise-ground-to-star :
      precise-consistency-env ⊢ precise-ground ∼★
    imprecise-ground-to-star :
      imprecise-consistency-env ⊢ imprecise-ground ∼★
    dynamic-precise-payload : Term Δᴾ
    dynamic-imprecise-payload : Term Δᴵ
    dynamic-imprecise-shape : Vᴵ ≡
      dynamic-imprecise-payload ⟨ groundInjection imprecise-ground-proof
        imprecise-ground-to-star ⟩
    dynamic-precise-shape : Vᴾ ≡
      dynamic-precise-payload ⟨ groundInjection precise-ground-proof
        precise-ground-to-star ⟩
    payload-imprecision :
      precise-ground ⊑ᵂ⟨ core W ⟩ imprecise-ground

open DynamicPayloadShape public

------------------------------------------------------------------------
-- Step-indexed value relation
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  ValueImprecisionᵏ : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    → ℕ
    → (W : World Δᴾ Δᴵ Δᶜ)
    → impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ
    → Term Δᴵ
    → Term Δᴾ
    → Set₁

  ValueImprecisionᵏ zero W p Vᴵ Vᴾ = TypedEndpoints W p Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W I.★⊑★ Vᴵ Vᴾ =
    TypedEndpoints W I.★⊑★ Vᴵ Vᴾ ×
    DynamicPayloadRelated W k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.ι⊑ι {ι = ι}) Vᴵ Vᴾ =
    TypedEndpoints W (I.ι⊑ι {ι = ι}) Vᴵ Vᴾ ×
    SameBaseValue ι Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.X⊑X {X = X}) Vᴵ Vᴾ =
    TypedEndpoints W (I.X⊑X {X = X}) Vᴵ Vᴾ ×
    PairedAtomHolds (semanticEntry W X) (suc k) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.⇒⊑⇒ p q) Vᴵ Vᴾ =
    TypedEndpoints W (I.⇒⊑⇒ p q) Vᴵ Vᴾ ×
    FunctionsRelated W p q k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W
      (I.∀⊑∀ {A = Aᴾ} {B = Aᴵ} p) Vᴵ Vᴾ =
    TypedEndpoints W (I.∀⊑∀ p) Vᴵ Vᴾ ×
    Σ[ Bᴾ ∈ Ty _ ]
    Σ[ Bᴵ ∈ Ty _ ]
      (embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Aᴾ)
      × (embedImprecise (core W) (`∀ Bᴵ) ≡ `∀ Aᴵ)
      × UniversalsRelated W p Bᴾ Bᴵ k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.⇒⊑★ p q) Vᴵ Vᴾ =
    TypedEndpoints W (I.⇒⊑★ p q) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.ι⊑★ {ι = ι}) Vᴵ Vᴾ =
    TypedEndpoints W (I.ι⊑★ {ι = ι}) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.X⊑★ eq) Vᴵ Vᴾ =
    TypedEndpoints W (I.X⊑★ eq) Vᴵ Vᴾ ×
    DynamicAtomHolds (semanticEntry W _) eq (suc k) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W
      (I.∀⊑ {A = Aᴾ} nonvar occurs p) Vᴵ Vᴾ =
    TypedEndpoints W (I.∀⊑ nonvar occurs p) Vᴵ Vᴾ ×
    Σ[ Bᴾ ∈ Ty _ ]
      (embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Aᴾ)
      × RightUniversalsRelated W p Bᴾ k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W I.∀★⊑★ Vᴵ Vᴾ =
    TypedEndpoints W I.∀★⊑★ Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.∀⊑★ nonstar p) Vᴵ Vᴾ =
    TypedEndpoints W (I.∀⊑★ nonstar p) Vᴵ Vᴾ ×
    DynamicUniversalRelated W p k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W I.bot-elim Vᴵ Vᴾ =
    TypedEndpoints W I.bot-elim Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W I.bot⊑★ Vᴵ Vᴾ =
    TypedEndpoints W I.bot⊑★ Vᴵ Vᴾ

  FutureValueRelation : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
      {W : World Δᴾ Δᴵ Δᶜ}
    → impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ
    → IndexedValueRelation W
  FutureValueRelation p W′ W≼W′ k Vᴵ Vᴾ =
    ValueImprecisionᵏ k W′ (liftCenterImprecision W≼W′ p) Vᴵ Vᴾ

  FunctionsRelated : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    → (W : World Δᴾ Δᴵ Δᶜ)
    → impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ
    → impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ
    → ℕ
    → Term Δᴵ
    → Term Δᴾ
    → Set₁

  FunctionsRelated W p q zero Vᴵ Vᴾ = ⊤

  FunctionsRelated W p q (suc k) Vᴵ Vᴾ =
    (∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
      → ValueImprecisionᵏ (suc k) W′
          (liftCenterImprecision W≼W′ p) Uᴵ Uᴾ
      → ComputationsRelated W′
          (FutureValueRelation (liftCenterImprecision W≼W′ q)) (suc k)
          (liftImpreciseTerm W≼W′ Vᴵ · Uᴵ)
          (liftPreciseTerm W≼W′ Vᴾ · Uᴾ))
    × FunctionsRelated W p q k Vᴵ Vᴾ

  UniversalsRelated : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    → (W : World Δᴾ Δᴵ Δᶜ)
    → I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
    → Ty (suc Δᴾ)
    → Ty (suc Δᴵ)
    → ℕ
    → Term Δᴵ
    → Term Δᴾ
    → Set₁

  UniversalsRelated W p Bᴾ Bᴵ zero Vᴵ Vᴾ = ⊤

  UniversalsRelated W p Bᴾ Bᴵ (suc k) Vᴵ Vᴾ =
    (∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
        (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
        (fresh : SemanticAtom (pairedBindCore (core W′) Rᴾ Rᴵ) Fin.zero)
      → let bound = pairedBindWorld W′ Rᴾ Rᴵ fresh
            W≼B = future-paired W≼W′ r fresh
            body = openFreshImprecision {W = bound}
              (liftCenterBodyImprecision W≼B p)
        in ComputationsRelated bound
            (FutureValueRelation {W = bound} body) (suc k)
            (liftImpreciseTerm W≼B Vᴵ
              ⦂∀ liftImpreciseBody W≼B Bᴵ [ ＇ Fin.zero ])
            (liftPreciseTerm W≼B Vᴾ
              ⦂∀ liftPreciseBody W≼B Bᴾ [ ＇ Fin.zero ]))
    × UniversalsRelated W p Bᴾ Bᴵ k Vᴵ Vᴾ

  RightUniversalsRelated : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    → (W : World Δᴾ Δᴵ Δᶜ)
    → I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
    → Ty (suc Δᴾ)
    → ℕ
    → Term Δᴵ
    → Term Δᴾ
    → Set₁

  RightUniversalsRelated W p Bᴾ zero Vᴵ Vᴾ = ⊤

  RightUniversalsRelated W p Bᴾ (suc k) Vᴵ Vᴾ =
    (∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′)
        (fresh : DynamicSemanticAtom
          (preciseBindCore (core W′) Rᴾ) Fin.zero)
      → let bound = preciseBindWorld W′ Rᴾ fresh
            W≼B = future-precise W≼W′ fresh
            body = openFreshDynamicImprecision {W = bound} refl
              (liftCenterDynamicBodyImprecision W≼B p)
        in ComputationsRelated bound
            (FutureValueRelation {W = bound} body) (suc k)
            (liftImpreciseTerm W≼B Vᴵ)
            (liftPreciseTerm W≼B Vᴾ
              ⦂∀ liftPreciseBody W≼B Bᴾ [ ＇ Fin.zero ]))
    × RightUniversalsRelated W p Bᴾ k Vᴵ Vᴾ

  DynamicUniversalRelated : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ}
    → (W : World Δᴾ Δᴵ Δᶜ)
    → I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ ★
    → ℕ
    → Term Δᴵ
    → Term Δᴾ
    → Set₁
  DynamicUniversalRelated W p k Vᴵ Vᴾ =
    Σ[ μᴵ ∈ Env∼ _ ]
    Σ[ Uᴵ ∈ Term _ ]
      (Vᴵ ≡ Uᴵ ⟨ groundInjection ∀★ (C.∀∼★ {μ = μᴵ}) ⟩)
      × ValueImprecisionᵏ k W (I.∀⊑∀ p) Uᴵ Vᴾ

  DynamicPayloadRelated : ∀ {Δᴾ Δᴵ Δᶜ}
    → (W : World Δᴾ Δᴵ Δᶜ)
    → ℕ
    → Term Δᴵ
    → Term Δᴾ
    → Set₁
  DynamicPayloadRelated W k Vᴵ Vᴾ =
    Σ[ shape ∈ DynamicPayloadShape W Vᴵ Vᴾ ]
      ValueImprecisionᵏ k W (payload-imprecision shape)
        (dynamic-imprecise-payload shape)
        (dynamic-precise-payload shape)

ValueImprecision : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ
  → ℕ
  → Term Δᴵ
  → Term Δᴾ
  → Set₁
ValueImprecision W p k = ValueImprecisionᵏ k W p

ValueNarrowing : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → NW.Narrowing (impEnv (core W)) Aᴵ Aᴾ
  → ℕ
  → Term Δᴵ
  → Term Δᴾ
  → Set₁
ValueNarrowing W narrowing =
  ValueImprecision W (narrowing→imprecision narrowing)

tags-and-payload : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k}
    {Gᴾ : Ty Δᴾ} {Gᴵ : Ty Δᴵ}
    (gᴾ : Ground Gᴾ) (gᴵ : Ground Gᴵ)
    {μᴾ : Env∼ Δᴾ} {μᴵ : Env∼ Δᴵ}
    (Gᴾ∼★ : μᴾ ⊢ Gᴾ ∼★) (Gᴵ∼★ : μᴵ ⊢ Gᴵ ∼★)
    {Uᴵ : Term Δᴵ} {Uᴾ : Term Δᴾ}
    (q : Gᴾ ⊑ᵂ⟨ core W ⟩ Gᴵ)
  → ValueImprecision W q k Uᴵ Uᴾ
  → DynamicPayloadRelated W k
      (Uᴵ ⟨ groundInjection gᴵ Gᴵ∼★ ⟩)
      (Uᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
tags-and-payload gᴾ gᴵ Gᴾ∼★ Gᴵ∼★ q payload-related =
  dynamic-payload-shape _ _ gᴾ gᴵ _ _ Gᴾ∼★ Gᴵ∼★
    _ _ refl refl q , payload-related
