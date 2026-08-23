module LR-narrow.LogicalRelation where

-- File Charter:
--   * Defines the draft step-indexed Kripke LR over center imprecision.
--   * Keeps precise and imprecise values in distinct endpoint contexts.
--   * Interprets X⊑★ through either an unoccupied dynamic atom or an
--     occupied paired atom protected by the matching imprecise runtime tag.
--   * Interprets paired and right-only universals through matching fresh
--     world extensions.
--   * Observes paired universal instantiation before allocation and records
--     that every successful return factors through the chosen extension.
--   * Reindexes the relation over polarized narrowing via the proved
--     derivation isomorphism.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_)
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

record RightDynamicPayloadShape {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᶜ)
    (Vᴵ : Term Δᴵ) : Set₁ where
  constructor right-dynamic-payload-shape
  field
    right-imprecise-ground : Ty Δᴵ
    right-imprecise-ground-proof : Ground right-imprecise-ground
    right-imprecise-consistency-env : Env∼ Δᴵ
    right-imprecise-ground-to-star :
      right-imprecise-consistency-env ⊢ right-imprecise-ground ∼★
    right-dynamic-imprecise-payload : Term Δᴵ
    right-dynamic-imprecise-shape : Vᴵ ≡
      right-dynamic-imprecise-payload
        ⟨ groundInjection right-imprecise-ground-proof
          right-imprecise-ground-to-star ⟩
    right-payload-imprecision :
      impEnv (core W) I.⊢ Aᴾ
        ⊑ embedImprecise (core W) right-imprecise-ground

open RightDynamicPayloadShape public

record DynamicAtomTagRelated {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (ℛ : PayloadRelation (core W))
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set₁ where
  constructor dynamic-atom-tag-related
  field
    dynamic-center-variable : TyVar Δᶜ
    dynamic-mode : impEnv (core W) dynamic-center-variable ≡ I.X⊑★
    atom-precise-ground : Ty Δᴾ
    atom-precise-ground-proof : Ground atom-precise-ground
    atom-precise-ground-center :
      embedPrecise (core W) atom-precise-ground ≡
        ＇ dynamic-center-variable
    atom-precise-consistency-env : Env∼ Δᴾ
    atom-precise-ground-to-star :
      atom-precise-consistency-env ⊢ atom-precise-ground ∼★
    atom-precise-payload : Term Δᴾ
    atom-precise-tag-shape : Vᴾ ≡
      atom-precise-payload
        ⟨ groundInjection atom-precise-ground-proof
          atom-precise-ground-to-star ⟩
    atom-relation-holds :
      DynamicAtomHolds ℛ
        (semanticEntry W dynamic-center-variable) dynamic-mode
        Vᴵ atom-precise-payload

open DynamicAtomTagRelated public

record AlignedDynamicAtomRelated {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (ℛ : PayloadRelation (core W)) (Z : TyVar Δᶜ)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set₁ where
  constructor aligned-dynamic-atom-related
  field
    aligned-imprecise-ground : Ty Δᴵ
    aligned-imprecise-ground-proof : Ground aligned-imprecise-ground
    aligned-imprecise-ground-center :
      embedImprecise (core W) aligned-imprecise-ground ≡ ＇ Z
    aligned-imprecise-consistency-env : Env∼ Δᴵ
    aligned-imprecise-ground-to-star :
      aligned-imprecise-consistency-env ⊢
        aligned-imprecise-ground ∼★
    aligned-imprecise-payload : Term Δᴵ
    aligned-imprecise-tag-shape : Vᴵ ≡
      aligned-imprecise-payload
        ⟨ groundInjection aligned-imprecise-ground-proof
          aligned-imprecise-ground-to-star ⟩
    aligned-atom-relation-holds :
      PairedAtomHolds ℛ (semanticEntry W Z)
        aligned-imprecise-payload Vᴾ

open AlignedDynamicAtomRelated public

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

  ValueImprecisionᵏ zero W
      (I.∀⊑ {A = Aᴾ} {B = Aᴵ} nonvar occurs p) Vᴵ Vᴾ =
    TypedEndpoints W (I.∀⊑ nonvar occurs p) Vᴵ Vᴾ ×
    Σ[ Bᴾ ∈ Ty _ ]
    Σ[ Bᴵ ∈ Ty _ ]
      (embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Aᴾ)
      × (embedImprecise (core W) Bᴵ ≡ Aᴵ)
      × RightUniversalsRelated W p Bᴾ Bᴵ zero Vᴵ Vᴾ

  ValueImprecisionᵏ zero W p Vᴵ Vᴾ = TypedEndpoints W p Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W I.★⊑★ Vᴵ Vᴾ =
    TypedEndpoints W I.★⊑★ Vᴵ Vᴾ ×
    (DynamicPayloadRelated W k Vᴵ Vᴾ ⊎
      DynamicAtomTagRelated W (ValueImprecisionᵏ k W) Vᴵ Vᴾ)

  ValueImprecisionᵏ (suc k) W (I.ι⊑ι {ι = ι}) Vᴵ Vᴾ =
    TypedEndpoints W (I.ι⊑ι {ι = ι}) Vᴵ Vᴾ ×
    SameBaseValue ι Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.X⊑X {X = X}) Vᴵ Vᴾ =
    TypedEndpoints W (I.X⊑X {X = X}) Vᴵ Vᴾ ×
    PairedAtomHolds (ValueImprecisionᵏ k W) (semanticEntry W X) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.⇒⊑⇒ p q) Vᴵ Vᴾ =
    TypedEndpoints W (I.⇒⊑⇒ p q) Vᴵ Vᴾ ×
    FunctionsRelated W p q (suc k) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W
      (I.∀⊑∀ {A = Aᴾ} {B = Aᴵ} p) Vᴵ Vᴾ =
    TypedEndpoints W (I.∀⊑∀ p) Vᴵ Vᴾ ×
    Σ[ Bᴾ ∈ Ty _ ]
    Σ[ Bᴵ ∈ Ty _ ]
      (embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Aᴾ)
      × (embedImprecise (core W) (`∀ Bᴵ) ≡ `∀ Aᴵ)
      × UniversalsRelated W p Bᴾ Bᴵ (suc k) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W
      (I.⇒⊑★ {A = A} {B = B} p q) Vᴵ Vᴾ =
    TypedEndpoints W (I.⇒⊑★ p q) Vᴵ Vᴾ ×
    RightDynamicPayloadRelated W (A ⇒ B) k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.ι⊑★ {ι = ι}) Vᴵ Vᴾ =
    TypedEndpoints W (I.ι⊑★ {ι = ι}) Vᴵ Vᴾ ×
    RightDynamicPayloadRelated W (‵ ι) k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W (I.X⊑★ {X = X} eq) Vᴵ Vᴾ =
    TypedEndpoints W (I.X⊑★ eq) Vᴵ Vᴾ ×
    (DynamicAtomHolds (ValueImprecisionᵏ k W) (semanticEntry W X) eq
        Vᴵ Vᴾ ⊎
      AlignedDynamicAtomRelated W (ValueImprecisionᵏ k W) X Vᴵ Vᴾ)

  ValueImprecisionᵏ (suc k) W
      (I.∀⊑ {A = Aᴾ} {B = Aᴵ} nonvar occurs p) Vᴵ Vᴾ =
    TypedEndpoints W (I.∀⊑ nonvar occurs p) Vᴵ Vᴾ ×
    Σ[ Bᴾ ∈ Ty _ ]
    Σ[ Bᴵ ∈ Ty _ ]
      (embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Aᴾ)
      × (embedImprecise (core W) Bᴵ ≡ Aᴵ)
      × RightUniversalsRelated W p Bᴾ Bᴵ (suc k) Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W I.∀★⊑★ Vᴵ Vᴾ =
    TypedEndpoints W I.∀★⊑★ Vᴵ Vᴾ ×
    RightDynamicPayloadRelated W (`∀ ★) k Vᴵ Vᴾ

  ValueImprecisionᵏ (suc k) W
      (I.∀⊑★ {A = A} nonstar p) Vᴵ Vᴾ =
    TypedEndpoints W (I.∀⊑★ nonstar p) Vᴵ Vᴾ ×
    RightDynamicPayloadRelated W (`∀ A) k Vᴵ Vᴾ

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

  PostBindValueRelation : ∀
      {Δᴾ Δᴵ Δᶜ Δᴾᵇ Δᴵᵇ Δᶜᵇ Aᴾ Aᴵ}
      {W : World Δᴾ Δᴵ Δᶜ}
      {bound : World Δᴾᵇ Δᴵᵇ Δᶜᵇ}
    → Future W bound
    → impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ
    → IndexedValueRelation W
  PostBindValueRelation {bound = bound} W≼B p W′ W≼W′ k Vᴵ Vᴾ =
    Σ[ bound≼W′ ∈ Future bound W′ ]
      (future-trans W≼B bound≼W′ ≡ W≼W′)
      × ValueImprecisionᵏ k W′
          (liftCenterImprecision W≼W′ p) Vᴵ Vᴾ

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
        (s : liftPreciseBody W≼W′ Bᴾ [ Rᴾ ]ᵗ
          ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ Bᴵ [ Rᴵ ]ᵗ)
      → let bound = pairedBindWorld W′ Rᴾ Rᴵ r
            W′≼B = future-paired (future-refl {W = W′}) r
        in ComputationsRelated W′
            (PostBindValueRelation W′≼B s) (suc k)
            (liftImpreciseTerm W≼W′ Vᴵ
              ⦂∀ liftImpreciseBody W≼W′ Bᴵ [ Rᴵ ])
            (liftPreciseTerm W≼W′ Vᴾ
              ⦂∀ liftPreciseBody W≼W′ Bᴾ [ Rᴾ ]))
    × UniversalsRelated W p Bᴾ Bᴵ k Vᴵ Vᴾ

  RightUniversalsRelated : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    → (W : World Δᴾ Δᴵ Δᶜ)
    → I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ
    → Ty (suc Δᴾ)
    → Ty Δᴵ
    → ℕ
    → Term Δᴵ
    → Term Δᴾ
    → Set₁

  RightUniversalsRelated W p Bᴾ Bᴵ zero Vᴵ Vᴾ =
    ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′)
      (r : impEnv (core W′) I.⊢ embedPrecise (core W′) Rᴾ ⊑ ★)
      (s : liftPreciseBody W≼W′ Bᴾ [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseTy W≼W′ Bᴵ)
    → let bound = preciseBindWorld W′ Rᴾ r
          W′≼B = future-precise (future-refl {W = W′}) r
      in ComputationsRelated W′
          (PostBindValueRelation W′≼B s) zero
          (liftImpreciseTerm W≼W′ Vᴵ)
          (liftPreciseTerm W≼W′ Vᴾ
            ⦂∀ liftPreciseBody W≼W′ Bᴾ [ Rᴾ ])

  RightUniversalsRelated W p Bᴾ Bᴵ (suc k) Vᴵ Vᴾ =
    (∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′)
        (r : impEnv (core W′) I.⊢ embedPrecise (core W′) Rᴾ ⊑ ★)
        (s : liftPreciseBody W≼W′ Bᴾ [ Rᴾ ]ᵗ
          ⊑ᵂ⟨ core W′ ⟩ liftImpreciseTy W≼W′ Bᴵ)
      → let bound = preciseBindWorld W′ Rᴾ r
            W′≼B = future-precise (future-refl {W = W′}) r
        in ComputationsRelated W′
            (PostBindValueRelation W′≼B s) (suc k)
            (liftImpreciseTerm W≼W′ Vᴵ)
            (liftPreciseTerm W≼W′ Vᴾ
              ⦂∀ liftPreciseBody W≼W′ Bᴾ [ Rᴾ ]))
    × RightUniversalsRelated W p Bᴾ Bᴵ k Vᴵ Vᴾ

  RightDynamicPayloadRelated : ∀ {Δᴾ Δᴵ Δᶜ}
    → (W : World Δᴾ Δᴵ Δᶜ)
    → Ty Δᶜ
    → ℕ
    → Term Δᴵ
    → Term Δᴾ
    → Set₁
  RightDynamicPayloadRelated W Aᴾ k Vᴵ Vᴾ =
    Σ[ shape ∈ RightDynamicPayloadShape W Aᴾ Vᴵ ]
      ValueImprecisionᵏ k W (right-payload-imprecision shape)
        (right-dynamic-imprecise-payload shape) Vᴾ

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

dynamic-atom-tag-map : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {ℛ ℛ′ : PayloadRelation (core W)}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → PayloadMap (core W) ℛ ℛ′
  → DynamicAtomTagRelated W ℛ Vᴵ Vᴾ
  → DynamicAtomTagRelated W ℛ′ Vᴵ Vᴾ
dynamic-atom-tag-map {W = W} f
    (dynamic-atom-tag-related Z mode G g ground-center μ G∼★ U
      tag-shape related) =
  dynamic-atom-tag-related Z mode G g ground-center μ G∼★ U
    tag-shape (dynamic-holds-map f (semanticEntry W Z) mode related)

aligned-dynamic-atom-map : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {ℛ ℛ′ : PayloadRelation (core W)}
    {Z : TyVar Δᶜ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → PayloadMap (core W) ℛ ℛ′
  → AlignedDynamicAtomRelated W ℛ Z Vᴵ Vᴾ
  → AlignedDynamicAtomRelated W ℛ′ Z Vᴵ Vᴾ
aligned-dynamic-atom-map {W = W} {Z = Z} f
    (aligned-dynamic-atom-related G g ground-center μ G∼★ U
      tag-shape related) =
  aligned-dynamic-atom-related G g ground-center μ G∼★ U
    tag-shape (paired-holds-map f (semanticEntry W Z) related)

dynamic-atom-tag : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {ℛ : PayloadRelation (core W)} {Z : TyVar Δᶜ}
    (mode : impEnv (core W) Z ≡ I.X⊑★)
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : Env∼ Δᴾ} (Gᴾ∼★ : μᴾ ⊢ Gᴾ ∼★)
    {Vᴵ : Term Δᴵ} {Uᴾ : Term Δᴾ}
  → DynamicAtomHolds ℛ (semanticEntry W Z) mode Vᴵ Uᴾ
  → DynamicAtomTagRelated W ℛ Vᴵ
      (Uᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
dynamic-atom-tag mode gᴾ ground-center Gᴾ∼★ related =
  dynamic-atom-tag-related _ mode _ gᴾ ground-center _ Gᴾ∼★
    _ refl related
