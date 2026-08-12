module LR-narrow.LogicalRelation where

-- File Charter:
--   * Defines a step-indexed Kripke value relation by recursion on the live
--     type-imprecision derivation `p : Aᴾ ⊑ Aᴵ`.
--   * Presents the less-precise `Aᴵ` endpoint on the semantic left and the
--     more-precise `Aᴾ` endpoint on the semantic right.
--   * Requires every related pair to be closed, well typed at the endpoints
--     selected by `p`, and semantically related at its constructor.
--   * Uses only direct interpreter observations, never small-step reduction.

open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ImprecisionWf
open import Interpreter using
  ( Outcome
  ; SealName
  ; TypeEnvironment
  ; Value
  ; applyValue
  ; blamed
  ; constant
  ; instantiateValue
  ; lookup
  ; returned
  ; seal-name
  ; sealed
  ; tagged
  )
  renaming (World to RuntimeWorld)
open import LR-narrow.Atoms
open import LR-narrow.ClosedValues
open import LR-narrow.Dynamic
open import LR-narrow.World
open import Primitives using (κℕ)
open import Typing.InterpreterSemanticTypingCore using
  (ValueTyping; ⟦_⟧[_])
open import Types using (Base; Ground; Ty; TyCtx; `ℕ)

------------------------------------------------------------------------
-- Closed, typed value narrowing at an exact imprecision derivation
------------------------------------------------------------------------

record TypedClosedEndpoints
    {Φ : ImpCtx} {Δᴾ Δᴵ : TyCtx} {Aᴾ Aᴵ : Ty}
    (p : Φ ∣ Δᴾ ⊢ Aᴾ ⊑ Aᴵ ⊣ Δᴵ)
    {w : World} (I : Interpretation {Φ} {Δᴾ} {Δᴵ} w)
    (Vᴵ Vᴾ : Value) : Set₁ where
  constructor typed-closed-endpoints
  field
    left-closed : ClosedValue (left-world w) Vᴵ
    right-closed : ClosedValue (right-world w) Vᴾ
    left-typed :
      ValueTyping (left-world w) Vᴵ ⟦ Aᴵ ⟧[ left-types I ]
    right-typed :
      ValueTyping (right-world w) Vᴾ ⟦ Aᴾ ⟧[ right-types I ]

open TypedClosedEndpoints public

-- This record is deliberately not itself called narrowing: it supplies the
-- closure and endpoint-typing invariant shared by every semantic clause.

data AssumptionRelated
    {Φ : ImpCtx} {Δᴾ Δᴵ : TyCtx} {w : World}
    (I : Interpretation {Φ} {Δᴾ} {Δᴵ} w) :
    ∀ {assumption}
    → Atom assumption → ℕ → Value → Value → Set₁ where
  paired-payload : ∀ {X Y αᴵ αᴾ Uᴵ Uᴾ n}
      {a : Atom (X ˣ⊑ˣ Y)}
    → lookup (right-types I) X ≡ just (seal-name αᴾ)
    → lookup (left-types I) Y ≡ just (seal-name αᴵ)
    → AtomHolds a n Uᴵ Uᴾ
    → AssumptionRelated I a n (sealed αᴵ Uᴵ) (sealed αᴾ Uᴾ)

  right-sealed-payload : ∀ {X α Vᴵ Uᴾ n}
      {a : Atom (X ˣ⊑★)}
    → lookup (right-types I) X ≡ just (seal-name α)
    → AtomHolds a n Vᴵ Uᴾ
    → AssumptionRelated I a n Vᴵ (sealed α Uᴾ)

data SameBaseValue : Base → Value → Value → Set where
  same-natural : ∀ n
    → SameBaseValue `ℕ (constant (κℕ n)) (constant (κℕ n))

------------------------------------------------------------------------
-- Bounded direct-interpreter observations
------------------------------------------------------------------------

Computation : Set
Computation = ℕ → Outcome

IndexedValueRelation : ImpCtx → TyCtx → TyCtx → Set₂
IndexedValueRelation Φ Δᴾ Δᴵ =
  {w : World} →
  Interpretation {Φ} {Δᴾ} {Δᴵ} w →
  ℕ → Value → Value → Set₁

record ComputationsRelated
    {Φ : ImpCtx} {Δᴾ Δᴵ : TyCtx}
    (R : IndexedValueRelation Φ Δᴾ Δᴵ)
    {w : World} (I : Interpretation {Φ} {Δᴾ} {Δᴵ} w)
    (k : ℕ) (left right : Computation) : Set₁ where
  field
    forward-return : ∀ {n Uᴵ Vᴵ}
      → n ≤ k
      → left n ≡ returned Uᴵ Vᴵ
      →
        (Σ[ m ∈ ℕ ]
         Σ[ Uᴾ ∈ RuntimeWorld ]
         Σ[ Vᴾ ∈ Value ]
         Σ[ future ∈ World ]
         Σ[ futureᵢ ∈ Interpretation {Φ} {Δᴾ} {Δᴵ} future ]
           (futureᵢ ⊒ⁱ I) ×
           (left-world future ≡ Uᴵ) ×
           (right-world future ≡ Uᴾ) ×
           (right m ≡ returned Uᴾ Vᴾ) ×
           R futureᵢ (k ∸ n) Vᴵ Vᴾ)
        ⊎
        (Σ[ m ∈ ℕ ]
         Σ[ Uᴾ ∈ RuntimeWorld ]
         Σ[ future ∈ World ]
         Σ[ futureᵢ ∈ Interpretation {Φ} {Δᴾ} {Δᴵ} future ]
           (futureᵢ ⊒ⁱ I) ×
           (left-world future ≡ Uᴵ) ×
           (right-world future ≡ Uᴾ) ×
           (right m ≡ blamed Uᴾ))

    backward-return : ∀ {n Uᴾ Vᴾ}
      → n ≤ k
      → right n ≡ returned Uᴾ Vᴾ
      → Σ[ m ∈ ℕ ]
        Σ[ Uᴵ ∈ RuntimeWorld ]
        Σ[ Vᴵ ∈ Value ]
        Σ[ future ∈ World ]
        Σ[ futureᵢ ∈ Interpretation {Φ} {Δᴾ} {Δᴵ} future ]
          (futureᵢ ⊒ⁱ I) ×
          (left-world future ≡ Uᴵ) ×
          (right-world future ≡ Uᴾ) ×
          (left m ≡ returned Uᴵ Vᴵ) ×
          R futureᵢ (k ∸ n) Vᴵ Vᴾ

    forward-blame : ∀ {n Uᴵ}
      → n ≤ k
      → left n ≡ blamed Uᴵ
      → Σ[ m ∈ ℕ ]
        Σ[ Uᴾ ∈ RuntimeWorld ]
        Σ[ future ∈ World ]
        Σ[ futureᵢ ∈ Interpretation {Φ} {Δᴾ} {Δᴵ} future ]
          (futureᵢ ⊒ⁱ I) ×
          (left-world future ≡ Uᴵ) ×
          (right-world future ≡ Uᴾ) ×
          (right m ≡ blamed Uᴾ)

open ComputationsRelated public

------------------------------------------------------------------------
-- Step-indexed value relation, structurally indexed by `p`
------------------------------------------------------------------------

-- The new `id★` branch calls the relation at a strictly smaller step index
-- but at an existentially chosen ground derivation.  The remaining branches
-- retain the previous structural recursion through function and universal
-- subderivations.  Agda cannot combine those two decreasing orders across the
-- higher-order relation passed to `ComputationsRelated`.  The semantic
-- lexicographic termination argument is therefore recorded here explicitly,
-- while the pragma asks Agda to accept that argument.
{-# TERMINATING #-}
mutual

  ValueNarrowingᵏ : ∀ {Φ Δᴾ Δᴵ Aᴾ Aᴵ}
    → ℕ
    → (p : Φ ∣ Δᴾ ⊢ Aᴾ ⊑ Aᴵ ⊣ Δᴵ)
    → {w : World}
    → Interpretation {Φ} {Δᴾ} {Δᴵ} w
    → Value → Value → Set₁

  ValueNarrowingᵏ zero p I Vᴵ Vᴾ = TypedClosedEndpoints p I Vᴵ Vᴾ

  ValueNarrowingᵏ (suc k) id★ I Vᴵ Vᴾ =
    TypedClosedEndpoints id★ I Vᴵ Vᴾ ×
    Σ[ shape ∈ DynamicPayloadShape I Vᴵ Vᴾ ]
      ValueNarrowingᵏ k (payload-imprecision shape) I
        (dynamic-left-payload shape) (dynamic-right-payload shape)

  ValueNarrowingᵏ (suc k) (idˣ assumption∈ X< Y<) I Vᴵ Vᴾ =
    TypedClosedEndpoints (idˣ assumption∈ X< Y<) I Vᴵ Vᴾ ×
    AssumptionRelated I
      (lookup-atom assumption∈ (atoms I)) k Vᴵ Vᴾ

  ValueNarrowingᵏ (suc k) (idι {ι = ι}) I Vᴵ Vᴾ =
    TypedClosedEndpoints (idι {ι = ι}) I Vᴵ Vᴾ ×
    SameBaseValue ι Vᴵ Vᴾ

  ValueNarrowingᵏ (suc k) (p ↦ q) I Vᴵ Vᴾ =
    TypedClosedEndpoints (p ↦ q) I Vᴵ Vᴾ ×
    FunctionsRelated p q I k Vᴵ Vᴾ

  ValueNarrowingᵏ (suc k) (∀ⁱ p) I Vᴵ Vᴾ =
    TypedClosedEndpoints (∀ⁱ p) I Vᴵ Vᴾ ×
    UniversalsRelated p I k Vᴵ Vᴾ

  -- Provisional gradual boundaries. The final clauses must expose the
  -- imprecise-left tag and relate it to the precise-right payload at the
  -- induced ground imprecision.
  ValueNarrowingᵏ (suc k) (tag ι) I Vᴵ Vᴾ =
    TypedClosedEndpoints (tag ι) I Vᴵ Vᴾ

  ValueNarrowingᵏ (suc k) (tag p ⇛ q) I Vᴵ Vᴾ =
    TypedClosedEndpoints (tag p ⇛ q) I Vᴵ Vᴾ

  ValueNarrowingᵏ (suc k) (tagˣ assumption∈ X<) I Vᴵ Vᴾ =
    TypedClosedEndpoints (tagˣ assumption∈ X<) I Vᴵ Vᴾ ×
    AssumptionRelated I
      (lookup-atom assumption∈ (atoms I)) k Vᴵ Vᴾ

  -- Provisional precise-right universal. The compiler's reveal conversion may
  -- require an additional coerceValue observation after instantiation.
  ValueNarrowingᵏ (suc k) (ν nonvar occurs p) I Vᴵ Vᴾ =
    TypedClosedEndpoints (ν nonvar occurs p) I Vᴵ Vᴾ ×
    RightUniversalsRelated p I k Vᴵ Vᴾ

  FunctionsRelated : ∀ {Φ Δᴾ Δᴵ Aᴾ Aᴵ Bᴾ Bᴵ}
    → (p : Φ ∣ Δᴾ ⊢ Aᴾ ⊑ Aᴵ ⊣ Δᴵ)
    → (q : Φ ∣ Δᴾ ⊢ Bᴾ ⊑ Bᴵ ⊣ Δᴵ)
    → {w : World}
    → Interpretation {Φ} {Δᴾ} {Δᴵ} w
    → ℕ → Value → Value → Set₁

  -- Function application with zero interpreter fuel always times out, so the
  -- enclosing endpoint certificate is the only zero-index requirement.
  FunctionsRelated p q I zero Vᴵ Vᴾ = ⊤

  FunctionsRelated p q I (suc k) Vᴵ Vᴾ =
    (∀ {future} (futureᵢ : Interpretation future) {Uᴵ Uᴾ}
      → futureᵢ ⊒ⁱ I
      → ValueNarrowingᵏ (suc k) p futureᵢ Uᴵ Uᴾ
      → ComputationsRelated (λ J j → ValueNarrowingᵏ j q J)
          futureᵢ (suc k)
          (λ n → applyValue (left-world future) Vᴵ Uᴵ n)
          (λ n → applyValue (right-world future) Vᴾ Uᴾ n))
    × FunctionsRelated p q I k Vᴵ Vᴾ

  UniversalsRelated : ∀ {Φ Δᴾ Δᴵ Aᴾ Aᴵ}
    → (p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴾ ⊢ Aᴾ ⊑ Aᴵ ⊣ suc Δᴵ)
    → {w : World}
    → Interpretation {Φ} {Δᴾ} {Δᴵ} w
    → ℕ → Value → Value → Set₁

  -- Paired instantiation with zero interpreter fuel also always times out.
  UniversalsRelated p I zero Vᴵ Vᴾ = ⊤

  UniversalsRelated p I (suc k) Vᴵ Vᴾ =
    (∀ (extension : PairedBinderExtension I)
      → ComputationsRelated (λ J j → ValueNarrowingᵏ j p J)
          (paired-body-interpretation extension) (suc k)
          (λ n → instantiateValue
            (left-world (paired-future extension))
            (paired-left-seal extension) Vᴵ n)
          (λ n → instantiateValue
            (right-world (paired-future extension))
            (paired-right-seal extension) Vᴾ n))
    × UniversalsRelated p I k Vᴵ Vᴾ

  RightUniversalsRelated : ∀ {Φ Δᴾ Δᴵ Aᴾ Aᴵ}
    → (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴾ ⊢ Aᴾ ⊑ Aᴵ ⊣ Δᴵ)
    → {w : World}
    → Interpretation {Φ} {Δᴾ} {Δᴵ} w
    → ℕ → Value → Value → Set₁

  RightUniversalsRelated p I zero Vᴵ Vᴾ =
    ∀ (extension : RightBinderExtension I)
    → ComputationsRelated (λ J j → ValueNarrowingᵏ j p J)
        (right-body-interpretation extension) zero
        (λ n → returned
          (left-world (right-future-world extension)) Vᴵ)
        (λ n → instantiateValue
          (right-world (right-future-world extension))
          (right-binder-seal extension) Vᴾ n)

  RightUniversalsRelated p I (suc k) Vᴵ Vᴾ =
    (∀ (extension : RightBinderExtension I)
      → ComputationsRelated (λ J j → ValueNarrowingᵏ j p J)
          (right-body-interpretation extension) (suc k)
          (λ n → returned
            (left-world (right-future-world extension)) Vᴵ)
          (λ n → instantiateValue
            (right-world (right-future-world extension))
            (right-binder-seal extension) Vᴾ n))
    × RightUniversalsRelated p I k Vᴵ Vᴾ

ValueNarrowing : ∀ {Φ Δᴾ Δᴵ Aᴾ Aᴵ}
  → (p : Φ ∣ Δᴾ ⊢ Aᴾ ⊑ Aᴵ ⊣ Δᴵ)
  → {w : World}
  → Interpretation {Φ} {Δᴾ} {Δᴵ} w
  → ℕ → Value → Value → Set₁
ValueNarrowing p I k = ValueNarrowingᵏ k p I

DynamicPayloadRelated : ∀
    {Φ} {Δᴾ Δᴵ : TyCtx} {w : World}
  → (I : Interpretation {Φ} {Δᴾ} {Δᴵ} w)
  → ℕ → Value → Value → Set₁
DynamicPayloadRelated I k Vᴵ Vᴾ =
  Σ[ shape ∈ DynamicPayloadShape I Vᴵ Vᴾ ]
    ValueNarrowing (payload-imprecision shape) I k
      (dynamic-left-payload shape) (dynamic-right-payload shape)

tags-and-payload : ∀
    {Φ} {Δᴾ Δᴵ : TyCtx} {w : World}
    {I : Interpretation {Φ} {Δᴾ} {Δᴵ} w} {k}
    {Gᴾ Gᴵ : Ty} {gᴾ : Ground Gᴾ} {gᴵ : Ground Gᴵ}
    {θᴵ θᴾ : TypeEnvironment} {Uᴵ Uᴾ : Value}
    (q : Φ ∣ Δᴾ ⊢ Gᴾ ⊑ Gᴵ ⊣ Δᴵ)
  → GroundTagAgreement I q gᴵ gᴾ θᴵ θᴾ
  → ValueNarrowing q I k Uᴵ Uᴾ
  → DynamicPayloadRelated I k
      (tagged gᴵ θᴵ Uᴵ) (tagged gᴾ θᴾ Uᴾ)
tags-and-payload q tags-related payload-related =
  dynamic-payload-shape _ _ _ _ _ _ _ _ refl refl q tags-related ,
  payload-related
