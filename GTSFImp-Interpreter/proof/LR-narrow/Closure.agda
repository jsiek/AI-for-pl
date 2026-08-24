module proof.LR-narrow.Closure where

-- File Charter:
--   * Proves closure properties of the three-context logical relation.
--   * Establishes downward closure and future-world monotonicity.
--   * Supplies the proof terms re-exported by LR-narrow.Closure.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m<n∨m≡n)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; sym; trans)
  renaming (subst to subst≡)

open import Types
open import CastTerms
import Primitives
import Consistency as C
open C using (Env∼; _⊢_∼★)
import Imprecision as I
import proof.Imprecision as PI
import proof.Consistency as PC
import proof.ImprecisionConsistency as IC
open import proof.TypeInTermSubst
  using (renameᵗᵐ-preserves-Value; toRename-wk-eq; typing-shiftᵗ-bind)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
import Conversion
import Level
open import TyStore using (TyStore; _∋_⦂_)

-- At index zero no imprecise step is available, so any two computations
-- are related.

computations-related-zero : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → ComputationsRelated W R zero Mᴵ Mᴾ
computations-related-zero = record
  { forward-return = λ ()
  ; backward-return = λ ()
  ; forward-blame = λ ()
  }

-- Termination note: the `X⊑★` dynamic case recurses at the same step
-- index into the slot's representation imprecision; this is
-- well-founded by allocation order (`dynamicFresh`, see the pragma
-- note in LR-narrow/LogicalRelation.agda).
{-# TERMINATING #-}
value-imprecision-downward : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {k : ℕ} {Vᴵ Vᴾ}
  → ValueImprecision W p (suc k) Vᴵ Vᴾ
  → ValueImprecision W p k Vᴵ Vᴾ
value-imprecision-downward {p = I.★⊑★} {k = zero}
    (endpoints , payload) = endpoints
value-imprecision-downward {p = I.ι⊑ι} {k = zero}
    (endpoints , same) = endpoints
value-imprecision-downward {p = I.X⊑X} {k = zero}
    (endpoints , related) = endpoints
value-imprecision-downward {p = I.⇒⊑⇒ p q} {k = zero}
    (endpoints , related) = endpoints
value-imprecision-downward {p = I.∀⊑∀ p} {k = zero}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , related) = endpoints
value-imprecision-downward {p = I.⇒⊑★ p q} {k = zero}
    (endpoints , payload) =
  endpoints
value-imprecision-downward {p = I.ι⊑★} {k = zero}
    (endpoints , payload) =
  endpoints
value-imprecision-downward {p = I.X⊑★ eq} {k = zero}
    (endpoints , related) =
  endpoints
value-imprecision-downward {p = I.∀⊑ nonvar occurs p} {k = zero}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , head , tail) = endpoints
value-imprecision-downward {p = I.∀★⊑★} {k = zero}
    (endpoints , payload) =
  endpoints
value-imprecision-downward {p = I.∀⊑★ nonstar p} {k = zero}
    (endpoints , payload) = endpoints
value-imprecision-downward {p = I.bot-elim} {k = zero} endpoints =
  endpoints
value-imprecision-downward {p = I.bot⊑★} {k = zero} endpoints =
  endpoints
value-imprecision-downward {p = I.★⊑★} {k = suc k}
    (endpoints , inj₁ (shape , payload)) =
  endpoints , inj₁ (shape , value-imprecision-downward payload)
value-imprecision-downward {p = I.★⊑★} {k = suc k}
    (endpoints , inj₂ related) =
  endpoints , inj₂
    (dynamic-atom-tag-map (value-imprecision-downward {k = suc k})
      related)
value-imprecision-downward {p = I.ι⊑ι} {k = suc k} related =
  related
value-imprecision-downward {W = W} {p = I.X⊑X {X = X}} {k = suc k}
    (endpoints , related) =
  endpoints ,
  paired-holds-map (value-imprecision-downward {k = k})
    (semanticEntry W X) related
value-imprecision-downward {p = I.⇒⊑⇒ p q} {k = suc k}
    (endpoints , head , tail) =
  endpoints , tail
value-imprecision-downward {p = I.∀⊑∀ p} {k = suc k}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , head , tail) =
  endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , tail
value-imprecision-downward {p = I.⇒⊑★ p q} {k = suc k}
    (endpoints , shape , payload) =
  endpoints , shape , value-imprecision-downward payload
value-imprecision-downward {p = I.ι⊑★} {k = suc k}
    (endpoints , shape , payload) =
  endpoints , shape , value-imprecision-downward payload
value-imprecision-downward {W = W} {p = I.X⊑★ {X = X} eq}
    {k = suc k} (endpoints , inj₁ related) =
  endpoints , inj₁
    (dynamic-holds-map (value-imprecision-downward {k = suc k})
      (semanticEntry W X) eq related)
value-imprecision-downward {p = I.X⊑★ eq} {k = suc k}
    (endpoints , inj₂ related) =
  endpoints , inj₂
    (aligned-dynamic-atom-map (value-imprecision-downward {k = k})
      related)
value-imprecision-downward {p = I.∀⊑ nonvar occurs p} {k = suc k}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , head , tail) =
  endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , tail
value-imprecision-downward {p = I.∀★⊑★} {k = suc k}
    (endpoints , shape , payload) =
  endpoints , shape , value-imprecision-downward payload
value-imprecision-downward {p = I.∀⊑★ nonstar p} {k = suc k}
    (endpoints , shape , payload) =
  endpoints , shape , value-imprecision-downward payload
value-imprecision-downward {p = I.bot-elim} {k = suc k} endpoints =
  endpoints
value-imprecision-downward {p = I.bot⊑★} {k = suc k} endpoints =
  endpoints

value-imprecision-downward-to : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {j k : ℕ} {Vᴵ Vᴾ}
  → j ≤ k
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision W p j Vᴵ Vᴾ
value-imprecision-downward-to {j = zero} {k = zero} z≤n related = related
value-imprecision-downward-to {j = suc j} {k = zero} () related
value-imprecision-downward-to {j = j} {k = suc k} j≤sk related
    with m≤n⇒m<n∨m≡n j≤sk
value-imprecision-downward-to {j = j} {k = suc k} j≤sk related
    | inj₁ (s≤s j≤k) =
  value-imprecision-downward-to j≤k
    (value-imprecision-downward related)
value-imprecision-downward-to {j = j} {k = suc k} j≤sk related
    | inj₂ refl = related

right-dynamic-payload-downward : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ}
    {W : World Δᴾ Δᴵ Δᶜ} {k Vᴵ Vᴾ}
  → RightDynamicPayloadRelated W Aᴾ (suc k) Vᴵ Vᴾ
  → RightDynamicPayloadRelated W Aᴾ k Vᴵ Vᴾ
right-dynamic-payload-downward (shape , payload) =
  shape , value-imprecision-downward payload

value-imprecision-endpoints : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {k : ℕ} {Vᴵ Vᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → TypedEndpoints W p Vᴵ Vᴾ
value-imprecision-endpoints {p = I.∀⊑ nonvar occurs p} {k = zero}
    related = related
value-imprecision-endpoints {p = I.★⊑★} {k = zero} related = related
value-imprecision-endpoints {p = I.ι⊑ι} {k = zero} related = related
value-imprecision-endpoints {p = I.X⊑X} {k = zero} related = related
value-imprecision-endpoints {p = I.⇒⊑⇒ p q} {k = zero} related =
  related
value-imprecision-endpoints {p = I.∀⊑∀ p} {k = zero} related =
  related
value-imprecision-endpoints {p = I.⇒⊑★ p q} {k = zero} related =
  related
value-imprecision-endpoints {p = I.ι⊑★} {k = zero} related = related
value-imprecision-endpoints {p = I.X⊑★ eq} {k = zero} related =
  related
value-imprecision-endpoints {p = I.∀★⊑★} {k = zero} related =
  related
value-imprecision-endpoints {p = I.∀⊑★ nonstar p} {k = zero}
    related = related
value-imprecision-endpoints {p = I.bot-elim} {k = zero} related =
  related
value-imprecision-endpoints {p = I.bot⊑★} {k = zero} related =
  related
value-imprecision-endpoints {k = suc k} related =
  value-imprecision-endpoints (value-imprecision-downward related)

sealed-precise-typing : ∀ {Δ} {Σ : TyStore Δ} {U : Term Δ}
    {X : TyVar Δ} {R A : Ty Δ}
  → Σ ∋ X ⦂ R
  → ⟨ Δ , Σ , [] ⟩ ⊢ U ⦂ A
  → A ≡ R
  → ⟨ Δ , Σ , [] ⟩ ⊢ U ↓ Conversion.seal X R ⦂ ＇ X
sealed-precise-typing bound U⊢ refl =
  ⊢conceal (Conversion.⊢↓-seal bound) U⊢

-- Endpoint evidence of sealed values at a slot, for any derivation at the
-- slot's types.

paired-holds-endpoints : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : World Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ} {k Vᴵ Vᴾ}
    (entry : SemanticEntry (core W) Z mode)
    (p : impEnv (core W) I.⊢ ＇ Z ⊑ ＇ Z)
  → PairedAtomHolds (ValueImprecisionᵏ k W) entry Vᴵ Vᴾ
  → TypedEndpoints W p Vᴵ Vᴾ
paired-holds-endpoints {W = W} (paired-entry a) p
    (atom-holds Uᴵ Uᴾ refl refl payloads) =
  let endpoints = value-imprecision-endpoints payloads
      typeᴵ-eq = IC.renameᵗ-injective
        (IC.toRenameᵗ-injective (impreciseEmbedding (core W)))
        (impreciseEmbedded endpoints)
      typeᴾ-eq = IC.renameᵗ-injective
        (IC.toRenameᵗ-injective (preciseEmbedding (core W)))
        (preciseEmbedded endpoints)
  in typed-endpoints (＇ impreciseVariable a) (＇ preciseVariable a)
       (cong (λ Y → ＇ Y) (impreciseAligned a))
       (cong (λ Y → ＇ Y) (preciseAligned a))
       (imprecise-value endpoints ↓ CastTerms.seal)
       (precise-value endpoints ↓ CastTerms.seal)
       (sealed-precise-typing (impreciseBound a)
         (imprecise-typed endpoints) typeᴵ-eq)
       (sealed-precise-typing (preciseBound a)
         (precise-typed endpoints) typeᴾ-eq)
paired-holds-endpoints (dynamic-entry a) p (Level.lift ())
paired-holds-endpoints (target-entry a) p (Level.lift ())

dynamic-holds-endpoints : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : World Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ} {k Vᴵ Vᴾ}
    (entry : SemanticEntry (core W) Z mode)
    (eq : mode ≡ I.X⊑★)
    (p : impEnv (core W) I.⊢ ＇ Z ⊑ ★)
  → DynamicAtomHolds (ValueImprecisionᵏ k W) entry eq Vᴵ Vᴾ
  → TypedEndpoints W p Vᴵ Vᴾ
dynamic-holds-endpoints (paired-entry a) eq p (Level.lift ())
dynamic-holds-endpoints {W = W} (dynamic-entry a) refl p
    (dynamic-holds Uᴾ refl payload) =
  let endpoints = value-imprecision-endpoints payload
      typeᴾ-eq = IC.renameᵗ-injective
        (IC.toRenameᵗ-injective (preciseEmbedding (core W)))
        (preciseEmbedded endpoints)
      typeᴵ-eq = IC.renameᵗ-injective
        (IC.toRenameᵗ-injective (impreciseEmbedding (core W)))
        (impreciseEmbedded endpoints)
  in typed-endpoints ★ (＇ dynamicPreciseVariable a) refl
       (cong (λ Y → ＇ Y) (dynamicPreciseAligned a))
       (imprecise-value endpoints)
       (precise-value endpoints ↓ CastTerms.seal)
       (subst≡ (λ T → ⟨ _ , _ , [] ⟩ ⊢ _ ⦂ T)
         typeᴵ-eq (imprecise-typed endpoints))
       (sealed-precise-typing (dynamicBound a)
         (precise-typed endpoints) typeᴾ-eq)
dynamic-holds-endpoints (target-entry a) refl p (Level.lift ())

-- Sealed payloads related at a paired slot are related values at the
-- slot's center variable.

semantic-atom-value : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {X : TyVar Δᶜ} {k Vᴵ Vᴾ}
  → PairedAtomHolds (ValueImprecisionᵏ k W) (semanticEntry W X) Vᴵ Vᴾ
  → ValueImprecision W (I.X⊑X {X = X}) (suc k) Vᴵ Vᴾ
semantic-atom-value {W = W} {X = X} related =
  paired-holds-endpoints (semanticEntry W X) I.X⊑X related , related

dynamic-semantic-atom-value : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {X : TyVar Δᶜ} {k Vᴵ Vᴾ}
    (eq : impEnv (core W) X ≡ I.X⊑★)
  → DynamicAtomHolds (ValueImprecisionᵏ (suc k) W) (semanticEntry W X)
      eq Vᴵ Vᴾ
  → ValueImprecision W (I.X⊑★ eq) (suc k) Vᴵ Vᴾ
dynamic-semantic-atom-value {W = W} {X = X} eq related =
  dynamic-holds-endpoints (semanticEntry W X) eq (I.X⊑★ eq) related ,
  inj₁ related

precise-value-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {V}
    (W≼W′ : Future W W′)
  → Value V
  → Value (liftPreciseTerm W≼W′ V)
precise-value-future future-refl vV = vV
precise-value-future (future-paired W≼W′ related) vV =
  renameᵗᵐ-preserves-Value C.wk↪ᵗ (precise-value-future W≼W′ vV)
precise-value-future (future-precise W≼W′ r★) vV =
  renameᵗᵐ-preserves-Value C.wk↪ᵗ (precise-value-future W≼W′ vV)
precise-value-future (future-imprecise W≼W′) vV =
  precise-value-future W≼W′ vV

imprecise-value-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {V}
    (W≼W′ : Future W W′)
  → Value V
  → Value (liftImpreciseTerm W≼W′ V)
imprecise-value-future future-refl vV = vV
imprecise-value-future (future-paired W≼W′ related) vV =
  renameᵗᵐ-preserves-Value C.wk↪ᵗ (imprecise-value-future W≼W′ vV)
imprecise-value-future (future-precise W≼W′ r★) vV =
  imprecise-value-future W≼W′ vV
imprecise-value-future (future-imprecise W≼W′) vV =
  renameᵗᵐ-preserves-Value C.wk↪ᵗ (imprecise-value-future W≼W′ vV)

precise-typing-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ A}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {V}
    (W≼W′ : Future W W′)
  → ⟨ Δᴾ , preciseStore (core W) , [] ⟩ ⊢ V ⦂ A
  → ⟨ Δᴾ′ , preciseStore (core W′) , [] ⟩
      ⊢ liftPreciseTerm W≼W′ V ⦂ liftPreciseTy W≼W′ A
precise-typing-future future-refl V⊢ = V⊢
precise-typing-future (future-paired W≼W′ related) V⊢ =
  typing-shiftᵗ-bind (precise-typing-future W≼W′ V⊢)
precise-typing-future (future-precise W≼W′ r★) V⊢ =
  typing-shiftᵗ-bind (precise-typing-future W≼W′ V⊢)
precise-typing-future (future-imprecise W≼W′) V⊢ =
  precise-typing-future W≼W′ V⊢

imprecise-typing-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ A}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {V}
    (W≼W′ : Future W W′)
  → ⟨ Δᴵ , impreciseStore (core W) , [] ⟩ ⊢ V ⦂ A
  → ⟨ Δᴵ′ , impreciseStore (core W′) , [] ⟩
      ⊢ liftImpreciseTerm W≼W′ V ⦂ liftImpreciseTy W≼W′ A
imprecise-typing-future future-refl V⊢ = V⊢
imprecise-typing-future (future-paired W≼W′ related) V⊢ =
  typing-shiftᵗ-bind (imprecise-typing-future W≼W′ V⊢)
imprecise-typing-future (future-precise W≼W′ r★) V⊢ =
  imprecise-typing-future W≼W′ V⊢
imprecise-typing-future (future-imprecise W≼W′) V⊢ =
  typing-shiftᵗ-bind (imprecise-typing-future W≼W′ V⊢)

typed-endpoints-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → TypedEndpoints W p Vᴵ Vᴾ
  → TypedEndpoints W′ (liftCenterImprecision W≼W′ p)
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
typed-endpoints-future W≼W′ endpoints =
  typed-endpoints
    (liftImpreciseTy W≼W′ (impreciseType endpoints))
    (liftPreciseTy W≼W′ (preciseType endpoints))
    (trans (embedImprecise-lift W≼W′ (impreciseType endpoints))
      (cong (liftCenterTy W≼W′) (impreciseEmbedded endpoints)))
    (trans (embedPrecise-lift W≼W′ (preciseType endpoints))
      (cong (liftCenterTy W≼W′) (preciseEmbedded endpoints)))
    (imprecise-value-future W≼W′ (imprecise-value endpoints))
    (precise-value-future W≼W′ (precise-value endpoints))
    (imprecise-typing-future W≼W′ (imprecise-typed endpoints))
    (precise-typing-future W≼W′ (precise-typed endpoints))

value-imprecision-reindex : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Aᴾ′ Aᴵ′}
    {W : World Δᴾ Δᴵ Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (q : impEnv (core W) I.⊢ Aᴾ′ ⊑ Aᴵ′)
    {k Vᴵ Vᴾ}
  → Aᴾ ≡ Aᴾ′
  → Aᴵ ≡ Aᴵ′
  → ValueImprecision W q k Vᴵ Vᴾ
  → ValueImprecision W p k Vᴵ Vᴾ
value-imprecision-reindex p q refl refl related
  rewrite PI.⊑-unique q p = related

value-imprecision-local→center : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
    {k Vᴵ Vᴾ}
  → ValueImprecision W′ (liftLocalImprecision W≼W′ p) k Vᴵ Vᴾ
  → ValueImprecision W′ (liftCenterImprecision W≼W′ p) k Vᴵ Vᴾ
value-imprecision-local→center {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} W≼W′ p =
  value-imprecision-reindex (liftCenterImprecision W≼W′ p)
    (liftLocalImprecision W≼W′ p)
    (sym (embedPrecise-lift W≼W′ Aᴾ))
    (sym (embedImprecise-lift W≼W′ Aᴵ))

value-imprecision-center→local : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
    {k Vᴵ Vᴾ}
  → ValueImprecision W′ (liftCenterImprecision W≼W′ p) k Vᴵ Vᴾ
  → ValueImprecision W′ (liftLocalImprecision W≼W′ p) k Vᴵ Vᴾ
value-imprecision-center→local {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} W≼W′ p =
  value-imprecision-reindex (liftLocalImprecision W≼W′ p)
    (liftCenterImprecision W≼W′ p)
    (embedPrecise-lift W≼W′ Aᴾ)
    (embedImprecise-lift W≼W′ Aᴵ)

typed-endpoints-derivation-reindex : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    (p q : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ) {Vᴵ Vᴾ}
  → TypedEndpoints W p Vᴵ Vᴾ
  → TypedEndpoints W q Vᴵ Vᴾ
typed-endpoints-derivation-reindex p q endpoints
  rewrite PI.⊑-unique p q = endpoints

computations-related-reindex : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Aᴾ′ Aᴵ′}
    {W : World Δᴾ Δᴵ Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (q : impEnv (core W) I.⊢ Aᴾ′ ⊑ Aᴵ′)
    {k} {Mᴵ Mᴵ′ : Term Δᴵ} {Mᴾ Mᴾ′ : Term Δᴾ}
  → Aᴾ ≡ Aᴾ′
  → Aᴵ ≡ Aᴵ′
  → Mᴵ ≡ Mᴵ′
  → Mᴾ ≡ Mᴾ′
  → ComputationsRelated W (FutureValueRelation p) k Mᴵ Mᴾ
  → ComputationsRelated W (FutureValueRelation q) k Mᴵ′ Mᴾ′
computations-related-reindex p q refl refl refl refl related
  rewrite PI.⊑-unique p q = related

computations-related-post-bind-reindex : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾᵇ Δᴵᵇ Δᶜᵇ}
    {Aᴾ Aᴾ′ Aᴵ Aᴵ′ : Ty Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {bound : World Δᴾᵇ Δᴵᵇ Δᶜᵇ}
    {W≼B : Future W bound}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (q : impEnv (core W) I.⊢ Aᴾ′ ⊑ Aᴵ′)
    {k} {Mᴵ Mᴵ′ : Term Δᴵ} {Mᴾ Mᴾ′ : Term Δᴾ}
  → Aᴾ ≡ Aᴾ′
  → Aᴵ ≡ Aᴵ′
  → Mᴵ ≡ Mᴵ′
  → Mᴾ ≡ Mᴾ′
  → ComputationsRelated W (PostBindValueRelation W≼B p) k Mᴵ Mᴾ
  → ComputationsRelated W (PostBindValueRelation W≼B q) k Mᴵ′ Mᴾ′
computations-related-post-bind-reindex p q refl refl refl refl related
  rewrite PI.⊑-unique p q = related

right-universals-related-reindex : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Aᴾ′ Aᴵ′}
    {W : World Δᴾ Δᴵ Δᶜ} {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {k Vᴵ Vᴾ}
    (p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
    (q : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ′ ⊑ Aᴵ′)
  → Aᴾ ≡ Aᴾ′
  → Aᴵ ≡ Aᴵ′
  → RightUniversalsRelated W q Bᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W p Bᴾ Bᴵ k Vᴵ Vᴾ
right-universals-related-reindex p q refl refl related
  rewrite PI.⊑-unique q p = related

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
functions-related-future {k = zero} W≼W′ related = tt
functions-related-future {k = suc k} W≼W′ (head , tail) =
  (λ K W′≼K {Uᴵ} {Uᴾ} argument →
      let composite = future-trans W≼W′ W′≼K
          argument′ = value-imprecision-reindex
            (liftCenterImprecision composite _)
            (liftCenterImprecision W′≼K
              (liftCenterImprecision W≼W′ _))
            (liftCenterTy-trans W≼W′ W′≼K _)
            (liftCenterTy-trans W≼W′ W′≼K _) argument
      in computations-related-reindex
          (liftCenterImprecision composite _)
          (liftCenterImprecision W′≼K
            (liftCenterImprecision W≼W′ _))
          (liftCenterTy-trans W≼W′ W′≼K _)
          (liftCenterTy-trans W≼W′ W′≼K _)
          (cong (λ F → F · Uᴵ)
            (liftImpreciseTerm-trans W≼W′ W′≼K _))
          (cong (λ F → F · Uᴾ)
            (liftPreciseTerm-trans W≼W′ W′≼K _))
          (head K composite argument′)) ,
  functions-related-future W≼W′ tail

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
universals-related-future {k = zero} W≼W′ related = tt
universals-related-future {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {k = suc k}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    W≼W′ (head , tail) =
  (λ K W′≼K Rᴾ Rᴵ r s →
      let composite = future-trans W≼W′ W′≼K
          precise-result-trans = cong (λ C → C [ Rᴾ ]ᵗ)
            (liftPreciseBody-trans W≼W′ W′≼K Bᴾ)
          imprecise-result-trans = cong (λ C → C [ Rᴵ ]ᵗ)
            (liftImpreciseBody-trans W≼W′ W′≼K Bᴵ)
          s-composite = subst≡
            (λ L → L ⊑ᵂ⟨ core K ⟩
              liftImpreciseBody composite Bᴵ [ Rᴵ ]ᵗ)
            (sym precise-result-trans)
            (subst≡
              (λ R → liftPreciseBody W′≼K
                (liftPreciseBody W≼W′ Bᴾ) [ Rᴾ ]ᵗ
                ⊑ᵂ⟨ core K ⟩ R)
              (sym imprecise-result-trans) s)
      in computations-related-post-bind-reindex
          s-composite s
          (cong (embedPrecise (core K)) precise-result-trans)
          (cong (embedImprecise (core K)) imprecise-result-trans)
          (cong₂ (λ V B → V ⦂∀ B [ Rᴵ ])
            (liftImpreciseTerm-trans W≼W′ W′≼K Vᴵ)
            (liftImpreciseBody-trans W≼W′ W′≼K Bᴵ))
          (cong₂ (λ V B → V ⦂∀ B [ Rᴾ ])
            (liftPreciseTerm-trans W≼W′ W′≼K Vᴾ)
            (liftPreciseBody-trans W≼W′ W′≼K Bᴾ))
          (head K composite Rᴾ Rᴵ r s-composite)) ,
  universals-related-future {p = p} W≼W′ tail

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
right-universals-related-future {k = zero} W≼W′ head = head
right-universals-related-future {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {p = p}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {k = suc k}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    W≼W′ (head , tail) =
  (λ K W′≼K Rᴾ r★ s →
      let composite = future-trans W≼W′ W′≼K
          precise-result-trans = cong (λ C → C [ Rᴾ ]ᵗ)
            (liftPreciseBody-trans W≼W′ W′≼K Bᴾ)
          s-composite = subst≡
            (λ L → L ⊑ᵂ⟨ core K ⟩ liftImpreciseTy composite Bᴵ)
            (sym precise-result-trans)
            (subst≡
              (λ R → liftPreciseBody W′≼K
                (liftPreciseBody W≼W′ Bᴾ) [ Rᴾ ]ᵗ
                ⊑ᵂ⟨ core K ⟩ R)
              (sym (liftImpreciseTy-trans W≼W′ W′≼K Bᴵ)) s)
      in computations-related-post-bind-reindex
          s-composite s
          (cong (embedPrecise (core K)) precise-result-trans)
          (cong (embedImprecise (core K))
            (liftImpreciseTy-trans W≼W′ W′≼K Bᴵ))
          (liftImpreciseTerm-trans W≼W′ W′≼K Vᴵ)
          (cong₂ (λ V B → V ⦂∀ B [ Rᴾ ])
            (liftPreciseTerm-trans W≼W′ W′≼K Vᴾ)
            (liftPreciseBody-trans W≼W′ W′≼K Bᴾ))
          (head K composite Rᴾ r★ s-composite)) ,
  right-universals-related-future {p = p} {Bᴵ = Bᴵ} W≼W′ tail

precise-ground-type : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᴾ
  → Ty Δᴾ′
precise-ground-type future-refl G = G
precise-ground-type (future-paired W≼W′ related) G =
  renameᵗ (C.toRenameᵗ C.wk↪ᵗ) (precise-ground-type W≼W′ G)
precise-ground-type (future-precise W≼W′ r★) G =
  renameᵗ (C.toRenameᵗ C.wk↪ᵗ) (precise-ground-type W≼W′ G)
precise-ground-type (future-imprecise W≼W′) G =
  precise-ground-type W≼W′ G

imprecise-ground-type : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᴵ
  → Ty Δᴵ′
imprecise-ground-type future-refl G = G
imprecise-ground-type (future-paired W≼W′ related) G =
  renameᵗ (C.toRenameᵗ C.wk↪ᵗ) (imprecise-ground-type W≼W′ G)
imprecise-ground-type (future-precise W≼W′ r★) G =
  imprecise-ground-type W≼W′ G
imprecise-ground-type (future-imprecise W≼W′) G =
  renameᵗ (C.toRenameᵗ C.wk↪ᵗ) (imprecise-ground-type W≼W′ G)

precise-ground-type-eq : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (G : Ty Δᴾ)
  → precise-ground-type W≼W′ G ≡ liftPreciseTy W≼W′ G
precise-ground-type-eq future-refl G = refl
precise-ground-type-eq (future-paired W≼W′ related) G =
  trans (renameᵗ-cong (precise-ground-type W≼W′ G) toRename-wk-eq)
    (cong ⇑ᵗ (precise-ground-type-eq W≼W′ G))
precise-ground-type-eq (future-precise W≼W′ r★) G =
  trans (renameᵗ-cong (precise-ground-type W≼W′ G) toRename-wk-eq)
    (cong ⇑ᵗ (precise-ground-type-eq W≼W′ G))
precise-ground-type-eq (future-imprecise W≼W′) G =
  precise-ground-type-eq W≼W′ G

imprecise-ground-type-eq : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (G : Ty Δᴵ)
  → imprecise-ground-type W≼W′ G ≡ liftImpreciseTy W≼W′ G
imprecise-ground-type-eq future-refl G = refl
imprecise-ground-type-eq (future-paired W≼W′ related) G =
  trans (renameᵗ-cong (imprecise-ground-type W≼W′ G) toRename-wk-eq)
    (cong ⇑ᵗ (imprecise-ground-type-eq W≼W′ G))
imprecise-ground-type-eq (future-precise W≼W′ r★) G =
  imprecise-ground-type-eq W≼W′ G
imprecise-ground-type-eq (future-imprecise W≼W′) G =
  trans (renameᵗ-cong (imprecise-ground-type W≼W′ G) toRename-wk-eq)
    (cong ⇑ᵗ (imprecise-ground-type-eq W≼W′ G))

precise-ground-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ G}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → Ground G
  → Ground (precise-ground-type W≼W′ G)
precise-ground-future future-refl g = g
precise-ground-future (future-paired W≼W′ related) g =
  PC.renameGroundᵐ C.wk↪ᵗ (precise-ground-future W≼W′ g)
precise-ground-future (future-precise W≼W′ r★) g =
  PC.renameGroundᵐ C.wk↪ᵗ (precise-ground-future W≼W′ g)
precise-ground-future (future-imprecise W≼W′) g =
  precise-ground-future W≼W′ g

imprecise-ground-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ G}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → Ground G
  → Ground (imprecise-ground-type W≼W′ G)
imprecise-ground-future future-refl g = g
imprecise-ground-future (future-paired W≼W′ related) g =
  PC.renameGroundᵐ C.wk↪ᵗ (imprecise-ground-future W≼W′ g)
imprecise-ground-future (future-precise W≼W′ r★) g =
  imprecise-ground-future W≼W′ g
imprecise-ground-future (future-imprecise W≼W′) g =
  PC.renameGroundᵐ C.wk↪ᵗ (imprecise-ground-future W≼W′ g)

precise-consistency-env-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Env∼ Δᴾ
  → Env∼ Δᴾ′
precise-consistency-env-future future-refl μ = μ
precise-consistency-env-future (future-paired W≼W′ related) μ =
  C.renameEnv∼ C.wk↪ᵗ (precise-consistency-env-future W≼W′ μ)
precise-consistency-env-future (future-precise W≼W′ r★) μ =
  C.renameEnv∼ C.wk↪ᵗ (precise-consistency-env-future W≼W′ μ)
precise-consistency-env-future (future-imprecise W≼W′) μ =
  precise-consistency-env-future W≼W′ μ

imprecise-consistency-env-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Env∼ Δᴵ
  → Env∼ Δᴵ′
imprecise-consistency-env-future future-refl μ = μ
imprecise-consistency-env-future (future-paired W≼W′ related) μ =
  C.renameEnv∼ C.wk↪ᵗ (imprecise-consistency-env-future W≼W′ μ)
imprecise-consistency-env-future (future-precise W≼W′ r★) μ =
  imprecise-consistency-env-future W≼W′ μ
imprecise-consistency-env-future (future-imprecise W≼W′) μ =
  C.renameEnv∼ C.wk↪ᵗ (imprecise-consistency-env-future W≼W′ μ)

precise-ground-to-star-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ G μ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → μ ⊢ G ∼★
  → precise-consistency-env-future W≼W′ μ ⊢
      precise-ground-type W≼W′ G ∼★
precise-ground-to-star-future future-refl G∼★ = G∼★
precise-ground-to-star-future (future-paired W≼W′ related) G∼★ =
  PC.rename∼★ᵐ C.wk↪ᵗ (precise-ground-to-star-future W≼W′ G∼★)
precise-ground-to-star-future (future-precise W≼W′ r★) G∼★ =
  PC.rename∼★ᵐ C.wk↪ᵗ (precise-ground-to-star-future W≼W′ G∼★)
precise-ground-to-star-future (future-imprecise W≼W′) G∼★ =
  precise-ground-to-star-future W≼W′ G∼★

imprecise-ground-to-star-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ G μ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → μ ⊢ G ∼★
  → imprecise-consistency-env-future W≼W′ μ ⊢
      imprecise-ground-type W≼W′ G ∼★
imprecise-ground-to-star-future future-refl G∼★ = G∼★
imprecise-ground-to-star-future
    (future-paired W≼W′ related) G∼★ =
  PC.rename∼★ᵐ C.wk↪ᵗ
    (imprecise-ground-to-star-future W≼W′ G∼★)
imprecise-ground-to-star-future (future-precise W≼W′ r★) G∼★ =
  imprecise-ground-to-star-future W≼W′ G∼★
imprecise-ground-to-star-future (future-imprecise W≼W′) G∼★ =
  PC.rename∼★ᵐ C.wk↪ᵗ
    (imprecise-ground-to-star-future W≼W′ G∼★)

rename-ground-injection : ∀ {Δ G μ} (g : Ground {Δ} G)
    (G∼★ : μ ⊢ G ∼★)
  → C.renameᵐᶜ C.wk↪ᵗ (groundInjection g G∼★)
      ≡ groundInjection (PC.renameGroundᵐ C.wk↪ᵗ g)
          (PC.rename∼★ᵐ C.wk↪ᵗ G∼★)
rename-ground-injection ★⇒★ C.⇒∼★ = refl
rename-ground-injection (‵ ι) C.ι∼★ = refl
rename-ground-injection (＇ X) (C.X∼★ᵍ eq) = refl
rename-ground-injection (＇ X) (C.X∼★ᶜ eq) = refl
rename-ground-injection ∀★ C.∀∼★ = refl

precise-injection-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ G μ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (U : Term Δᴾ)
    (g : Ground G) (G∼★ : μ ⊢ G ∼★)
  → liftPreciseTerm W≼W′ (U ⟨ groundInjection g G∼★ ⟩)
      ≡ liftPreciseTerm W≼W′ U
        ⟨ groundInjection (precise-ground-future W≼W′ g)
          (precise-ground-to-star-future W≼W′ G∼★) ⟩
precise-injection-future future-refl U g G∼★ = refl
precise-injection-future (future-paired W≼W′ related) U g G∼★ =
  trans (cong ⇑ᵗᵐ (precise-injection-future W≼W′ U g G∼★))
    (cong (λ c → ⇑ᵗᵐ (liftPreciseTerm W≼W′ U) ⟨ c ⟩)
      (rename-ground-injection (precise-ground-future W≼W′ g)
        (precise-ground-to-star-future W≼W′ G∼★)))
precise-injection-future (future-precise W≼W′ r★) U g G∼★ =
  trans (cong ⇑ᵗᵐ (precise-injection-future W≼W′ U g G∼★))
    (cong (λ c → ⇑ᵗᵐ (liftPreciseTerm W≼W′ U) ⟨ c ⟩)
      (rename-ground-injection (precise-ground-future W≼W′ g)
        (precise-ground-to-star-future W≼W′ G∼★)))
precise-injection-future (future-imprecise W≼W′) U g G∼★ =
  precise-injection-future W≼W′ U g G∼★

imprecise-injection-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ G μ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (U : Term Δᴵ)
    (g : Ground G) (G∼★ : μ ⊢ G ∼★)
  → liftImpreciseTerm W≼W′ (U ⟨ groundInjection g G∼★ ⟩)
      ≡ liftImpreciseTerm W≼W′ U
        ⟨ groundInjection (imprecise-ground-future W≼W′ g)
          (imprecise-ground-to-star-future W≼W′ G∼★) ⟩
imprecise-injection-future future-refl U g G∼★ = refl
imprecise-injection-future
    (future-paired W≼W′ related) U g G∼★ =
  trans (cong ⇑ᵗᵐ (imprecise-injection-future W≼W′ U g G∼★))
    (cong (λ c → ⇑ᵗᵐ (liftImpreciseTerm W≼W′ U) ⟨ c ⟩)
      (rename-ground-injection (imprecise-ground-future W≼W′ g)
        (imprecise-ground-to-star-future W≼W′ G∼★)))
imprecise-injection-future (future-precise W≼W′ r★) U g G∼★ =
  imprecise-injection-future W≼W′ U g G∼★
imprecise-injection-future (future-imprecise W≼W′) U g G∼★ =
  trans (cong ⇑ᵗᵐ (imprecise-injection-future W≼W′ U g G∼★))
    (cong (λ c → ⇑ᵗᵐ (liftImpreciseTerm W≼W′ U) ⟨ c ⟩)
      (rename-ground-injection (imprecise-ground-future W≼W′ g)
        (imprecise-ground-to-star-future W≼W′ G∼★)))

local-imprecision-reindex : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Aᴾ′ Aᴵ′} {W : World Δᴾ Δᴵ Δᶜ}
  → Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ
  → Aᴾ′ ≡ Aᴾ
  → Aᴵ′ ≡ Aᴵ
  → Aᴾ′ ⊑ᵂ⟨ core W ⟩ Aᴵ′
local-imprecision-reindex p refl refl = p

dynamic-payload-shape-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Vᴵ Vᴾ} (W≼W′ : Future W W′)
  → DynamicPayloadShape W Vᴵ Vᴾ
  → DynamicPayloadShape W′ (liftImpreciseTerm W≼W′ Vᴵ)
      (liftPreciseTerm W≼W′ Vᴾ)
dynamic-payload-shape-future {W′ = W′} W≼W′ shape =
  dynamic-payload-shape
    (precise-ground-type W≼W′ (precise-ground shape))
    (imprecise-ground-type W≼W′ (imprecise-ground shape))
    (precise-ground-future W≼W′ (precise-ground-proof shape))
    (imprecise-ground-future W≼W′ (imprecise-ground-proof shape))
    (precise-consistency-env-future W≼W′
      (precise-consistency-env shape))
    (imprecise-consistency-env-future W≼W′
      (imprecise-consistency-env shape))
    (precise-ground-to-star-future W≼W′
      (precise-ground-to-star shape))
    (imprecise-ground-to-star-future W≼W′
      (imprecise-ground-to-star shape))
    (liftPreciseTerm W≼W′ (dynamic-precise-payload shape))
    (liftImpreciseTerm W≼W′ (dynamic-imprecise-payload shape))
    (trans (cong (liftImpreciseTerm W≼W′)
        (dynamic-imprecise-shape shape))
      (imprecise-injection-future W≼W′
        (dynamic-imprecise-payload shape)
        (imprecise-ground-proof shape)
        (imprecise-ground-to-star shape)))
    (trans (cong (liftPreciseTerm W≼W′)
        (dynamic-precise-shape shape))
      (precise-injection-future W≼W′
        (dynamic-precise-payload shape)
        (precise-ground-proof shape)
        (precise-ground-to-star shape)))
    (local-imprecision-reindex {W = W′}
      (liftLocalImprecision W≼W′ (payload-imprecision shape))
      (precise-ground-type-eq W≼W′ (precise-ground shape))
      (imprecise-ground-type-eq W≼W′ (imprecise-ground shape)))

------------------------------------------------------------------------
-- Slot relations through futures
------------------------------------------------------------------------

-- A payload map carries the payload relation of a world to the payload
-- relation of a future world on lifted payloads; the value relation at a
-- lower index supplies it during the monotonicity induction.

PayloadFutureMap : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → PayloadRelation (core W)
  → PayloadRelation (core W′)
  → Set₁
PayloadFutureMap {Δᶜ = Δᶜ} {W = W} W≼W′ ℛ ℛ′ =
  ∀ {Aᴾ Aᴵ : Ty Δᶜ} {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {U U′}
  → ℛ p U U′
  → ℛ′ (liftCenterImprecision W≼W′ p)
      (liftImpreciseTerm W≼W′ U) (liftPreciseTerm W≼W′ U′)

-- A payload relation that depends on its derivation index only through
-- the endpoint types.

PayloadReindex : ∀ {Δᴾ Δᴵ Δᶜ} (W : CoreWorld Δᴾ Δᴵ Δᶜ)
  → PayloadRelation W → Set₁
PayloadReindex {Δᶜ = Δᶜ} W ℛ =
  ∀ {Aᴾ Aᴵ Aᴾ′ Aᴵ′ : Ty Δᶜ}
    (p : impEnv W I.⊢ Aᴾ ⊑ Aᴵ) (q : impEnv W I.⊢ Aᴾ′ ⊑ Aᴵ′)
    {U U′}
  → Aᴾ ≡ Aᴾ′ → Aᴵ ≡ Aᴵ′
  → ℛ p U U′ → ℛ q U U′

value-payload-reindex : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} {k}
  → PayloadReindex (core W) (ValueImprecisionᵏ k W)
value-payload-reindex p q refl refl related
  rewrite PI.⊑-unique p q = related

paired-holds-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ mode mode′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {ℛ : PayloadRelation (core W)} {ℛ′ : PayloadRelation (core W′)}
    {Z : TyVar Δᶜ} {Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → PayloadFutureMap W≼W′ ℛ ℛ′
  → PayloadReindex (core W′) ℛ′
  → {e : SemanticEntry (core W) Z mode}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → EntryLift W≼W′ e e′
  → PairedAtomHolds ℛ e Vᴵ Vᴾ
  → PairedAtomHolds ℛ′ e′
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
paired-holds-lift {W′ = W′} W≼W′ f reindex
    (lift-paired {a = a} {a′ = a′} eqᴾ eqᴵ repᴾ repᴵ)
    (atom-holds Uᴵ Uᴾ refl refl related) =
  atom-holds (liftImpreciseTerm W≼W′ Uᴵ) (liftPreciseTerm W≼W′ Uᴾ)
    (trans (liftImpreciseTerm-sealed W≼W′ Uᴵ _ _)
      (sym (cong₂ (λ Y T → liftImpreciseTerm W≼W′ Uᴵ ↓ Conversion.seal Y T)
        eqᴵ repᴵ)))
    (trans (liftPreciseTerm-sealed W≼W′ Uᴾ _ _)
      (sym (cong₂ (λ Y T → liftPreciseTerm W≼W′ Uᴾ ↓ Conversion.seal Y T)
        eqᴾ repᴾ)))
    (reindex (liftCenterImprecision W≼W′ (rep-related a)) (rep-related a′)
      (trans (sym (embedPrecise-lift W≼W′ (preciseRep a)))
        (cong (embedPrecise (core W′)) (sym repᴾ)))
      (trans (sym (embedImprecise-lift W≼W′ (impreciseRep a)))
        (cong (embedImprecise (core W′)) (sym repᴵ)))
      (f related))
paired-holds-lift W≼W′ f reindex (lift-dynamic eqᴾ repᴾ) (Level.lift ())
paired-holds-lift W≼W′ f reindex lift-target (Level.lift ())

paired-holds-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {ℛ : PayloadRelation (core W)} {ℛ′ : PayloadRelation (core W′)}
    {Z : TyVar Δᶜ} {Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → PayloadFutureMap W≼W′ ℛ ℛ′
  → PayloadReindex (core W′) ℛ′
  → PairedAtomHolds ℛ (semanticEntry W Z) Vᴵ Vᴾ
  → PairedAtomHolds ℛ′ (semanticEntry W′ (liftCenterVariable W≼W′ Z))
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
paired-holds-future {Z = Z} W≼W′ f reindex holds =
  paired-holds-lift W≼W′ f reindex (entry-future W≼W′ Z) holds

dynamic-holds-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ mode mode′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {ℛ : PayloadRelation (core W)} {ℛ′ : PayloadRelation (core W′)}
    {Z : TyVar Δᶜ} {Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → PayloadFutureMap W≼W′ ℛ ℛ′
  → PayloadReindex (core W′) ℛ′
  → {e : SemanticEntry (core W) Z mode}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → EntryLift W≼W′ e e′
  → (eq : mode ≡ I.X⊑★) (eq′ : mode′ ≡ I.X⊑★)
  → DynamicAtomHolds ℛ e eq Vᴵ Vᴾ
  → DynamicAtomHolds ℛ′ e′ eq′
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
dynamic-holds-lift W≼W′ f reindex (lift-paired _ _ _ _) eq eq′
    (Level.lift ())
dynamic-holds-lift {W′ = W′} W≼W′ f reindex
    (lift-dynamic {a = a} {a′ = a′} eqᴾ repᴾ) refl refl
    (dynamic-holds Uᴾ refl related) =
  dynamic-holds (liftPreciseTerm W≼W′ Uᴾ)
    (trans (liftPreciseTerm-sealed W≼W′ Uᴾ _ _)
      (sym (cong₂ (λ Y T → liftPreciseTerm W≼W′ Uᴾ ↓ Conversion.seal Y T)
        eqᴾ repᴾ)))
    (reindex (liftCenterImprecision W≼W′ (dynamicRep-related a))
      (dynamicRep-related a′)
      (trans (sym (embedPrecise-lift W≼W′ (dynamicRep a)))
        (cong (embedPrecise (core W′)) (sym repᴾ)))
      (liftCenterTy-star W≼W′)
      (f related))
dynamic-holds-lift W≼W′ f reindex lift-target refl refl (Level.lift ())

dynamic-holds-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {ℛ : PayloadRelation (core W)} {ℛ′ : PayloadRelation (core W′)}
    {Z : TyVar Δᶜ} {Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → PayloadFutureMap W≼W′ ℛ ℛ′
  → PayloadReindex (core W′) ℛ′
  → (eq : impEnv (core W) Z ≡ I.X⊑★)
  → DynamicAtomHolds ℛ (semanticEntry W Z) eq Vᴵ Vᴾ
  → DynamicAtomHolds ℛ′ (semanticEntry W′ (liftCenterVariable W≼W′ Z))
      (trans (liftCenterMode W≼W′ Z) eq)
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
dynamic-holds-future {Z = Z} W≼W′ f reindex eq holds =
  dynamic-holds-lift W≼W′ f reindex (entry-future W≼W′ Z) eq
    (trans (liftCenterMode W≼W′ Z) eq) holds

dynamic-atom-tag-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {ℛ : PayloadRelation (core W)} {ℛ′ : PayloadRelation (core W′)}
    {Vᴵ Vᴾ} (W≼W′ : Future W W′)
  → PayloadFutureMap W≼W′ ℛ ℛ′
  → PayloadReindex (core W′) ℛ′
  → DynamicAtomTagRelated W ℛ Vᴵ Vᴾ
  → DynamicAtomTagRelated W′ ℛ′
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
dynamic-atom-tag-future {W′ = W′} W≼W′ f reindex related =
  dynamic-atom-tag-related
    (liftCenterVariable W≼W′ (dynamic-center-variable related))
    mode′
    (precise-ground-type W≼W′ (atom-precise-ground related))
    (precise-ground-future W≼W′
      (atom-precise-ground-proof related))
    ground-center′
    (precise-consistency-env-future W≼W′
      (atom-precise-consistency-env related))
    (precise-ground-to-star-future W≼W′
      (atom-precise-ground-to-star related))
    (liftPreciseTerm W≼W′ (atom-precise-payload related))
    tag-shape′
    (dynamic-holds-future W≼W′ f reindex (dynamic-mode related)
      (atom-relation-holds related))
  where
  mode′ = trans
    (liftCenterMode W≼W′ (dynamic-center-variable related))
    (dynamic-mode related)

  ground-center′ = trans
    (cong (embedPrecise (core W′))
      (precise-ground-type-eq W≼W′ (atom-precise-ground related)))
    (trans (embedPrecise-lift W≼W′ (atom-precise-ground related))
      (trans (cong (liftCenterTy W≼W′)
          (atom-precise-ground-center related))
        (liftCenterTy-variable W≼W′
          (dynamic-center-variable related))))

  tag-shape′ = trans
    (cong (liftPreciseTerm W≼W′) (atom-precise-tag-shape related))
    (precise-injection-future W≼W′ (atom-precise-payload related)
      (atom-precise-ground-proof related)
      (atom-precise-ground-to-star related))

aligned-dynamic-atom-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {ℛ : PayloadRelation (core W)} {ℛ′ : PayloadRelation (core W′)}
    {Z Vᴵ Vᴾ} (W≼W′ : Future W W′)
  → PayloadFutureMap W≼W′ ℛ ℛ′
  → PayloadReindex (core W′) ℛ′
  → AlignedDynamicAtomRelated W ℛ Z Vᴵ Vᴾ
  → AlignedDynamicAtomRelated W′ ℛ′ (liftCenterVariable W≼W′ Z)
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
aligned-dynamic-atom-future {W′ = W′} W≼W′ f reindex related =
  aligned-dynamic-atom-related
    (imprecise-ground-type W≼W′ (aligned-imprecise-ground related))
    (imprecise-ground-future W≼W′
      (aligned-imprecise-ground-proof related))
    ground-center′
    (imprecise-consistency-env-future W≼W′
      (aligned-imprecise-consistency-env related))
    (imprecise-ground-to-star-future W≼W′
      (aligned-imprecise-ground-to-star related))
    (liftImpreciseTerm W≼W′ (aligned-imprecise-payload related))
    tag-shape′
    (paired-holds-future W≼W′ f reindex
      (aligned-atom-relation-holds related))
  where
  ground-center′ = trans
    (cong (embedImprecise (core W′))
      (imprecise-ground-type-eq W≼W′
        (aligned-imprecise-ground related)))
    (trans (embedImprecise-lift W≼W′
        (aligned-imprecise-ground related))
      (trans (cong (liftCenterTy W≼W′)
          (aligned-imprecise-ground-center related))
        (liftCenterTy-variable W≼W′ _)))

  tag-shape′ = trans
    (cong (liftImpreciseTerm W≼W′)
      (aligned-imprecise-tag-shape related))
    (imprecise-injection-future W≼W′
      (aligned-imprecise-payload related)
      (aligned-imprecise-ground-proof related)
      (aligned-imprecise-ground-to-star related))

right-dynamic-payload-shape-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Vᴵ} (W≼W′ : Future W W′)
  → RightDynamicPayloadShape W Aᴾ Vᴵ
  → RightDynamicPayloadShape W′ (liftCenterTy W≼W′ Aᴾ)
      (liftImpreciseTerm W≼W′ Vᴵ)
right-dynamic-payload-shape-future {W′ = W′} W≼W′ shape =
  let ground-eq = trans
        (cong (embedImprecise (core W′))
          (imprecise-ground-type-eq W≼W′
            (right-imprecise-ground shape)))
        (embedImprecise-lift W≼W′ (right-imprecise-ground shape))
      payload-imprecision′ = subst≡
        (λ R → impEnv (core W′) I.⊢
          liftCenterTy W≼W′ _ ⊑ R)
        (sym ground-eq)
        (liftCenterImprecision W≼W′
          (right-payload-imprecision shape))
  in right-dynamic-payload-shape
       (imprecise-ground-type W≼W′ (right-imprecise-ground shape))
       (imprecise-ground-future W≼W′
         (right-imprecise-ground-proof shape))
       (imprecise-consistency-env-future W≼W′
         (right-imprecise-consistency-env shape))
       (imprecise-ground-to-star-future W≼W′
         (right-imprecise-ground-to-star shape))
       (liftImpreciseTerm W≼W′
         (right-dynamic-imprecise-payload shape))
       (trans (cong (liftImpreciseTerm W≼W′)
          (right-dynamic-imprecise-shape shape))
         (imprecise-injection-future W≼W′
           (right-dynamic-imprecise-payload shape)
           (right-imprecise-ground-proof shape)
           (right-imprecise-ground-to-star shape)))
       payload-imprecision′

right-dynamic-payload-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ k}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Vᴵ Vᴾ} (W≼W′ : Future W W′)
    (shape : RightDynamicPayloadShape W Aᴾ Vᴵ)
  → ValueImprecision W′
      (liftCenterImprecision W≼W′ (right-payload-imprecision shape)) k
      (liftImpreciseTerm W≼W′
        (right-dynamic-imprecise-payload shape))
      (liftPreciseTerm W≼W′ Vᴾ)
  → RightDynamicPayloadRelated W′ (liftCenterTy W≼W′ Aᴾ) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
right-dynamic-payload-future {W′ = W′} W≼W′ shape payload =
  let shape′ = right-dynamic-payload-shape-future W≼W′ shape
      ground-eq = trans
        (cong (embedImprecise (core W′))
          (imprecise-ground-type-eq W≼W′
            (right-imprecise-ground shape)))
        (embedImprecise-lift W≼W′ (right-imprecise-ground shape))
      payload′ = value-imprecision-reindex
        (right-payload-imprecision shape′)
        (liftCenterImprecision W≼W′
          (right-payload-imprecision shape))
        refl ground-eq payload
  in shape′ , payload′

lift-precise-constant : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) κ
  → liftPreciseTerm W≼W′ ($ κ) ≡ $ κ
lift-precise-constant future-refl κ = refl
lift-precise-constant (future-paired W≼W′ related) κ
  rewrite lift-precise-constant W≼W′ κ = refl
lift-precise-constant (future-precise W≼W′ r★) κ
  rewrite lift-precise-constant W≼W′ κ = refl
lift-precise-constant (future-imprecise W≼W′) κ =
  lift-precise-constant W≼W′ κ

lift-imprecise-constant : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) κ
  → liftImpreciseTerm W≼W′ ($ κ) ≡ $ κ
lift-imprecise-constant future-refl κ = refl
lift-imprecise-constant (future-paired W≼W′ related) κ
  rewrite lift-imprecise-constant W≼W′ κ = refl
lift-imprecise-constant (future-precise W≼W′ r★) κ =
  lift-imprecise-constant W≼W′ κ
lift-imprecise-constant (future-imprecise W≼W′) κ
  rewrite lift-imprecise-constant W≼W′ κ = refl

same-base-value-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ ι Vᴵ Vᴾ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → SameBaseValue ι Vᴵ Vᴾ
  → SameBaseValue ι (liftImpreciseTerm W≼W′ Vᴵ)
      (liftPreciseTerm W≼W′ Vᴾ)
same-base-value-future W≼W′ (same-natural n)
  rewrite lift-imprecise-constant W≼W′ (Primitives.κℕ n)
        | lift-precise-constant W≼W′ (Primitives.κℕ n) =
  same-natural n
same-base-value-future W≼W′ (same-boolean b)
  rewrite lift-imprecise-constant W≼W′ (Primitives.κ𝔹 b)
        | lift-precise-constant W≼W′ (Primitives.κ𝔹 b) =
  same-boolean b

paired-future : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → Future W (pairedBindWorld W Rᴾ Rᴵ r)
paired-future W r = future-paired future-refl r

precise-future : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) {Rᴾ : Ty Δᴾ}
    (r : impEnv (core W) I.⊢ embedPrecise (core W) Rᴾ ⊑ ★)
  → Future W (preciseBindWorld W Rᴾ r)
precise-future W r = future-precise future-refl r

imprecise-future : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (Rᴵ : Ty Δᴵ)
  → Future W (impreciseBindWorld W Rᴵ)
imprecise-future W Rᴵ = future-imprecise future-refl

-- Termination note: the `X⊑★` dynamic case recurses at the same step
-- index into the slot's representation imprecision; well-founded by
-- allocation order (`dynamicFresh`; see LR-narrow/LogicalRelation.agda).
{-# TERMINATING #-}
value-imprecision-paired : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Rᴾ Rᴵ}
    (W : World Δᴾ Δᴵ Δᶜ)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k Vᴵ Vᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision (pairedBindWorld W Rᴾ Rᴵ r)
      (liftCenterImprecision (paired-future W r) p) k
      (liftImpreciseTerm (paired-future W r) Vᴵ)
      (liftPreciseTerm (paired-future W r) Vᴾ)
value-imprecision-paired W r {p = I.∀⊑ nonvar occurs p} {k = zero}
    endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.★⊑★} {k = zero} endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.ι⊑ι} {k = zero} endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.X⊑X} {k = zero} endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.⇒⊑⇒ p q} {k = zero}
    endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.∀⊑∀ p} {k = zero}
    endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.⇒⊑★ p q} {k = zero}
    endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.ι⊑★} {k = zero} endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.X⊑★ eq} {k = zero}
    endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.∀★⊑★} {k = zero}
    endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.∀⊑★ nonstar p}
    {k = zero} endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.bot-elim} {k = zero}
    endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.bot⊑★} {k = zero}
    endpoints =
  typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} W r
    {p = I.★⊑★} {k = suc k}
    (endpoints , inj₁ (shape , payload)) =
  let step = paired-future W r
      shape′ = dynamic-payload-shape-future step shape
      payload′ = value-imprecision-paired W r payload
      precise-eq = trans
        (cong (embedPrecise (core (pairedBindWorld W Rᴾ Rᴵ r)))
          (precise-ground-type-eq step (precise-ground shape)))
        (embedPrecise-lift step (precise-ground shape))
      imprecise-eq = trans
        (cong (embedImprecise (core (pairedBindWorld W Rᴾ Rᴵ r)))
          (imprecise-ground-type-eq step (imprecise-ground shape)))
        (embedImprecise-lift step (imprecise-ground shape))
      related′ = value-imprecision-reindex
        (payload-imprecision shape′)
        (liftCenterImprecision step (payload-imprecision shape))
        precise-eq imprecise-eq payload′
  in typed-endpoints-future step endpoints , inj₁ (shape′ , related′)
value-imprecision-paired W r {p = I.★⊑★} {k = suc k}
    (endpoints , inj₂ related) =
  let step = paired-future W r
  in typed-endpoints-future step endpoints ,
     inj₂ (dynamic-atom-tag-future step
       (λ {p = p} rel →
         value-imprecision-paired W r {p = p} {k = suc k} rel)
       value-payload-reindex related)
value-imprecision-paired W r {p = I.ι⊑ι} {k = suc k}
    (endpoints , same) =
  typed-endpoints-future (paired-future W r) endpoints ,
  same-base-value-future (paired-future W r) same
value-imprecision-paired W r {p = I.X⊑X} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (paired-future W r) endpoints ,
  paired-holds-future (paired-future W r)
    (λ {p = p} rel → value-imprecision-paired W r {p = p} {k = k} rel)
    value-payload-reindex related
value-imprecision-paired W r {p = I.⇒⊑⇒ p q} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (paired-future W r) endpoints ,
  functions-related-future (paired-future W r) related
value-imprecision-paired W r
    {p = I.∀⊑∀ {A = Aᴾ} {B = Aᴵ} p} {k = suc k}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , related) =
  let step = paired-future W r
      lifted = liftCenterImprecision step (I.∀⊑∀ p)
      structural = I.∀⊑∀ (liftCenterBodyImprecision step p)
      structural-endpoints = typed-endpoints-derivation-reindex
        lifted structural (typed-endpoints-future step endpoints)
      structural-related =
        structural-endpoints ,
        liftPreciseBody step Bᴾ , liftImpreciseBody step Bᴵ ,
        trans (embedPrecise-lift step (`∀ Bᴾ))
          (cong (liftCenterTy step) eqᴾ) ,
        trans (embedImprecise-lift step (`∀ Bᴵ))
          (cong (liftCenterTy step) eqᴵ) ,
        universals-related-future {p = p} step related
  in value-imprecision-reindex lifted structural {suc k} refl refl
       structural-related
value-imprecision-paired W r {p = I.⇒⊑★ p q} {k = suc k}
    (endpoints , shape , payload) =
  let step = paired-future W r
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-paired W r payload)
value-imprecision-paired W r {p = I.ι⊑★} {k = suc k}
    (endpoints , shape , payload) =
  let step = paired-future W r
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-paired W r payload)
value-imprecision-paired W r {p = I.X⊑★ eq} {k = suc k}
    (endpoints , inj₁ related) =
  typed-endpoints-future (paired-future W r) endpoints ,
  inj₁ (dynamic-holds-future (paired-future W r)
    (λ {p = p} rel →
      value-imprecision-paired W r {p = p} {k = suc k} rel)
    value-payload-reindex eq related)
value-imprecision-paired W r {p = I.X⊑★ eq} {k = suc k}
    (endpoints , inj₂ related) =
  typed-endpoints-future (paired-future W r) endpoints ,
  inj₂ (aligned-dynamic-atom-future (paired-future W r)
    (λ {p = p} rel → value-imprecision-paired W r {p = p} {k = k} rel)
    value-payload-reindex related)
value-imprecision-paired W r
    {p = I.∀⊑ {A = Aᴾ} {B = Aᴵ} nonvar occurs p} {k = suc k}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , related) =
  let step = paired-future W r
      lifted = liftCenterImprecision step
        (I.∀⊑ nonvar occurs p)
      p-lifted = liftCenterDynamicBodyImprecision step p
      p-structural =
        subst≡
          (λ T → I.instᵐ (impEnv (core (pairedBindWorld W _ _ r)))
            I.⊢ liftCenterBody step _ ⊑ T)
          (renameᵗ-shift Fin.suc Aᴵ) p-lifted
      related-structural = right-universals-related-reindex
        p-structural p-lifted refl (sym (renameᵗ-shift Fin.suc Aᴵ))
        (right-universals-related-future {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} step related)
      structural = I.∀⊑
        (renameNonVar (extᵗ Fin.suc) nonvar)
        (IC.rename-occurs (extᵗ Fin.suc)
          (IC.ext-injective IC.fin-suc-injective) occurs)
        p-structural
      structural-endpoints = typed-endpoints-derivation-reindex
        lifted structural (typed-endpoints-future step endpoints)
      structural-related = structural-endpoints ,
        liftPreciseBody step Bᴾ , liftImpreciseTy step Bᴵ ,
        trans (embedPrecise-lift step (`∀ Bᴾ))
          (cong (liftCenterTy step) eqᴾ) ,
        trans (embedImprecise-lift step Bᴵ)
          (cong (liftCenterTy step) eqᴵ) ,
        related-structural
  in value-imprecision-reindex lifted structural {suc k} refl refl
       structural-related
value-imprecision-paired W r {p = I.∀★⊑★} {k = suc k}
    (endpoints , shape , payload) =
  let step = paired-future W r
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-paired W r payload)
value-imprecision-paired W r
    {p = I.∀⊑★ nonstar p} {k = suc k}
    (endpoints , shape , payload) =
  let step = paired-future W r
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-paired W r payload)
value-imprecision-paired W r {p = I.bot-elim} {k = suc k}
    endpoints = typed-endpoints-future (paired-future W r) endpoints
value-imprecision-paired W r {p = I.bot⊑★} {k = suc k}
    endpoints = typed-endpoints-future (paired-future W r) endpoints

-- Termination note: the `X⊑★` dynamic case recurses at the same step
-- index into the slot's representation imprecision; well-founded by
-- allocation order (`dynamicFresh`; see LR-narrow/LogicalRelation.agda).
{-# TERMINATING #-}
value-imprecision-precise : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Rᴾ}
    (W : World Δᴾ Δᴵ Δᶜ)
    (r : impEnv (core W) I.⊢ embedPrecise (core W) Rᴾ ⊑ ★)
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k Vᴵ Vᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision (preciseBindWorld W Rᴾ r)
      (liftCenterImprecision (precise-future W r) p) k
      (liftImpreciseTerm (precise-future W r) Vᴵ)
      (liftPreciseTerm (precise-future W r) Vᴾ)
value-imprecision-precise W r {p = I.∀⊑ nonvar occurs p} {k = zero}
    endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.★⊑★} {k = zero} endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.ι⊑ι} {k = zero} endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.X⊑X} {k = zero} endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.⇒⊑⇒ p q} {k = zero}
    endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.∀⊑∀ p} {k = zero}
    endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.⇒⊑★ p q} {k = zero}
    endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.ι⊑★} {k = zero} endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.X⊑★ eq} {k = zero}
    endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.∀★⊑★} {k = zero}
    endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.∀⊑★ nonstar p}
    {k = zero} endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.bot-elim} {k = zero}
    endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.bot⊑★} {k = zero}
    endpoints =
  typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise {Rᴾ = Rᴾ} W r
    {p = I.★⊑★} {k = suc k}
    (endpoints , inj₁ (shape , payload)) =
  let step = precise-future W r
      shape′ = dynamic-payload-shape-future step shape
      payload′ = value-imprecision-precise W r payload
      precise-eq = trans
        (cong (embedPrecise (core (preciseBindWorld W Rᴾ r)))
          (precise-ground-type-eq step (precise-ground shape)))
        (embedPrecise-lift step (precise-ground shape))
      imprecise-eq = trans
        (cong (embedImprecise (core (preciseBindWorld W Rᴾ r)))
          (imprecise-ground-type-eq step (imprecise-ground shape)))
        (embedImprecise-lift step (imprecise-ground shape))
      related′ = value-imprecision-reindex
        (payload-imprecision shape′)
        (liftCenterImprecision step (payload-imprecision shape))
        precise-eq imprecise-eq payload′
  in typed-endpoints-future step endpoints , inj₁ (shape′ , related′)
value-imprecision-precise W r {p = I.★⊑★} {k = suc k}
    (endpoints , inj₂ related) =
  let step = precise-future W r
  in typed-endpoints-future step endpoints ,
     inj₂ (dynamic-atom-tag-future step
       (λ {p = p} rel →
         value-imprecision-precise W r {p = p} {k = suc k} rel)
       value-payload-reindex related)
value-imprecision-precise W r {p = I.ι⊑ι} {k = suc k}
    (endpoints , same) =
  typed-endpoints-future (precise-future W r) endpoints ,
  same-base-value-future (precise-future W r) same
value-imprecision-precise W r {p = I.X⊑X} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (precise-future W r) endpoints ,
  paired-holds-future (precise-future W r)
    (λ {p = p} rel → value-imprecision-precise W r {p = p} {k = k} rel)
    value-payload-reindex related
value-imprecision-precise W r {p = I.⇒⊑⇒ p q} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (precise-future W r) endpoints ,
  functions-related-future (precise-future W r) related
value-imprecision-precise W r
    {p = I.∀⊑∀ {A = Aᴾ} {B = Aᴵ} p} {k = suc k}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , related) =
  let step = precise-future W r
      lifted = liftCenterImprecision step (I.∀⊑∀ p)
      structural = I.∀⊑∀ (liftCenterBodyImprecision step p)
      structural-endpoints = typed-endpoints-derivation-reindex
        lifted structural (typed-endpoints-future step endpoints)
      structural-related = structural-endpoints ,
        liftPreciseBody step Bᴾ , liftImpreciseBody step Bᴵ ,
        trans (embedPrecise-lift step (`∀ Bᴾ))
          (cong (liftCenterTy step) eqᴾ) ,
        trans (embedImprecise-lift step (`∀ Bᴵ))
          (cong (liftCenterTy step) eqᴵ) ,
        universals-related-future {p = p} step related
  in value-imprecision-reindex lifted structural {suc k} refl refl
       structural-related
value-imprecision-precise W r {p = I.⇒⊑★ p q} {k = suc k}
    (endpoints , shape , payload) =
  let step = precise-future W r
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-precise W r payload)
value-imprecision-precise W r {p = I.ι⊑★} {k = suc k}
    (endpoints , shape , payload) =
  let step = precise-future W r
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-precise W r payload)
value-imprecision-precise W r {p = I.X⊑★ eq} {k = suc k}
    (endpoints , inj₁ related) =
  typed-endpoints-future (precise-future W r) endpoints ,
  inj₁ (dynamic-holds-future (precise-future W r)
    (λ {p = p} rel →
      value-imprecision-precise W r {p = p} {k = suc k} rel)
    value-payload-reindex eq related)
value-imprecision-precise W r {p = I.X⊑★ eq} {k = suc k}
    (endpoints , inj₂ related) =
  typed-endpoints-future (precise-future W r) endpoints ,
  inj₂ (aligned-dynamic-atom-future (precise-future W r)
    (λ {p = p} rel → value-imprecision-precise W r {p = p} {k = k} rel)
    value-payload-reindex related)
value-imprecision-precise W r
    {p = I.∀⊑ {A = Aᴾ} {B = Aᴵ} nonvar occurs p} {k = suc k}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , related) =
  let step = precise-future W r
      lifted = liftCenterImprecision step (I.∀⊑ nonvar occurs p)
      p-lifted = liftCenterDynamicBodyImprecision step p
      p-structural = subst≡
        (λ T → I.instᵐ
          (impEnv (core (preciseBindWorld W _ r)))
          I.⊢ liftCenterBody step _ ⊑ T)
        (renameᵗ-shift Fin.suc Aᴵ) p-lifted
      related-structural = right-universals-related-reindex
        p-structural p-lifted refl (sym (renameᵗ-shift Fin.suc Aᴵ))
        (right-universals-related-future {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} step related)
      structural = I.∀⊑
        (renameNonVar (extᵗ Fin.suc) nonvar)
        (IC.rename-occurs (extᵗ Fin.suc)
          (IC.ext-injective IC.fin-suc-injective) occurs)
        p-structural
      structural-endpoints = typed-endpoints-derivation-reindex
        lifted structural (typed-endpoints-future step endpoints)
      structural-related = structural-endpoints ,
        liftPreciseBody step Bᴾ , liftImpreciseTy step Bᴵ ,
        trans (embedPrecise-lift step (`∀ Bᴾ))
          (cong (liftCenterTy step) eqᴾ) ,
        trans (embedImprecise-lift step Bᴵ)
          (cong (liftCenterTy step) eqᴵ) ,
        related-structural
  in value-imprecision-reindex lifted structural {suc k} refl refl
       structural-related
value-imprecision-precise W r {p = I.∀★⊑★} {k = suc k}
    (endpoints , shape , payload) =
  let step = precise-future W r
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-precise W r payload)
value-imprecision-precise W r
    {p = I.∀⊑★ nonstar p} {k = suc k}
    (endpoints , shape , payload) =
  let step = precise-future W r
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-precise W r payload)
value-imprecision-precise W r {p = I.bot-elim} {k = suc k}
    endpoints = typed-endpoints-future (precise-future W r) endpoints
value-imprecision-precise W r {p = I.bot⊑★} {k = suc k}
    endpoints = typed-endpoints-future (precise-future W r) endpoints

-- Termination note: the `X⊑★` dynamic case recurses at the same step
-- index into the slot's representation imprecision; well-founded by
-- allocation order (`dynamicFresh`; see LR-narrow/LogicalRelation.agda).
{-# TERMINATING #-}
value-imprecision-imprecise : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Rᴵ}
    (W : World Δᴾ Δᴵ Δᶜ)
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k Vᴵ Vᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision (impreciseBindWorld W Rᴵ)
      (liftCenterImprecision (imprecise-future W Rᴵ) p) k
      (liftImpreciseTerm (imprecise-future W Rᴵ) Vᴵ)
      (liftPreciseTerm (imprecise-future W Rᴵ) Vᴾ)
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.∀⊑ nonvar occurs p}
    {k = zero} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.★⊑★} {k = zero}
    endpoints = typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.ι⊑ι} {k = zero}
    endpoints = typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.X⊑X} {k = zero}
    endpoints = typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.⇒⊑⇒ p q}
    {k = zero} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.∀⊑∀ p}
    {k = zero} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.⇒⊑★ p q}
    {k = zero} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.ι⊑★} {k = zero}
    endpoints = typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.X⊑★ eq}
    {k = zero} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.∀★⊑★}
    {k = zero} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.∀⊑★ nonstar p}
    {k = zero} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.bot-elim}
    {k = zero} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.bot⊑★}
    {k = zero} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.★⊑★} {k = suc k}
    (endpoints , inj₁ (shape , payload)) =
  let step = imprecise-future W Rᴵ
      shape′ = dynamic-payload-shape-future step shape
      payload′ = value-imprecision-imprecise W payload
      precise-eq = trans
        (cong (embedPrecise (core (impreciseBindWorld W Rᴵ)))
          (precise-ground-type-eq step (precise-ground shape)))
        (embedPrecise-lift step (precise-ground shape))
      imprecise-eq = trans
        (cong (embedImprecise (core (impreciseBindWorld W Rᴵ)))
          (imprecise-ground-type-eq step (imprecise-ground shape)))
        (embedImprecise-lift step (imprecise-ground shape))
      related′ = value-imprecision-reindex
        (payload-imprecision shape′)
        (liftCenterImprecision step (payload-imprecision shape))
        precise-eq imprecise-eq payload′
  in typed-endpoints-future step endpoints , inj₁ (shape′ , related′)
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.★⊑★} {k = suc k}
    (endpoints , inj₂ related) =
  let step = imprecise-future W Rᴵ
  in typed-endpoints-future step endpoints ,
     inj₂ (dynamic-atom-tag-future step
       (λ {p = p} rel →
         value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = p} {k = suc k} rel)
       value-payload-reindex related)
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.ι⊑ι} {k = suc k}
    (endpoints , same) =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints ,
  same-base-value-future (imprecise-future W Rᴵ) same
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.X⊑X} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints ,
  paired-holds-future (imprecise-future W Rᴵ)
    (λ {p = p} rel →
      value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = p} {k = k} rel)
    value-payload-reindex related
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.⇒⊑⇒ p q}
    {k = suc k} (endpoints , related) =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints ,
  functions-related-future (imprecise-future W Rᴵ) related
value-imprecision-imprecise {Rᴵ = Rᴵ} W
    {p = I.∀⊑∀ {A = Aᴾ} {B = Aᴵ} p} {k = suc k}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , related) =
  let step = imprecise-future W Rᴵ
      lifted = liftCenterImprecision step (I.∀⊑∀ p)
      structural = I.∀⊑∀ (liftCenterBodyImprecision step p)
      structural-endpoints = typed-endpoints-derivation-reindex
        lifted structural (typed-endpoints-future step endpoints)
      structural-related = structural-endpoints ,
        liftPreciseBody step Bᴾ , liftImpreciseBody step Bᴵ ,
        trans (embedPrecise-lift step (`∀ Bᴾ))
          (cong (liftCenterTy step) eqᴾ) ,
        trans (embedImprecise-lift step (`∀ Bᴵ))
          (cong (liftCenterTy step) eqᴵ) ,
        universals-related-future {p = p} step related
  in value-imprecision-reindex lifted structural {suc k} refl refl
       structural-related
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.⇒⊑★ p q}
    {k = suc k} (endpoints , shape , payload) =
  let step = imprecise-future W Rᴵ
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-imprecise W payload)
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.ι⊑★}
    {k = suc k} (endpoints , shape , payload) =
  let step = imprecise-future W Rᴵ
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-imprecise W payload)
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.X⊑★ eq}
    {k = suc k} (endpoints , inj₁ related) =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints ,
  inj₁ (dynamic-holds-future (imprecise-future W Rᴵ)
    (λ {p = p} rel →
      value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = p} {k = suc k} rel)
    value-payload-reindex eq related)
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.X⊑★ eq}
    {k = suc k} (endpoints , inj₂ related) =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints ,
  inj₂ (aligned-dynamic-atom-future (imprecise-future W Rᴵ)
    (λ {p = p} rel →
      value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = p} {k = k} rel)
    value-payload-reindex related)
value-imprecision-imprecise {Rᴵ = Rᴵ} W
    {p = I.∀⊑ {A = Aᴾ} {B = Aᴵ} nonvar occurs p} {k = suc k}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , related) =
  let step = imprecise-future W Rᴵ
      lifted = liftCenterImprecision step (I.∀⊑ nonvar occurs p)
      p-lifted = liftCenterDynamicBodyImprecision step p
      p-structural = subst≡
        (λ T → I.instᵐ (impEnv (core (impreciseBindWorld W Rᴵ)))
          I.⊢ liftCenterBody step _ ⊑ T)
        (renameᵗ-shift Fin.suc Aᴵ) p-lifted
      related-structural = right-universals-related-reindex
        p-structural p-lifted refl (sym (renameᵗ-shift Fin.suc Aᴵ))
        (right-universals-related-future {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} step related)
      structural = I.∀⊑
        (renameNonVar (extᵗ Fin.suc) nonvar)
        (IC.rename-occurs (extᵗ Fin.suc)
          (IC.ext-injective IC.fin-suc-injective) occurs)
        p-structural
      structural-endpoints = typed-endpoints-derivation-reindex
        lifted structural (typed-endpoints-future step endpoints)
      structural-related = structural-endpoints ,
        liftPreciseBody step Bᴾ , liftImpreciseTy step Bᴵ ,
        trans (embedPrecise-lift step (`∀ Bᴾ))
          (cong (liftCenterTy step) eqᴾ) ,
        trans (embedImprecise-lift step Bᴵ)
          (cong (liftCenterTy step) eqᴵ) ,
        related-structural
  in value-imprecision-reindex lifted structural {suc k} refl refl
       structural-related
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.∀★⊑★}
    {k = suc k} (endpoints , shape , payload) =
  let step = imprecise-future W Rᴵ
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-imprecise W payload)
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.∀⊑★ nonstar p}
    {k = suc k} (endpoints , shape , payload) =
  let step = imprecise-future W Rᴵ
  in typed-endpoints-future step endpoints ,
     right-dynamic-payload-future step shape
       (value-imprecision-imprecise W payload)
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.bot-elim}
    {k = suc k} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints
value-imprecision-imprecise {Rᴵ = Rᴵ} W {p = I.bot⊑★}
    {k = suc k} endpoints =
  typed-endpoints-future (imprecise-future W Rᴵ) endpoints

value-imprecision-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision W′ (liftCenterImprecision W≼W′ p) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
value-imprecision-future future-refl related = related
value-imprecision-future
    (future-paired {W′ = W′} W≼W′ related) value-related =
  value-imprecision-paired W′ related
    (value-imprecision-future W≼W′ value-related)
value-imprecision-future
    (future-precise {W′ = W′} W≼W′ related) value-related =
  value-imprecision-precise W′ related
    (value-imprecision-future W≼W′ value-related)
value-imprecision-future
    (future-imprecise {W′ = W′} {Aᴵ = Aᴵ} W≼W′) value-related =
  value-imprecision-imprecise W′
    (value-imprecision-future W≼W′ value-related)

right-dynamic-payload-related-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {k Vᴵ Vᴾ} (W≼W′ : Future W W′)
  → RightDynamicPayloadRelated W Aᴾ k Vᴵ Vᴾ
  → RightDynamicPayloadRelated W′ (liftCenterTy W≼W′ Aᴾ) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
right-dynamic-payload-related-future W≼W′ (shape , payload) =
  right-dynamic-payload-future W≼W′ shape
    (value-imprecision-future W≼W′ payload)
