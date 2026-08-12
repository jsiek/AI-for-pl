module proof.LR-narrow.Closure where

-- File Charter:
--   * Proves closure properties of the three-context logical relation.
--   * Establishes downward closure and future-world monotonicity.
--   * Supplies the proof terms re-exported by LR-narrow.Closure.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
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
value-imprecision-downward {p = I.⇒⊑★ p q} {k = zero} endpoints =
  endpoints
value-imprecision-downward {p = I.ι⊑★} {k = zero} endpoints =
  endpoints
value-imprecision-downward {p = I.X⊑★ eq} {k = zero}
    (endpoints , related) =
  endpoints
value-imprecision-downward {p = I.∀⊑ nonvar occurs p} {k = zero}
    (endpoints , Bᴾ , eqᴾ , related) = endpoints
value-imprecision-downward {p = I.∀★⊑★} {k = zero} endpoints =
  endpoints
value-imprecision-downward {p = I.∀⊑★ nonstar p} {k = zero}
    (endpoints , payload) = endpoints
value-imprecision-downward {p = I.bot-elim} {k = zero} endpoints =
  endpoints
value-imprecision-downward {p = I.bot⊑★} {k = zero} endpoints =
  endpoints
value-imprecision-downward {p = I.★⊑★} {k = suc k}
    (endpoints , shape , payload) =
  endpoints , shape , value-imprecision-downward payload
value-imprecision-downward {p = I.ι⊑ι} {k = suc k} related =
  related
value-imprecision-downward {W = W} {p = I.X⊑X {X = X}} {k = suc k}
    (endpoints , related) =
  endpoints , paired-atom-downward (semanticEntry W X) related
value-imprecision-downward {p = I.⇒⊑⇒ p q} {k = suc k}
    (endpoints , head , tail) =
  endpoints , tail
value-imprecision-downward {p = I.∀⊑∀ p} {k = suc k}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , head , tail) =
  endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , tail
value-imprecision-downward {p = I.⇒⊑★ p q} {k = suc k} endpoints =
  endpoints
value-imprecision-downward {p = I.ι⊑★} {k = suc k} endpoints =
  endpoints
value-imprecision-downward {W = W} {p = I.X⊑★ {X = X} eq}
    {k = suc k} (endpoints , related) =
  endpoints , dynamic-atom-downward (semanticEntry W X) eq related
value-imprecision-downward {p = I.∀⊑ nonvar occurs p} {k = suc k}
    (endpoints , Bᴾ , eqᴾ , head , tail) =
  endpoints , Bᴾ , eqᴾ , tail
value-imprecision-downward {p = I.∀★⊑★} {k = suc k} endpoints =
  endpoints
value-imprecision-downward {p = I.∀⊑★ nonstar p} {k = suc k}
    (endpoints , μᴵ , Uᴵ , eq , payload) =
  endpoints , μᴵ , Uᴵ , eq , value-imprecision-downward payload
value-imprecision-downward {p = I.bot-elim} {k = suc k} endpoints =
  endpoints
value-imprecision-downward {p = I.bot⊑★} {k = suc k} endpoints =
  endpoints

semantic-atom-value : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {X : TyVar Δᶜ} {k Vᴵ Vᴾ}
  → PairedAtomHolds (semanticEntry W X) (suc k) Vᴵ Vᴾ
  → ValueImprecision W (I.X⊑X {X = X}) (suc k) Vᴵ Vᴾ
semantic-atom-value {W = W} {X = X} related =
  let Xᴾ , Xᴵ , eqᴾ , eqᴵ ,
        (vVᴵ , Vᴵ⊢) , (vVᴾ , Vᴾ⊢) =
        paired-atom-evidence (semanticEntry W X) related
  in typed-endpoints (＇ Xᴵ) (＇ Xᴾ)
       (cong (λ Y → ＇ Y) eqᴵ)
       (cong (λ Y → ＇ Y) eqᴾ)
       vVᴵ vVᴾ Vᴵ⊢ Vᴾ⊢ , related

dynamic-semantic-atom-value : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {X : TyVar Δᶜ} {k Vᴵ Vᴾ}
    (eq : impEnv (core W) X ≡ I.X⊑★)
  → DynamicAtomHolds (semanticEntry W X) eq (suc k) Vᴵ Vᴾ
  → ValueImprecision W (I.X⊑★ eq) (suc k) Vᴵ Vᴾ
dynamic-semantic-atom-value {W = W} {X = X} eq related =
  let Xᴾ , eqᴾ , (vVᴵ , Vᴵ⊢) , (vVᴾ , Vᴾ⊢) =
        dynamic-atom-evidence (semanticEntry W X) eq related
  in typed-endpoints ★ (＇ Xᴾ) refl
       (cong (λ Y → ＇ Y) eqᴾ) vVᴵ vVᴾ Vᴵ⊢ Vᴾ⊢ , related

precise-value-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {V}
    (W≼W′ : Future W W′)
  → Value V
  → Value (liftPreciseTerm W≼W′ V)
precise-value-future future-refl vV = vV
precise-value-future (future-paired W≼W′ related fresh) vV =
  renameᵗᵐ-preserves-Value C.wk↪ᵗ (precise-value-future W≼W′ vV)
precise-value-future (future-precise W≼W′ fresh) vV =
  renameᵗᵐ-preserves-Value C.wk↪ᵗ (precise-value-future W≼W′ vV)

imprecise-value-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {V}
    (W≼W′ : Future W W′)
  → Value V
  → Value (liftImpreciseTerm W≼W′ V)
imprecise-value-future future-refl vV = vV
imprecise-value-future (future-paired W≼W′ related fresh) vV =
  renameᵗᵐ-preserves-Value C.wk↪ᵗ (imprecise-value-future W≼W′ vV)
imprecise-value-future (future-precise W≼W′ fresh) vV =
  imprecise-value-future W≼W′ vV

precise-typing-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ A}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {V}
    (W≼W′ : Future W W′)
  → ⟨ Δᴾ , preciseStore (core W) , [] ⟩ ⊢ V ⦂ A
  → ⟨ Δᴾ′ , preciseStore (core W′) , [] ⟩
      ⊢ liftPreciseTerm W≼W′ V ⦂ liftPreciseTy W≼W′ A
precise-typing-future future-refl V⊢ = V⊢
precise-typing-future (future-paired W≼W′ related fresh) V⊢ =
  typing-shiftᵗ-bind (precise-typing-future W≼W′ V⊢)
precise-typing-future (future-precise W≼W′ fresh) V⊢ =
  typing-shiftᵗ-bind (precise-typing-future W≼W′ V⊢)

imprecise-typing-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ A}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′} {V}
    (W≼W′ : Future W W′)
  → ⟨ Δᴵ , impreciseStore (core W) , [] ⟩ ⊢ V ⦂ A
  → ⟨ Δᴵ′ , impreciseStore (core W′) , [] ⟩
      ⊢ liftImpreciseTerm W≼W′ V ⦂ liftImpreciseTy W≼W′ A
imprecise-typing-future future-refl V⊢ = V⊢
imprecise-typing-future (future-paired W≼W′ related fresh) V⊢ =
  typing-shiftᵗ-bind (imprecise-typing-future W≼W′ V⊢)
imprecise-typing-future (future-precise W≼W′ fresh) V⊢ =
  imprecise-typing-future W≼W′ V⊢

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

right-universals-related-reindex : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Aᴾ′ Aᴵ′}
    {W : World Δᴾ Δᴵ Δᶜ} {Bᴾ : Ty (suc Δᴾ)} {k Vᴵ Vᴾ}
    (p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
    (q : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ′ ⊑ Aᴵ′)
  → Aᴾ ≡ Aᴾ′
  → Aᴵ ≡ Aᴵ′
  → RightUniversalsRelated W q Bᴾ k Vᴵ Vᴾ
  → RightUniversalsRelated W p Bᴾ k Vᴵ Vᴾ
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
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    W≼W′ (head , tail) =
  (λ K W′≼K Rᴾ Rᴵ r fresh →
      let W′≼B = future-paired W′≼K r fresh
          composite = future-trans W≼W′ W′≼B
          p-composite = openFreshImprecision
            (liftCenterBodyImprecision composite _)
          p-sequential = openFreshImprecision
            (liftCenterBodyImprecision W′≼B
              (liftCenterBodyImprecision W≼W′ _))
      in computations-related-reindex p-composite p-sequential
          (cong (λ A → A [ ＇ Fin.zero ]ᵗ)
            (liftCenterBody-trans W≼W′ W′≼B Aᴾ))
          (cong (λ A → A [ ＇ Fin.zero ]ᵗ)
            (liftCenterBody-trans W≼W′ W′≼B Aᴵ))
          (cong₂ (λ V B → V ⦂∀ B [ ＇ Fin.zero ])
            (liftImpreciseTerm-trans W≼W′ W′≼B Vᴵ)
            (liftImpreciseBody-trans W≼W′ W′≼B Bᴵ))
          (cong₂ (λ V B → V ⦂∀ B [ ＇ Fin.zero ])
            (liftPreciseTerm-trans W≼W′ W′≼B Vᴾ)
            (liftPreciseBody-trans W≼W′ W′≼B Bᴾ))
          (head K (future-trans W≼W′ W′≼K) Rᴾ Rᴵ r fresh)) ,
  universals-related-future W≼W′ tail

right-universals-related-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {k : ℕ} {Vᴵ Vᴾ}
    (W≼W′ : Future W W′)
  → RightUniversalsRelated W p Bᴾ k Vᴵ Vᴾ
  → RightUniversalsRelated W′
      (liftCenterDynamicBodyImprecision W≼W′ p)
      (liftPreciseBody W≼W′ Bᴾ) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
right-universals-related-future {k = zero} W≼W′ related = tt
right-universals-related-future {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {Bᴾ = Bᴾ} {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    W≼W′ (head , tail) =
  (λ K W′≼K Rᴾ fresh →
      let W′≼B = future-precise W′≼K fresh
          composite = future-trans W≼W′ W′≼B
          p-composite = openFreshDynamicImprecision refl
            (liftCenterDynamicBodyImprecision composite _)
          p-sequential = openFreshDynamicImprecision refl
            (liftCenterDynamicBodyImprecision W′≼B
              (liftCenterDynamicBodyImprecision W≼W′ _))
      in computations-related-reindex p-composite p-sequential
          (cong (λ A → A [ ＇ Fin.zero ]ᵗ)
            (liftCenterBody-trans W≼W′ W′≼B Aᴾ))
          (cong (λ A → A [ ＇ Fin.zero ]ᵗ)
            (liftCenterBody-trans W≼W′ W′≼B Aᴵ))
          (liftImpreciseTerm-trans W≼W′ W′≼B Vᴵ)
          (cong₂ (λ V B → V ⦂∀ B [ ＇ Fin.zero ])
            (liftPreciseTerm-trans W≼W′ W′≼B Vᴾ)
            (liftPreciseBody-trans W≼W′ W′≼B Bᴾ))
          (head K (future-trans W≼W′ W′≼K) Rᴾ fresh)) ,
  right-universals-related-future W≼W′ tail

precise-ground-type : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᴾ
  → Ty Δᴾ′
precise-ground-type future-refl G = G
precise-ground-type (future-paired W≼W′ related fresh) G =
  renameᵗ (C.toRenameᵗ C.wk↪ᵗ) (precise-ground-type W≼W′ G)
precise-ground-type (future-precise W≼W′ fresh) G =
  renameᵗ (C.toRenameᵗ C.wk↪ᵗ) (precise-ground-type W≼W′ G)

imprecise-ground-type : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Ty Δᴵ
  → Ty Δᴵ′
imprecise-ground-type future-refl G = G
imprecise-ground-type (future-paired W≼W′ related fresh) G =
  renameᵗ (C.toRenameᵗ C.wk↪ᵗ) (imprecise-ground-type W≼W′ G)
imprecise-ground-type (future-precise W≼W′ fresh) G =
  imprecise-ground-type W≼W′ G

precise-ground-type-eq : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (G : Ty Δᴾ)
  → precise-ground-type W≼W′ G ≡ liftPreciseTy W≼W′ G
precise-ground-type-eq future-refl G = refl
precise-ground-type-eq (future-paired W≼W′ related fresh) G =
  trans (renameᵗ-cong (precise-ground-type W≼W′ G) toRename-wk-eq)
    (cong ⇑ᵗ (precise-ground-type-eq W≼W′ G))
precise-ground-type-eq (future-precise W≼W′ fresh) G =
  trans (renameᵗ-cong (precise-ground-type W≼W′ G) toRename-wk-eq)
    (cong ⇑ᵗ (precise-ground-type-eq W≼W′ G))

imprecise-ground-type-eq : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (G : Ty Δᴵ)
  → imprecise-ground-type W≼W′ G ≡ liftImpreciseTy W≼W′ G
imprecise-ground-type-eq future-refl G = refl
imprecise-ground-type-eq (future-paired W≼W′ related fresh) G =
  trans (renameᵗ-cong (imprecise-ground-type W≼W′ G) toRename-wk-eq)
    (cong ⇑ᵗ (imprecise-ground-type-eq W≼W′ G))
imprecise-ground-type-eq (future-precise W≼W′ fresh) G =
  imprecise-ground-type-eq W≼W′ G

precise-ground-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ G}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → Ground G
  → Ground (precise-ground-type W≼W′ G)
precise-ground-future future-refl g = g
precise-ground-future (future-paired W≼W′ related fresh) g =
  PC.renameGroundᵐ C.wk↪ᵗ (precise-ground-future W≼W′ g)
precise-ground-future (future-precise W≼W′ fresh) g =
  PC.renameGroundᵐ C.wk↪ᵗ (precise-ground-future W≼W′ g)

imprecise-ground-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ G}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → Ground G
  → Ground (imprecise-ground-type W≼W′ G)
imprecise-ground-future future-refl g = g
imprecise-ground-future (future-paired W≼W′ related fresh) g =
  PC.renameGroundᵐ C.wk↪ᵗ (imprecise-ground-future W≼W′ g)
imprecise-ground-future (future-precise W≼W′ fresh) g =
  imprecise-ground-future W≼W′ g

precise-consistency-env-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Env∼ Δᴾ
  → Env∼ Δᴾ′
precise-consistency-env-future future-refl μ = μ
precise-consistency-env-future (future-paired W≼W′ related fresh) μ =
  C.renameEnv∼ C.wk↪ᵗ (precise-consistency-env-future W≼W′ μ)
precise-consistency-env-future (future-precise W≼W′ fresh) μ =
  C.renameEnv∼ C.wk↪ᵗ (precise-consistency-env-future W≼W′ μ)

imprecise-consistency-env-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′
  → Env∼ Δᴵ
  → Env∼ Δᴵ′
imprecise-consistency-env-future future-refl μ = μ
imprecise-consistency-env-future (future-paired W≼W′ related fresh) μ =
  C.renameEnv∼ C.wk↪ᵗ (imprecise-consistency-env-future W≼W′ μ)
imprecise-consistency-env-future (future-precise W≼W′ fresh) μ =
  imprecise-consistency-env-future W≼W′ μ

precise-ground-to-star-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ G μ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → μ ⊢ G ∼★
  → precise-consistency-env-future W≼W′ μ ⊢
      precise-ground-type W≼W′ G ∼★
precise-ground-to-star-future future-refl G∼★ = G∼★
precise-ground-to-star-future (future-paired W≼W′ related fresh) G∼★ =
  PC.rename∼★ᵐ C.wk↪ᵗ (precise-ground-to-star-future W≼W′ G∼★)
precise-ground-to-star-future (future-precise W≼W′ fresh) G∼★ =
  PC.rename∼★ᵐ C.wk↪ᵗ (precise-ground-to-star-future W≼W′ G∼★)

imprecise-ground-to-star-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ G μ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′)
  → μ ⊢ G ∼★
  → imprecise-consistency-env-future W≼W′ μ ⊢
      imprecise-ground-type W≼W′ G ∼★
imprecise-ground-to-star-future future-refl G∼★ = G∼★
imprecise-ground-to-star-future
    (future-paired W≼W′ related fresh) G∼★ =
  PC.rename∼★ᵐ C.wk↪ᵗ
    (imprecise-ground-to-star-future W≼W′ G∼★)
imprecise-ground-to-star-future (future-precise W≼W′ fresh) G∼★ =
  imprecise-ground-to-star-future W≼W′ G∼★

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
precise-injection-future (future-paired W≼W′ related fresh) U g G∼★ =
  trans (cong ⇑ᵗᵐ (precise-injection-future W≼W′ U g G∼★))
    (cong (λ c → ⇑ᵗᵐ (liftPreciseTerm W≼W′ U) ⟨ c ⟩)
      (rename-ground-injection (precise-ground-future W≼W′ g)
        (precise-ground-to-star-future W≼W′ G∼★)))
precise-injection-future (future-precise W≼W′ fresh) U g G∼★ =
  trans (cong ⇑ᵗᵐ (precise-injection-future W≼W′ U g G∼★))
    (cong (λ c → ⇑ᵗᵐ (liftPreciseTerm W≼W′ U) ⟨ c ⟩)
      (rename-ground-injection (precise-ground-future W≼W′ g)
        (precise-ground-to-star-future W≼W′ G∼★)))

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
    (future-paired W≼W′ related fresh) U g G∼★ =
  trans (cong ⇑ᵗᵐ (imprecise-injection-future W≼W′ U g G∼★))
    (cong (λ c → ⇑ᵗᵐ (liftImpreciseTerm W≼W′ U) ⟨ c ⟩)
      (rename-ground-injection (imprecise-ground-future W≼W′ g)
        (imprecise-ground-to-star-future W≼W′ G∼★)))
imprecise-injection-future (future-precise W≼W′ fresh) U g G∼★ =
  imprecise-injection-future W≼W′ U g G∼★

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

lift-precise-constant : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) κ
  → liftPreciseTerm W≼W′ ($ κ) ≡ $ κ
lift-precise-constant future-refl κ = refl
lift-precise-constant (future-paired W≼W′ related fresh) κ
  rewrite lift-precise-constant W≼W′ κ = refl
lift-precise-constant (future-precise W≼W′ fresh) κ
  rewrite lift-precise-constant W≼W′ κ = refl

lift-imprecise-constant : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) κ
  → liftImpreciseTerm W≼W′ ($ κ) ≡ $ κ
lift-imprecise-constant future-refl κ = refl
lift-imprecise-constant (future-paired W≼W′ related fresh) κ
  rewrite lift-imprecise-constant W≼W′ κ = refl
lift-imprecise-constant (future-precise W≼W′ fresh) κ =
  lift-imprecise-constant W≼W′ κ

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
    (fresh : SemanticAtom (pairedBindCore (core W) Rᴾ Rᴵ) Fin.zero)
  → Future W (pairedBindWorld W Rᴾ Rᴵ fresh)
paired-future W r fresh = future-paired future-refl r fresh

precise-future : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) {Rᴾ : Ty Δᴾ}
    (fresh : DynamicSemanticAtom
      (preciseBindCore (core W) Rᴾ) Fin.zero)
  → Future W (preciseBindWorld W Rᴾ fresh)
precise-future W fresh = future-precise future-refl fresh

value-imprecision-paired : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Rᴾ Rᴵ}
    (W : World Δᴾ Δᴵ Δᶜ)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
    (fresh : SemanticAtom (pairedBindCore (core W) Rᴾ Rᴵ) Fin.zero)
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k Vᴵ Vᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision (pairedBindWorld W Rᴾ Rᴵ fresh)
      (liftCenterImprecision (paired-future W r fresh) p) k
      (liftImpreciseTerm (paired-future W r fresh) Vᴵ)
      (liftPreciseTerm (paired-future W r fresh) Vᴾ)
value-imprecision-paired W r fresh {k = zero} endpoints =
  typed-endpoints-future (paired-future W r fresh) endpoints
value-imprecision-paired {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} W r fresh
    {p = I.★⊑★} {k = suc k}
    (endpoints , shape , payload) =
  let step = paired-future W r fresh
      shape′ = dynamic-payload-shape-future step shape
      payload′ = value-imprecision-paired W r fresh payload
      precise-eq = trans
        (cong (embedPrecise (core (pairedBindWorld W Rᴾ Rᴵ fresh)))
          (precise-ground-type-eq step (precise-ground shape)))
        (embedPrecise-lift step (precise-ground shape))
      imprecise-eq = trans
        (cong (embedImprecise (core (pairedBindWorld W Rᴾ Rᴵ fresh)))
          (imprecise-ground-type-eq step (imprecise-ground shape)))
        (embedImprecise-lift step (imprecise-ground shape))
      related′ = value-imprecision-reindex
        (payload-imprecision shape′)
        (liftCenterImprecision step (payload-imprecision shape))
        precise-eq imprecise-eq payload′
  in typed-endpoints-future step endpoints , shape′ , related′
value-imprecision-paired W r fresh {p = I.ι⊑ι} {k = suc k}
    (endpoints , same) =
  typed-endpoints-future (paired-future W r fresh) endpoints ,
  same-base-value-future (paired-future W r fresh) same
value-imprecision-paired W r fresh {p = I.X⊑X} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (paired-future W r fresh) endpoints ,
  paired-atom-holds-future (paired-future W r fresh) related
value-imprecision-paired W r fresh {p = I.⇒⊑⇒ p q} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (paired-future W r fresh) endpoints ,
  functions-related-future (paired-future W r fresh) related
value-imprecision-paired W r fresh
    {p = I.∀⊑∀ {A = Aᴾ} {B = Aᴵ} p} {k = suc k}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , related) =
  let step = paired-future W r fresh
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
        universals-related-future step related
  in value-imprecision-reindex lifted structural {suc k} refl refl
       structural-related
value-imprecision-paired W r fresh {p = I.⇒⊑★ p q} {k = suc k}
    endpoints = typed-endpoints-future (paired-future W r fresh) endpoints
value-imprecision-paired W r fresh {p = I.ι⊑★} {k = suc k}
    endpoints = typed-endpoints-future (paired-future W r fresh) endpoints
value-imprecision-paired W r fresh {p = I.X⊑★ eq} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (paired-future W r fresh) endpoints ,
  dynamic-atom-holds-future (paired-future W r fresh) eq related
value-imprecision-paired W r fresh
    {p = I.∀⊑ {A = Aᴾ} {B = Aᴵ} nonvar occurs p} {k = suc k}
    (endpoints , Bᴾ , eqᴾ , related) =
  let step = paired-future W r fresh
      lifted = liftCenterImprecision step
        (I.∀⊑ nonvar occurs p)
      p-lifted = liftCenterDynamicBodyImprecision step p
      p-structural =
        subst≡
          (λ T → I.instᵐ (impEnv (core (pairedBindWorld W _ _ fresh)))
            I.⊢ liftCenterBody step _ ⊑ T)
          (renameᵗ-shift Fin.suc Aᴵ) p-lifted
      related-structural = right-universals-related-reindex
        p-structural p-lifted refl (sym (renameᵗ-shift Fin.suc Aᴵ))
        (right-universals-related-future step related)
      structural = I.∀⊑
        (renameNonVar (extᵗ Fin.suc) nonvar)
        (IC.rename-occurs (extᵗ Fin.suc)
          (IC.ext-injective IC.fin-suc-injective) occurs)
        p-structural
      structural-endpoints = typed-endpoints-derivation-reindex
        lifted structural (typed-endpoints-future step endpoints)
      structural-related = structural-endpoints ,
        liftPreciseBody step Bᴾ ,
        trans (embedPrecise-lift step (`∀ Bᴾ))
          (cong (liftCenterTy step) eqᴾ) ,
        related-structural
  in value-imprecision-reindex lifted structural {suc k} refl refl
       structural-related
value-imprecision-paired W r fresh {p = I.∀★⊑★} {k = suc k}
    endpoints = typed-endpoints-future (paired-future W r fresh) endpoints
value-imprecision-paired W r fresh
    {p = I.∀⊑★ nonstar p} {k = suc k}
    (endpoints , μᴵ , Uᴵ , eq , payload) =
  let step = paired-future W r fresh
      lifted = liftCenterImprecision step (I.∀⊑★ nonstar p)
      structural = I.∀⊑★ (C.renameNonStar (extᵗ Fin.suc) nonstar)
        (liftCenterBodyImprecision step p)
      structural-endpoints = typed-endpoints-derivation-reindex
        lifted structural (typed-endpoints-future step endpoints)
      payload-lifted = value-imprecision-paired W r fresh payload
      payload-structural = value-imprecision-reindex
        (I.∀⊑∀ (liftCenterBodyImprecision step p))
        (liftCenterImprecision step (I.∀⊑∀ p)) refl refl payload-lifted
      related-structural =
        structural-endpoints ,
        imprecise-consistency-env-future step μᴵ ,
        liftImpreciseTerm step Uᴵ ,
        trans (cong (liftImpreciseTerm step) eq)
          (imprecise-injection-future step Uᴵ ∀★
            (C.∀∼★ {μ = μᴵ})) ,
        payload-structural
  in value-imprecision-reindex lifted structural {suc k} refl refl
       related-structural
value-imprecision-paired W r fresh {p = I.bot-elim} {k = suc k}
    endpoints = typed-endpoints-future (paired-future W r fresh) endpoints
value-imprecision-paired W r fresh {p = I.bot⊑★} {k = suc k}
    endpoints = typed-endpoints-future (paired-future W r fresh) endpoints

value-imprecision-precise : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Rᴾ}
    (W : World Δᴾ Δᴵ Δᶜ)
    (fresh : DynamicSemanticAtom
      (preciseBindCore (core W) Rᴾ) Fin.zero)
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k Vᴵ Vᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision (preciseBindWorld W Rᴾ fresh)
      (liftCenterImprecision (precise-future W fresh) p) k
      (liftImpreciseTerm (precise-future W fresh) Vᴵ)
      (liftPreciseTerm (precise-future W fresh) Vᴾ)
value-imprecision-precise W fresh {k = zero} endpoints =
  typed-endpoints-future (precise-future W fresh) endpoints
value-imprecision-precise {Rᴾ = Rᴾ} W fresh
    {p = I.★⊑★} {k = suc k} (endpoints , shape , payload) =
  let step = precise-future W fresh
      shape′ = dynamic-payload-shape-future step shape
      payload′ = value-imprecision-precise W fresh payload
      precise-eq = trans
        (cong (embedPrecise (core (preciseBindWorld W Rᴾ fresh)))
          (precise-ground-type-eq step (precise-ground shape)))
        (embedPrecise-lift step (precise-ground shape))
      imprecise-eq = trans
        (cong (embedImprecise (core (preciseBindWorld W Rᴾ fresh)))
          (imprecise-ground-type-eq step (imprecise-ground shape)))
        (embedImprecise-lift step (imprecise-ground shape))
      related′ = value-imprecision-reindex
        (payload-imprecision shape′)
        (liftCenterImprecision step (payload-imprecision shape))
        precise-eq imprecise-eq payload′
  in typed-endpoints-future step endpoints , shape′ , related′
value-imprecision-precise W fresh {p = I.ι⊑ι} {k = suc k}
    (endpoints , same) =
  typed-endpoints-future (precise-future W fresh) endpoints ,
  same-base-value-future (precise-future W fresh) same
value-imprecision-precise W fresh {p = I.X⊑X} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (precise-future W fresh) endpoints ,
  paired-atom-holds-future (precise-future W fresh) related
value-imprecision-precise W fresh {p = I.⇒⊑⇒ p q} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (precise-future W fresh) endpoints ,
  functions-related-future (precise-future W fresh) related
value-imprecision-precise W fresh
    {p = I.∀⊑∀ {A = Aᴾ} {B = Aᴵ} p} {k = suc k}
    (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , related) =
  let step = precise-future W fresh
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
        universals-related-future step related
  in value-imprecision-reindex lifted structural {suc k} refl refl
       structural-related
value-imprecision-precise W fresh {p = I.⇒⊑★ p q} {k = suc k}
    endpoints = typed-endpoints-future (precise-future W fresh) endpoints
value-imprecision-precise W fresh {p = I.ι⊑★} {k = suc k}
    endpoints = typed-endpoints-future (precise-future W fresh) endpoints
value-imprecision-precise W fresh {p = I.X⊑★ eq} {k = suc k}
    (endpoints , related) =
  typed-endpoints-future (precise-future W fresh) endpoints ,
  dynamic-atom-holds-future (precise-future W fresh) eq related
value-imprecision-precise W fresh
    {p = I.∀⊑ {A = Aᴾ} {B = Aᴵ} nonvar occurs p} {k = suc k}
    (endpoints , Bᴾ , eqᴾ , related) =
  let step = precise-future W fresh
      lifted = liftCenterImprecision step (I.∀⊑ nonvar occurs p)
      p-lifted = liftCenterDynamicBodyImprecision step p
      p-structural = subst≡
        (λ T → I.instᵐ
          (impEnv (core (preciseBindWorld W _ fresh)))
          I.⊢ liftCenterBody step _ ⊑ T)
        (renameᵗ-shift Fin.suc Aᴵ) p-lifted
      related-structural = right-universals-related-reindex
        p-structural p-lifted refl (sym (renameᵗ-shift Fin.suc Aᴵ))
        (right-universals-related-future step related)
      structural = I.∀⊑
        (renameNonVar (extᵗ Fin.suc) nonvar)
        (IC.rename-occurs (extᵗ Fin.suc)
          (IC.ext-injective IC.fin-suc-injective) occurs)
        p-structural
      structural-endpoints = typed-endpoints-derivation-reindex
        lifted structural (typed-endpoints-future step endpoints)
      structural-related = structural-endpoints ,
        liftPreciseBody step Bᴾ ,
        trans (embedPrecise-lift step (`∀ Bᴾ))
          (cong (liftCenterTy step) eqᴾ) ,
        related-structural
  in value-imprecision-reindex lifted structural {suc k} refl refl
       structural-related
value-imprecision-precise W fresh {p = I.∀★⊑★} {k = suc k}
    endpoints = typed-endpoints-future (precise-future W fresh) endpoints
value-imprecision-precise W fresh
    {p = I.∀⊑★ nonstar p} {k = suc k}
    (endpoints , μᴵ , Uᴵ , eq , payload) =
  let step = precise-future W fresh
      lifted = liftCenterImprecision step (I.∀⊑★ nonstar p)
      structural = I.∀⊑★ (C.renameNonStar (extᵗ Fin.suc) nonstar)
        (liftCenterBodyImprecision step p)
      structural-endpoints = typed-endpoints-derivation-reindex
        lifted structural (typed-endpoints-future step endpoints)
      payload-lifted = value-imprecision-precise W fresh payload
      payload-structural = value-imprecision-reindex
        (I.∀⊑∀ (liftCenterBodyImprecision step p))
        (liftCenterImprecision step (I.∀⊑∀ p)) refl refl payload-lifted
      related-structural =
        structural-endpoints ,
        imprecise-consistency-env-future step μᴵ ,
        liftImpreciseTerm step Uᴵ ,
        trans (cong (liftImpreciseTerm step) eq)
          (imprecise-injection-future step Uᴵ ∀★
            (C.∀∼★ {μ = μᴵ})) ,
        payload-structural
  in value-imprecision-reindex lifted structural {suc k} refl refl
       related-structural
value-imprecision-precise W fresh {p = I.bot-elim} {k = suc k}
    endpoints = typed-endpoints-future (precise-future W fresh) endpoints
value-imprecision-precise W fresh {p = I.bot⊑★} {k = suc k}
    endpoints = typed-endpoints-future (precise-future W fresh) endpoints

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
    (future-paired {W′ = W′} W≼W′ related fresh) value-related =
  value-imprecision-paired W′ related fresh
    (value-imprecision-future W≼W′ value-related)
value-imprecision-future
    (future-precise {W′ = W′} W≼W′ fresh) value-related =
  value-imprecision-precise W′ fresh
    (value-imprecision-future W≼W′ value-related)
