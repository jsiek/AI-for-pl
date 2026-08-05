module Narrowing.InterpreterOperationalValueNarrowing where

-- File Charter:
--   * Defines the exact operational value relation used by the mutual
--     interpreter simulation.
--   * Couples unary typing with the aligned closure body or coercion action
--     that produced every observable runtime value.
--   * Keeps polymorphic bodies related after the exact future allocation.
--   * Erases to `TypedValueNarrowing` at the public terminal boundary.
--   * Contains no interpreter recursion or reduction result.

open import Coercions using (Coercion)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_; map)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  )
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Narrowing.InterpreterQuotientValueNarrowing using
  (InterpreterQuotientValueFrame)
open import Narrowing.InterpreterReachableCoercionNarrowing using
  (ReachableComponentCoercionNarrowing)
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using
  (ValueResultRelation)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import Narrowing.InterpreterWorldNarrowing using
  (Allocated; TypeEnvironmentScoped)
import NuTermImprecision as NTI
import NuTerms as N
import Primitives
open import proof.MaximalLowerBoundsWf using (∀ᵢᶜ)
open import proof.EndpointCanonicalMLBSimpleQuotient using
  ( EndpointRepresentativeAlignment
  ; endpoint-representatives-quotient
  )
open import Types

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

mutual

  data OperationalValueNarrowing :
      ∀ {W W′} →
      (A B : SemanticType) →
      (R : WorldRelation W W′) →
      Value → Value → Set₁ where
    operational-value :
      ∀ {W W′ A B V V′}
        {R : WorldRelation W W′} →
      TypedValueNarrowing A B R V V′ →
      OperationalValueOrigin A B R V V′ →
      OperationalValueNarrowing A B R V V′

  data OperationalValueOrigin :
      ∀ {W W′} →
      (A B : SemanticType) →
      (R : WorldRelation W W′) →
      Value → Value → Set₁ where
    closure-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′
          N N′ A A′ B B′ pA pB}
        {R : WorldRelation W W′} →
      (runtime :
        RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
      EnvironmentRealization runtime γᵀ γ γ′ →
      OperationalEnvironmentNarrowing
        θ θ′ R γᵀ γ γ′ →
      OpenInterpreterTermNarrowing
        R Φ Δᴸ Δᴿ ρ
        (NTI.ctx-imp A A′ pA ∷ γᵀ)
        N N′ B B′ pB →
      OperationalValueOrigin
        (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
        (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ])
        R (closure N γ θ) (closure N′ γ′ θ′)

    constant-origin :
      ∀ {W W′ n}
        {R : WorldRelation W W′} →
      OperationalValueOrigin
        (base-type `ℕ) (base-type `ℕ) R
        (constant (Primitives.κℕ n))
        (constant (Primitives.κℕ n))

    paired-tag-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          A A′ B B′ p q G H V V′}
        {gG : Ground G} {gH : Ground H}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions._! G))
        (apply-coercion (Coercions._! H))
        {A} {A′} {B} {B′} p q →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        dynamic-type dynamic-type R
        (tagged gG θ V) (tagged gH θ′ V′)

    left-tag-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          A A′ B B′ p q G V V′}
        {gG : Ground G}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions._! G)) skip-coercion
        {A} {A′} {B} {B′} p q →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        dynamic-type dynamic-type R (tagged gG θ V) V′

    right-tag-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          A A′ B B′ p q H V V′}
        {gH : Ground H}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion (Coercions._! H))
        {A} {A′} {B} {B′} p q →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        dynamic-type dynamic-type R V (tagged gH θ′ V′)

    paired-seal-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          A A′ B B′ p q C X D Y V V′ α α′}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.seal C X))
        (apply-coercion (Coercions.seal D Y))
        {A} {A′} {B} {B′} p q →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        (nominal-type (seal-name α))
        (nominal-type (seal-name α′)) R
        (sealed α V) (sealed α′ V′)

    left-seal-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          A A′ B B′ p q C X V V′ α}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.seal C X)) skip-coercion
        {A} {A′} {B} {B′} p q →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        (nominal-type (seal-name α)) ⟦ B′ ⟧[ θ′ ] R
        (sealed α V) V′

    paired-function-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          A A′ B B′ C C′ D D′
          pA pB pC pD c d c′ d′ V V′}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (c Coercions.↦ d))
        (apply-coercion (c′ Coercions.↦ d′))
        {A ⇒ B} {A′ ⇒ B′} {C ⇒ D} {C′ ⇒ D′}
        (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion c) (apply-coercion c′) pC pA →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion d) (apply-coercion d′) pB pD →
      OperationalValueNarrowing
        (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
        (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]) R V V′ →
      OperationalValueOrigin
        (⟦ C ⟧[ θ ] ⇒ᵛ ⟦ D ⟧[ θ ])
        (⟦ C′ ⟧[ θ′ ] ⇒ᵛ ⟦ D′ ⟧[ θ′ ]) R
        (function-proxy c d θ V)
        (function-proxy c′ d′ θ′ V′)

    left-function-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          A B C D T₁ T₂ pA pB pC pD c d V V′}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (c Coercions.↦ d)) skip-coercion
        {A ⇒ B} {T₁ ⇒ T₂} {C ⇒ D} {T₁ ⇒ T₂}
        (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion c) skip-coercion pC pA →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion d) skip-coercion pB pD →
      OperationalValueNarrowing
        (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])
        (⟦ T₁ ⟧[ θ′ ] ⇒ᵛ ⟦ T₂ ⟧[ θ′ ]) R V V′ →
      OperationalValueOrigin
        (⟦ C ⟧[ θ ] ⇒ᵛ ⟦ D ⟧[ θ ])
        (⟦ T₁ ⟧[ θ′ ] ⇒ᵛ ⟦ T₂ ⟧[ θ′ ]) R
        (function-proxy c d θ V) V′

    right-function-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          S₁ S₂ A′ B′ C′ D′ pA pB pC pD c′ d′ V V′}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion (c′ Coercions.↦ d′))
        {S₁ ⇒ S₂} {A′ ⇒ B′} {S₁ ⇒ S₂} {C′ ⇒ D′}
        (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
      OperationalValueNarrowing
        (⟦ S₁ ⟧[ θ ] ⇒ᵛ ⟦ S₂ ⟧[ θ ])
        (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]) R V V′ →
      OperationalValueOrigin
        (⟦ S₁ ⟧[ θ ] ⇒ᵛ ⟦ S₂ ⟧[ θ ])
        (⟦ C′ ⟧[ θ′ ] ⇒ᵛ ⟦ D′ ⟧[ θ′ ]) R
        V (function-proxy c′ d′ θ′ V′)

    right-function-components-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          S₁ S₂ A′ B′ C′ D′ pA pB pC pD c′ d′ V V′}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion (c′ Coercions.↦ d′))
        {S₁ ⇒ S₂} {A′ ⇒ B′} {S₁ ⇒ S₂} {C′ ⇒ D′}
        (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion c′) pC pA →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion d′) pB pD →
      OperationalValueNarrowing
        (⟦ S₁ ⟧[ θ ] ⇒ᵛ ⟦ S₂ ⟧[ θ ])
        (⟦ A′ ⟧[ θ′ ] ⇒ᵛ ⟦ B′ ⟧[ θ′ ]) R V V′ →
      OperationalValueOrigin
        (⟦ S₁ ⟧[ θ ] ⇒ᵛ ⟦ S₂ ⟧[ θ ])
        (⟦ C′ ⟧[ θ′ ] ⇒ᵛ ⟦ D′ ⟧[ θ′ ]) R
        V (function-proxy c′ d′ θ′ V′)

    right-function-boundary-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          A A′ C′ D′ p q c′ d′ V V′ left-result}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion (c′ Coercions.↦ d′))
        {A} {A′} {A} {C′ ⇒ D′} p q →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      left-result ≡ ⟦ A ⟧[ θ ] →
      OperationalValueOrigin
        left-result
        (⟦ C′ ⟧[ θ′ ] ⇒ᵛ ⟦ D′ ⟧[ θ′ ]) R
        V (function-proxy c′ d′ θ′ V′)

    paired-type-abstraction-origin :
      ∀ {W W′ body body′ X X′ V V′}
        {R : WorldRelation W W′} →
      (∀ {U U′ C C′ σ σ′}
         {S : WorldRelation U U′} →
        Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
        (C~C′ : InterpreterTypeNarrowing C C′) →
        (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
        WorldTyping (allocate U C σ) →
        WorldTyping (allocate U′ C′ σ′) →
        OperationalValueNarrowing
          (instantiateSemantic
            (nominal-type (seal-name (freshSealName U))) body)
          (instantiateSemantic
            (nominal-type (seal-name (freshSealName U′))) body′)
          (allocate-both S C~C′ σ~σ′)
          (substituteName X (freshSealName U) V)
          (substituteName X′ (freshSealName U′) V′)) →
      OperationalValueOrigin
        (polymorphic-type body) (polymorphic-type body′) R
        (type-abstraction X V) (type-abstraction X′ V′)

    left-type-abstraction-origin :
      ∀ {W W′ body target X V V′}
        {R : WorldRelation W W′} →
      (∀ {U U′ C σ}
         {S : WorldRelation U U′} →
        Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
        (σ-ok : TypeEnvironmentScoped U σ) →
        WorldTyping (allocate U C σ) →
        WorldTyping U′ →
        OperationalValueNarrowing
          (instantiateSemantic
            (nominal-type (seal-name (freshSealName U))) body)
          target
          (allocate-left-dynamic {A = C} S σ-ok)
          (substituteName X (freshSealName U) V)
          V′) →
      OperationalValueOrigin
        (polymorphic-type body) target R
        (type-abstraction X V) V′

    left-name-instantiated-origin :
      ∀ {W W′ U U′ A B C X α V V′ L}
        {R : WorldRelation W W′}
        {S : WorldRelation U U′} →
      Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
      Allocated U α →
      substituteName X α V ≡ L →
      OperationalValueNarrowing A B R V V′ →
      OperationalValueOrigin C B S L V′

    paired-forall-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          ρ′ A A′ B B′ p q c c′ V V′}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.`∀ c))
        (apply-coercion (Coercions.`∀ c′))
        {`∀ A} {`∀ A′} {`∀ B} {`∀ B′}
        (∀ⁱ p) (∀ⁱ q) →
      NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
      ComponentCoercionNarrowing
        (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ) ρ′
        (apply-coercion c) (apply-coercion c′) p q →
      OperationalValueNarrowing
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ)) A))
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ′)) A′))
        R V V′ →
      OperationalValueOrigin
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ)) B))
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ′)) B′))
        R
        (forall-proxy c θ V) (forall-proxy c′ θ′ V′)

    left-forall-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          ρ′ A T B p q c V V′}
        {nonvar : NonVar A}
        {occ : occurs zero A ≡ true}
        {nonvar′ : NonVar B}
        {occ′ : occurs zero B ≡ true}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.`∀ c)) skip-coercion
        {`∀ A} {T} {`∀ B} {T}
        (ν nonvar occ p) (ν nonvar′ occ′ q) →
      NTI.LiftLeftStoreⁱ
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      ComponentCoercionNarrowing
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ ρ′
        (apply-coercion c) skip-coercion p q →
      OperationalValueNarrowing
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ)) A))
        ⟦ T ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ)) B))
        ⟦ T ⟧[ θ′ ] R
        (forall-proxy c θ V) V′

    right-forall-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          ρ′ A A′ B′ p q c′ V V′}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion (Coercions.`∀ c′))
        {`∀ A} {`∀ A′} {`∀ A} {`∀ B′}
        (∀ⁱ p) (∀ⁱ q) →
      NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
      ComponentCoercionNarrowing
        (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ) ρ′
        skip-coercion (apply-coercion c′) p q →
      OperationalValueNarrowing
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ)) A))
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ′)) A′))
        R V V′ →
      OperationalValueOrigin
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ)) A))
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ′)) B′))
        R
        V (forall-proxy c′ θ′ V′)

    paired-generalized-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          A A′ B B′ p q C c C′ c′ V V′}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.gen C c))
        (apply-coercion (Coercions.gen C′ c′))
        {A} {A′} {`∀ B} {`∀ B′} p q →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ)) B))
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ′)) B′))
        R
        (generalized C c θ V) (generalized C′ c′ θ′ V′)

    left-generalized-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          A T B p q C c V V′}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.gen C c)) skip-coercion
        {A} {T} {`∀ B} {T} p q →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ T ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ)) B))
        ⟦ T ⟧[ θ′ ] R
        (generalized C c θ V) V′

    right-generalized-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′
          S A′ B′ p q C′ c′ V V′}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion (Coercions.gen C′ c′))
        {S} {A′} {S} {`∀ B′} p q →
      OperationalValueNarrowing
        ⟦ S ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        ⟦ S ⟧[ θ ]
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ′)) B′))
        R
        V (generalized C′ c′ θ′ V′)

    operational-quotient-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ C C′ D D′ A A′ X Y E
          d d′ u u′ V V′ L L′ left-result right-result}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {R : WorldRelation W W′} →
      (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
      (D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ) →
      (alignment :
        EndpointRepresentativeAlignment Δᴿ X Y E D′) →
      OperationalDownCoercionNarrowing
        Φ Δᴸ Δᴿ ρ d d′ pC
        (endpoint-representatives-quotient D⊑E alignment) →
      OperationalUpCoercionNarrowing
        Φ Δᴸ Δᴿ ρ u u′
        (endpoint-representatives-quotient D⊑E alignment) pA →
      left-result ≡ ⟦ A ⟧[ θ ] →
      right-result ≡ ⟦ A′ ⟧[ θ′ ] →
      InterpreterQuotientValueFrame R V V′ L L′ →
      OperationalValueNarrowing
        ⟦ C ⟧[ θ ] ⟦ C′ ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        left-result right-result R L L′

    quotient-origin :
      ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′
          M M′ C C′ A A′ pC pA d d′ u u′ V V′ U U′
          left-result right-result}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      OpenInterpreterTermNarrowing
        R Φ Δᴸ Δᴿ ρ γᵀ M M′ C C′ pC →
      OpenInterpreterTermNarrowing
        R Φ Δᴸ Δᴿ ρ γᵀ
        ((M N.⟨ d ⟩) N.⟨ u ⟩)
        ((M′ N.⟨ d′ ⟩) N.⟨ u′ ⟩) A A′ pA →
      left-result ≡ ⟦ A ⟧[ θ ] →
      right-result ≡ ⟦ A′ ⟧[ θ′ ] →
      InterpreterQuotientValueFrame R V V′ U U′ →
      OperationalValueNarrowing
        ⟦ C ⟧[ θ ] ⟦ C′ ⟧[ θ′ ] R V V′ →
      OperationalValueOrigin
        left-result right-result R U U′

  data OperationalEnvironmentNarrowing :
      ∀ {W W′} →
      TypeEnvironment → TypeEnvironment →
      (R : WorldRelation W W′) →
      ∀ {Φ Δᴸ Δᴿ} →
      NTI.CtxImp Φ Δᴸ Δᴿ →
      Environment → Environment → Set₁ where
    []⊑[]ᵒ :
      ∀ {W W′ Φ Δᴸ Δᴿ θ θ′}
        {R : WorldRelation W W′} →
      OperationalEnvironmentNarrowing
        θ θ′ R {Φ} {Δᴸ} {Δᴿ} [] [] []

    _∷⊑∷ᵒ_ :
      ∀ {W W′ Φ Δᴸ Δᴿ θ θ′ A A′}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
        {V V′ : Value} {γ γ′ : Environment}
        {R : WorldRelation W W′} →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalEnvironmentNarrowing
        θ θ′ R γᵀ γ γ′ →
      OperationalEnvironmentNarrowing
        θ θ′ R (NTI.ctx-imp A A′ p ∷ γᵀ)
        (V ∷ γ) (V′ ∷ γ′)

operational-typed :
  ∀ {W W′ A B V V′}
    {R : WorldRelation W W′} →
  OperationalValueNarrowing A B R V V′ →
  TypedValueNarrowing A B R V V′
operational-typed (operational-value typed origin) =
  typed

operational-origin :
  ∀ {W W′ A B V V′}
    {R : WorldRelation W W′} →
  OperationalValueNarrowing A B R V V′ →
  OperationalValueOrigin A B R V V′
operational-origin (operational-value typed origin) =
  origin

OperationalValueResult :
  SemanticType →
  SemanticType →
  ValueResultRelation
OperationalValueResult A B R V V′ =
  OperationalValueNarrowing A B R V V′

data QuotientOperationalOrigin
    {W W′}
    {R : WorldRelation W W′} :
    ∀ {A B V V′} →
    OperationalValueOrigin A B R V V′ → Set₁ where
  active-quotient-operational-origin :
    ∀ {Φ Δᴸ Δᴿ ρ θ θ′ C C′ D D′ A A′ X Y E
        d d′ u u′ V V′ L L′ left-result right-result}
      {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
      {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
      {alignment :
        EndpointRepresentativeAlignment Δᴿ X Y E D′}
      {down :
        OperationalDownCoercionNarrowing
          Φ Δᴸ Δᴿ ρ d d′ pC
          (endpoint-representatives-quotient D⊑E alignment)}
      {up :
        OperationalUpCoercionNarrowing
          Φ Δᴸ Δᴿ ρ u u′
          (endpoint-representatives-quotient D⊑E alignment) pA}
      {left-eq : left-result ≡ ⟦ A ⟧[ θ ]}
      {right-eq : right-result ≡ ⟦ A′ ⟧[ θ′ ]}
      {frame : InterpreterQuotientValueFrame R V V′ L L′}
      {value :
        OperationalValueNarrowing
          ⟦ C ⟧[ θ ] ⟦ C′ ⟧[ θ′ ] R V V′} →
    QuotientOperationalOrigin
      (operational-quotient-origin
        runtime D⊑E alignment down up left-eq right-eq frame value)

  quotient-operational-origin :
    ∀ {Φ Δᴸ Δᴿ ρ γᵀ θ θ′
        M M′ C C′ A′ A″ pC pA d d′ u u′ U U′ V V′
        left-result right-result}
      {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
      {base :
        OpenInterpreterTermNarrowing
          R Φ Δᴸ Δᴿ ρ γᵀ M M′ C C′ pC}
      {terms :
        OpenInterpreterTermNarrowing
          R Φ Δᴸ Δᴿ ρ γᵀ
          ((M N.⟨ d ⟩) N.⟨ u ⟩)
          ((M′ N.⟨ d′ ⟩) N.⟨ u′ ⟩) A′ A″ pA}
      {left-eq : left-result ≡ ⟦ A′ ⟧[ θ ]}
      {right-eq : right-result ≡ ⟦ A″ ⟧[ θ′ ]}
      {frame : InterpreterQuotientValueFrame R U U′ V V′}
      {value :
        OperationalValueNarrowing
          ⟦ C ⟧[ θ ] ⟦ C′ ⟧[ θ′ ] R U U′} →
    QuotientOperationalOrigin
      (quotient-origin runtime base terms left-eq right-eq frame value)


data NameInstantiatedOperationalOrigin
    {W W′}
    {R : WorldRelation W W′} :
    ∀ {A B V V′} →
    OperationalValueOrigin A B R V V′ → Set₁ where
  name-instantiated-operational-origin :
    ∀ {U U′ : World}
      {A B C : SemanticType}
      {X : Name} {α : SealName}
      {V V′ L : Value}
      {Q : WorldRelation U U′}
      {Q≤R :
        Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension Q R}
      {α-ok : Allocated W α}
      {result-eq : substituteName X α V ≡ L}
      {value : OperationalValueNarrowing A B Q V V′} →
    NameInstantiatedOperationalOrigin
      (left-name-instantiated-origin
        {C = C} Q≤R α-ok result-eq value)
