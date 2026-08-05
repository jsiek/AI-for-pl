module Narrowing.InterpreterFramedValueNarrowing where

-- File Charter:
--   * Defines the exact static- and runtime-indexed value relation consumed
--     by the mutual interpreter simulation.
--   * Distinguishes paired `∀` precision from one-sided `ν` precision even
--     when their semantic interpretations happen to coincide.
--   * Retains executable coercion components and quotient route frames.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_; map)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using
  ( NonVar
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  )
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Narrowing.InterpreterOperationalValueNarrowing using
  (OperationalEnvironmentNarrowing; OperationalValueNarrowing)
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
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.MaximalLowerBoundsWf using (∀ᵢᶜ)
open import proof.MaximalLowerBoundsWf using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ)
open import proof.EndpointCanonicalMLBSimpleQuotient using
  ( EndpointRepresentativeAlignment
  ; endpoint-representatives-quotient
  )
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

mutual

  data FramedValueNarrowing :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ : TypeEnvironment}
        {A A′ : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      Value → Value → Set₁ where
    framed-value :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ : TypeEnvironment}
        {A A′ : Ty}
        {V V′ : Value}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      TypedValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      FramedValueOrigin runtime p V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′

    reframed-value :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A A′ V V′ p}
        {R : WorldRelation W W′}
        {runtime runtime′ :
          RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      TypedValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime′ V V′

    reindexed-value :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A A′ V V′ p q}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      TypedValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = q} runtime V V′

    operationally-framed-value :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A A′ V V′ p}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′

    compiler-replanned-value :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ ρ′ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A A′ V V′ p}
        {R : WorldRelation W W′}
        {runtime :
          RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
        {runtime′ :
          RuntimeNarrowing R Φ Δᴸ Δᴿ ρ′ θ θ′} →
      TypedValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime′ V V′

    left-name-instantiated-value :
      ∀ {W W′ U U′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A A′ X α V V′ L p}
        {R : WorldRelation W W′}
        {S : WorldRelation U U′}
        {abstract-runtime :
          RuntimeNarrowing R Φ Δᴸ Δᴿ ρ
            (abstract-name X ∷ θ) θ′}
        {seal-runtime :
          RuntimeNarrowing S Φ Δᴸ Δᴿ ρ
            (seal-name α ∷ θ) θ′} →
      TypedValueNarrowing
        ⟦ A ⟧[ seal-name α ∷ θ ]
        ⟦ A′ ⟧[ θ′ ] S L V′ →
      OperationalValueNarrowing
        ⟦ A ⟧[ seal-name α ∷ θ ]
        ⟦ A′ ⟧[ θ′ ] S L V′ →
      RelatedWorlds.WorldExtension R S →
      Allocated U α →
      substituteName X α V ≡ L →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p}
        abstract-runtime V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p}
        seal-runtime L V′

    paired-lifted-value :
      ∀ {W W′ U U′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {ρ↑ : NTI.StoreImp (∀ᵢᶜ Φ)
          (suc Δᴸ) (suc Δᴿ)}
        {θ θ′ α α′ A A′ A↑ A′↑ V V′ p p↑}
        {R : WorldRelation W W′}
        {S : WorldRelation U U′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
        {runtime↑ :
          RuntimeNarrowing S (∀ᵢᶜ Φ)
            (suc Δᴸ) (suc Δᴿ) ρ↑
            (seal-name α ∷ θ) (seal-name α′ ∷ θ′)} →
      AssumptionMembershipUnique Φ →
      A↑ ≡ ⇑ᵗ A →
      A′↑ ≡ ⇑ᵗ A′ →
      RelatedWorlds.WorldExtension R S →
      TypedValueNarrowing
        ⟦ A↑ ⟧[ seal-name α ∷ θ ]
        ⟦ A′↑ ⟧[ seal-name α′ ∷ θ′ ] S V V′ →
      OperationalValueNarrowing
        ⟦ A↑ ⟧[ seal-name α ∷ θ ]
        ⟦ A′↑ ⟧[ seal-name α′ ∷ θ′ ] S V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′ →
      FramedValueNarrowing
        {A = A↑} {A′ = A′↑} {p = p↑} runtime↑ V V′

    paired-unlifted-value :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {ρ↑ : NTI.StoreImp (∀ᵢᶜ Φ)
          (suc Δᴸ) (suc Δᴿ)}
        {θ θ′ α α′ A A′ V V′ p}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
        {runtime↑ :
          RuntimeNarrowing R (∀ᵢᶜ Φ)
            (suc Δᴸ) (suc Δᴿ) ρ↑
            (seal-name α ∷ θ) (seal-name α′ ∷ θ′)} →
      AssumptionMembershipUnique Φ →
      TypedValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      FramedValueNarrowing
        {A = ⇑ᵗ A} {A′ = ⇑ᵗ A′}
        {p = ⊑-lift∀ᵢ p} runtime↑ V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′

    left-lifted-value :
      ∀ {W W′ U U′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {ρ↑ : NTI.StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {θ θ′ name A A′ A↑ V V′ p p↑}
        {R : WorldRelation W W′}
        {S : WorldRelation U U′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
        {runtime↑ :
          RuntimeNarrowing S
            ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
            (suc Δᴸ) Δᴿ ρ↑
            (name ∷ θ) θ′} →
      AssumptionMembershipUnique Φ →
      A↑ ≡ ⇑ᵗ A →
      RelatedWorlds.WorldExtension R S →
      TypedValueNarrowing
        ⟦ A↑ ⟧[ name ∷ θ ]
        ⟦ A′ ⟧[ θ′ ] S V V′ →
      OperationalValueNarrowing
        ⟦ A↑ ⟧[ name ∷ θ ]
        ⟦ A′ ⟧[ θ′ ] S V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′ →
      FramedValueNarrowing
        {A = A↑} {A′ = A′}
        {p = p↑} runtime↑ V V′

    left-unlifted-value :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {ρ↑ : NTI.StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {θ θ′ α A A′ V V′ p}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
        {runtime↑ :
          RuntimeNarrowing R
            ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
            (suc Δᴸ) Δᴿ ρ↑
            (seal-name α ∷ θ) θ′} →
      AssumptionMembershipUnique Φ →
      TypedValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      OperationalValueNarrowing
        ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
      FramedValueNarrowing
        {A = ⇑ᵗ A} {A′ = A′}
        {p = ⊑-source-liftνᵢ p} runtime↑ V V′ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′

  data FramedValueOrigin :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ : TypeEnvironment}
        {A A′ : Ty}
        {R : WorldRelation W W′} →
      (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
      Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
      Value → Value → Set₁ where
    closure-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
        {θ θ′ γ γ′ N N′ A A′ B B′ pA pB}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      EnvironmentRealization runtime γᵀ γ γ′ →
      FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
      OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ
        (NTI.ctx-imp A A′ pA ∷ γᵀ) N N′ B B′ pB →
      FramedValueOrigin runtime (pA ImprecisionWf.↦ pB)
        (closure N γ θ) (closure N′ γ′ θ′)

    constant-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ n}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      FramedValueOrigin
        {A = ‵ `ℕ} {A′ = ‵ `ℕ}
        runtime ImprecisionWf.idι
        (constant (Primitives.κℕ n))
        (constant (Primitives.κℕ n))

    paired-tag-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A A′ G H V V′ p}
        {gG : Ground G} {gH : Ground H}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions._! G))
        (apply-coercion (Coercions._! H))
        {A} {A′} {★} {★} p ImprecisionWf.id★ →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′ →
      FramedValueOrigin runtime ImprecisionWf.id★
        (tagged gG θ V) (tagged gH θ′ V′)

    left-tag-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A G V V′ p}
        {gG : Ground G}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions._! G)) skip-coercion
        {A} {★} {★} {★} p ImprecisionWf.id★ →
      FramedValueNarrowing
        {A = A} {A′ = ★} {p = p} runtime V V′ →
      FramedValueOrigin runtime ImprecisionWf.id★
        (tagged gG θ V) V′

    right-tag-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A′ H V V′ p}
        {gH : Ground H}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion (Coercions._! H))
        {★} {A′} {★} {★} p ImprecisionWf.id★ →
      FramedValueNarrowing
        {A = ★} {A′ = A′} {p = p} runtime V V′ →
      FramedValueOrigin runtime ImprecisionWf.id★
        V (tagged gH θ′ V′)

    paired-seal-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A A′ X Y C D V V′ α α′ p q}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.seal C X))
        (apply-coercion (Coercions.seal D Y))
        {A} {A′} {＇ X} {＇ Y} p q →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′ →
      FramedValueOrigin runtime q
        (sealed α V) (sealed α′ V′)

    left-seal-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A T X C V V′ α p q}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.seal C X)) skip-coercion
        {A} {T} {＇ X} {T} p q →
      FramedValueNarrowing
        {A = A} {A′ = T} {p = p} runtime V V′ →
      FramedValueOrigin runtime q (sealed α V) V′

    paired-function-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A A′ B B′ C C′ D D′
          pA pB pC pD c d c′ d′ V V′}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (c Coercions.↦ d))
        (apply-coercion (c′ Coercions.↦ d′))
        {A ⇒ B} {A′ ⇒ B′} {C ⇒ D} {C′ ⇒ D′}
        (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion c) (apply-coercion c′)
        {C} {C′} {A} {A′} pC pA →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion d) (apply-coercion d′)
        {B} {B′} {D} {D′} pB pD →
      FramedValueNarrowing
        {A = A ⇒ B} {A′ = A′ ⇒ B′}
        {p = pA ImprecisionWf.↦ pB} runtime V V′ →
      FramedValueOrigin runtime (pC ImprecisionWf.↦ pD)
        (function-proxy c d θ V)
        (function-proxy c′ d′ θ′ V′)

    left-function-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A B C D T₁ T₂ pA pB pC pD c d V V′}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (c Coercions.↦ d)) skip-coercion
        {A ⇒ B} {T₁ ⇒ T₂} {C ⇒ D} {T₁ ⇒ T₂}
        (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion c) skip-coercion
        {C} {T₁} {A} {T₁} pC pA →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion d) skip-coercion
        {B} {T₂} {D} {T₂} pB pD →
      FramedValueNarrowing
        {A = A ⇒ B} {A′ = T₁ ⇒ T₂}
        {p = pA ImprecisionWf.↦ pB} runtime V V′ →
      FramedValueOrigin runtime (pC ImprecisionWf.↦ pD)
        (function-proxy c d θ V) V′

    right-function-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ S₁ S₂ A′ B′ C′ D′
          pA pB pC pD c′ d′ V V′}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion (c′ Coercions.↦ d′))
        {S₁ ⇒ S₂} {A′ ⇒ B′} {S₁ ⇒ S₂} {C′ ⇒ D′}
        (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion c′)
        {S₁} {C′} {S₁} {A′} pC pA →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion d′)
        {S₂} {B′} {S₂} {D′} pB pD →
      FramedValueNarrowing
        {A = S₁ ⇒ S₂} {A′ = A′ ⇒ B′}
        {p = pA ImprecisionWf.↦ pB} runtime V V′ →
      FramedValueOrigin runtime (pC ImprecisionWf.↦ pD)
        V (function-proxy c′ d′ θ′ V′)

    paired-type-abstraction-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {ρ′ :
          NTI.StoreImp
            ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
            (suc Δᴸ) (suc Δᴿ)}
        {θ θ′ A A′ X X′ V V′ p}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      NTI.LiftStoreⁱ
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
      (∀ {U U′ C C′ σ σ′}
         {S : WorldRelation U U′} →
        RelatedWorlds.WorldExtension R S →
        (C~C′ : InterpreterTypeNarrowing C C′) →
        (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
        (allocated :
          RuntimeNarrowing
            (allocate-both S C~C′ σ~σ′)
            ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
            (suc Δᴸ) (suc Δᴿ)
            ρ′
            (seal-name (freshSealName U) ∷ θ)
            (seal-name (freshSealName U′) ∷ θ′)) →
        FramedValueNarrowing
          {A = A} {A′ = A′} {p = p} allocated
          (substituteName X (freshSealName U) V)
          (substituteName X′ (freshSealName U′) V′)) →
      FramedValueOrigin runtime (∀ⁱ p)
        (type-abstraction X V) (type-abstraction X′ V′)

    left-type-abstraction-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {ρ′ :
          NTI.StoreImp
            ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
            (suc Δᴸ) Δᴿ}
        {θ θ′ A T X V V′ p}
        {nonvar : NonVar A} {occ : occurs zero A ≡ true}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      NTI.LiftLeftStoreⁱ
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      (∀ {U U′ C σ}
         {S : WorldRelation U U′} →
        RelatedWorlds.WorldExtension R S →
        (σ-ok : TypeEnvironmentScoped U σ) →
        (allocated :
          RuntimeNarrowing
            (allocate-left-dynamic {A = C} S σ-ok)
            ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ
            ρ′
            (seal-name (freshSealName U) ∷ θ) θ′) →
        FramedValueNarrowing
          {A = A} {A′ = T} {p = p} allocated
          (substituteName X (freshSealName U) V) V′) →
      FramedValueOrigin runtime (ν nonvar occ p)
        (type-abstraction X V) V′

    paired-forall-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : NTI.StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
        {θ θ′ A A′ B B′ p q c c′ V V′}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.`∀ c))
        (apply-coercion (Coercions.`∀ c′))
        {`∀ A} {`∀ A′} {`∀ B} {`∀ B′}
        (∀ⁱ p) (∀ⁱ q) →
      NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
      ComponentCoercionNarrowing
        (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ) ρ′
        (apply-coercion c) (apply-coercion c′)
        {A} {A′} {B} {B′} p q →
      FramedValueNarrowing
        {A = `∀ A} {A′ = `∀ A′} {p = ∀ⁱ p}
        runtime V V′ →
      FramedValueOrigin runtime (∀ⁱ q)
        (forall-proxy c θ V) (forall-proxy c′ θ′ V′)

    left-forall-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {ρ′ :
          NTI.StoreImp
            ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
            (suc Δᴸ) Δᴿ}
        {θ θ′ A T B p q c V V′}
        {nonvar : NonVar A} {occ : occurs zero A ≡ true}
        {nonvar′ : NonVar B} {occ′ : occurs zero B ≡ true}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.`∀ c)) skip-coercion
        {`∀ A} {T} {`∀ B} {T}
        (ν nonvar occ p) (ν nonvar′ occ′ q) →
      NTI.LiftLeftStoreⁱ
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      ComponentCoercionNarrowing
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ ρ′
        (apply-coercion c) skip-coercion
        {A} {T} {B} {T} p q →
      FramedValueNarrowing
        {A = `∀ A} {A′ = T}
        {p = ν nonvar occ p} runtime V V′ →
      FramedValueOrigin runtime (ν nonvar′ occ′ q)
        (forall-proxy c θ V) V′

    right-forall-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : NTI.StoreImp (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ)}
        {θ θ′ A A′ B′ p q c′ V V′}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion (Coercions.`∀ c′))
        {`∀ A} {`∀ A′} {`∀ A} {`∀ B′}
        (∀ⁱ p) (∀ⁱ q) →
      NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
      ComponentCoercionNarrowing
        (∀ᵢᶜ Φ) (suc Δᴸ) (suc Δᴿ) ρ′
        skip-coercion (apply-coercion c′)
        {A} {A′} {A} {B′} p q →
      FramedValueNarrowing
        {A = `∀ A} {A′ = `∀ A′} {p = ∀ⁱ p}
        runtime V V′ →
      FramedValueOrigin runtime (∀ⁱ q)
        V (forall-proxy c′ θ′ V′)

    paired-generalized-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A A′ B B′ p q C C′ c c′ V V′}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.gen C c))
        (apply-coercion (Coercions.gen C′ c′))
        {A} {A′} {`∀ B} {`∀ B′} p (∀ⁱ q) →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′ →
      FramedValueOrigin runtime (∀ⁱ q)
        (generalized C c θ V) (generalized C′ c′ θ′ V′)

    left-generalized-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A T B p q C c V V′}
        {nonvar : NonVar B} {occ : occurs zero B ≡ true}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        (apply-coercion (Coercions.gen C c)) skip-coercion
        {A} {T} {`∀ B} {T} p (ν nonvar occ q) →
      FramedValueNarrowing
        {A = A} {A′ = T} {p = p} runtime V V′ →
      FramedValueOrigin runtime (ν nonvar occ q)
        (generalized C c θ V) V′

    right-generalized-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ S A′ B′ p q C′ c′ V V′}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
        skip-coercion (apply-coercion (Coercions.gen C′ c′))
        {S} {A′} {S} {`∀ B′} p q →
      FramedValueNarrowing
        {A = S} {A′ = A′} {p = p} runtime V V′ →
      FramedValueOrigin runtime q
        V (generalized C′ c′ θ′ V′)

    operational-quotient-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ C C′ D D′ A A′ X Y E
          d d′ u u′ V V′ L L′}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      (D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ) →
      (alignment :
        EndpointRepresentativeAlignment Δᴿ X Y E D′) →
      OperationalDownCoercionNarrowing
        Φ Δᴸ Δᴿ ρ d d′ pC
        (endpoint-representatives-quotient D⊑E alignment) →
      OperationalUpCoercionNarrowing
        Φ Δᴸ Δᴿ ρ u u′
        (endpoint-representatives-quotient D⊑E alignment) pA →
      InterpreterQuotientValueFrame R V V′ L L′ →
      FramedValueNarrowing
        {A = C} {A′ = C′} {p = pC} runtime V V′ →
      FramedValueOrigin runtime pA L L′

    quotient-originᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
        {θ θ′ M M′ C C′ A A′ pC pA
          d d′ u u′ V V′ U U′}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ γᵀ
        M M′ C C′ pC →
      OpenInterpreterTermNarrowing R Φ Δᴸ Δᴿ ρ γᵀ
        ((M N.⟨ d ⟩) N.⟨ u ⟩)
        ((M′ N.⟨ d′ ⟩) N.⟨ u′ ⟩) A A′ pA →
      InterpreterQuotientValueFrame R V V′ U U′ →
      FramedValueNarrowing
        {A = C} {A′ = C′} {p = pC} runtime V V′ →
      FramedValueOrigin runtime pA U U′

  data FramedEnvironmentNarrowing :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ : TypeEnvironment}
        {R : WorldRelation W W′} →
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
      NTI.CtxImp Φ Δᴸ Δᴿ →
      Environment → Environment → Set₁ where
    []⊑[]ᶠ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ : TypeEnvironment}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      FramedEnvironmentNarrowing runtime [] [] []

    _∷⊑∷ᶠ_ :
      ∀ {W W′ Φ Δᴸ Δᴿ}
        {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
        {θ θ′ A A′ V V′ γ γ′ γᵀ p}
        {R : WorldRelation W W′}
        {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
      FramedValueNarrowing
        {A = A} {A′ = A′} {p = p} runtime V V′ →
      FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
      FramedEnvironmentNarrowing runtime
        (NTI.ctx-imp A A′ p ∷ γᵀ)
        (V ∷ γ) (V′ ∷ γ′)

data NameInstantiatedFramedValue :
    ∀ {W W′ Φ Δᴸ Δᴿ}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ θ′ A A′ V V′ p}
      {R : WorldRelation W W′}
      {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
    FramedValueNarrowing
      {A = A} {A′ = A′} {p = p} runtime V V′ →
    Set₁ where
  name-instantiated-framed-value :
    ∀ {W W′ U U′ Φ Δᴸ Δᴿ}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ θ′ A A′ X α V V′ L p}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′}
      {abstract-runtime :
        RuntimeNarrowing R Φ Δᴸ Δᴿ ρ
          (abstract-name X ∷ θ) θ′}
      {seal-runtime :
        RuntimeNarrowing S Φ Δᴸ Δᴿ ρ
          (seal-name α ∷ θ) θ′}
      {typed :
        TypedValueNarrowing
          ⟦ A ⟧[ seal-name α ∷ θ ]
          ⟦ A′ ⟧[ θ′ ] S L V′}
      {operational :
        OperationalValueNarrowing
          ⟦ A ⟧[ seal-name α ∷ θ ]
          ⟦ A′ ⟧[ θ′ ] S L V′}
      {R≤S : RelatedWorlds.WorldExtension R S}
      {α-ok : Allocated U α}
      {result-eq : substituteName X α V ≡ L}
      {value :
        FramedValueNarrowing
          {A = A} {A′ = A′} {p = p}
          abstract-runtime V V′} →
    NameInstantiatedFramedValue
      {W = U} {W′ = U′} {Φ = Φ}
      {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
      {θ = seal-name α ∷ θ} {θ′ = θ′}
      {A = A} {A′ = A′} {V = L} {V′ = V′}
      {p = p} {R = S} {runtime = seal-runtime}
      (left-name-instantiated-value
        {p = p}
        typed operational R≤S α-ok result-eq value)

data FramedValueResult :
  ∀ {Φ Δᴸ Δᴿ}
    (ρ : NTI.StoreImp Φ Δᴸ Δᴿ)
    (θ θ′ : TypeEnvironment)
    {A A′ : Ty} →
  Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
  ValueResultRelation where
  framed-result :
    ∀ {W W′ Φ Δᴸ Δᴿ}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ θ′ : TypeEnvironment}
      {A A′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {R : WorldRelation W W′}
      {V V′ : Value} →
    (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
    FramedValueNarrowing
      {A = A} {A′ = A′} {p = p} runtime V V′ →
    FramedValueResult ρ θ θ′ p R V V′
