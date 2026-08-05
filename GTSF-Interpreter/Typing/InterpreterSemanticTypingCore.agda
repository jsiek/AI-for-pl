module Typing.InterpreterSemanticTypingCore where

-- File Charter:
--   * Defines the semantic types and unary runtime-typing judgments used by
--     the direct interpreter proof.
--   * Records typed worlds, captured environments, stores, semantic values,
--     and four-way outcomes without mentioning reduction.
--   * Keeps polymorphic instantiation evidence attached to the official
--     `type-abstraction` value form.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)

open import Coercions using
  (Coercion; ModeEnv; _∣_∣_⊢_∶_=⇒_)
import Coercions
open import Ctx using (⤊ᵗ)
open import Interpreter
open import Runtime.InterpreterClosedValue using (ClosedValue)
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import Narrowing.InterpreterWorldNarrowing using
  (Allocated; TypeEnvironmentScoped)
import NuTerms as N
import Primitives
open import Types

------------------------------------------------------------------------
-- Semantic interpretation of static types
------------------------------------------------------------------------

data SemanticType : Set where
  bound-type :
    ℕ →
    SemanticType

  nominal-type :
    TypeName →
    SemanticType

  unbound-type :
    ℕ →
    SemanticType

  base-type :
    Base →
    SemanticType

  dynamic-type :
    SemanticType

  _⇒ᵛ_ :
    SemanticType →
    SemanticType →
    SemanticType

  polymorphic-type :
    SemanticType →
    SemanticType

infixr 7 _⇒ᵛ_

semanticLookup : List SemanticType → ℕ → SemanticType
semanticLookup [] X = unbound-type X
semanticLookup (A ∷ η) zero = A
semanticLookup (A ∷ η) (suc X) = semanticLookup η X

renameSemantic : (ℕ → ℕ) → SemanticType → SemanticType
renameSemantic ρ (bound-type X) = bound-type (ρ X)
renameSemantic ρ (nominal-type X) = nominal-type X
renameSemantic ρ (unbound-type X) = unbound-type X
renameSemantic ρ (base-type ι) = base-type ι
renameSemantic ρ dynamic-type = dynamic-type
renameSemantic ρ (A ⇒ᵛ B) =
  renameSemantic ρ A ⇒ᵛ renameSemantic ρ B
renameSemantic ρ (polymorphic-type A) =
  polymorphic-type (renameSemantic (Types.extᵗ ρ) A)

liftSemantic : SemanticType → SemanticType
liftSemantic = renameSemantic suc

SemanticSubstitution : Set
SemanticSubstitution = ℕ → SemanticType

extendSemanticSubstitution :
  SemanticSubstitution →
  SemanticSubstitution
extendSemanticSubstitution σ zero = bound-type zero
extendSemanticSubstitution σ (suc X) = liftSemantic (σ X)

substituteSemantic :
  SemanticSubstitution →
  SemanticType →
  SemanticType
substituteSemantic σ (bound-type X) = σ X
substituteSemantic σ (nominal-type X) = nominal-type X
substituteSemantic σ (unbound-type X) = unbound-type X
substituteSemantic σ (base-type ι) = base-type ι
substituteSemantic σ dynamic-type = dynamic-type
substituteSemantic σ (A ⇒ᵛ B) =
  substituteSemantic σ A ⇒ᵛ substituteSemantic σ B
substituteSemantic σ (polymorphic-type A) =
  polymorphic-type
    (substituteSemantic (extendSemanticSubstitution σ) A)

singleSemanticSubstitution :
  SemanticType →
  SemanticSubstitution
singleSemanticSubstitution A zero = A
singleSemanticSubstitution A (suc X) = bound-type X

instantiateSemantic : SemanticType → SemanticType → SemanticType
instantiateSemantic A =
  substituteSemantic (singleSemanticSubstitution A)

interpretType : List SemanticType → Ty → SemanticType
interpretType η (＇ X) = semanticLookup η X
interpretType η (‵ ι) = base-type ι
interpretType η ★ = dynamic-type
interpretType η (A ⇒ B) =
  interpretType η A ⇒ᵛ interpretType η B
interpretType η (`∀ A) =
  polymorphic-type
    (interpretType
      (bound-type zero ∷ map liftSemantic η)
      A)

semanticEnvironment : TypeEnvironment → List SemanticType
semanticEnvironment = map nominal-type

⟦_⟧[_] : Ty → TypeEnvironment → SemanticType
⟦ A ⟧[ θ ] = interpretType (semanticEnvironment θ) A

interpretContext : TypeEnvironment → Ctx → List SemanticType
interpretContext θ [] = []
interpretContext θ (A ∷ Γ) =
  ⟦ A ⟧[ θ ] ∷ interpretContext θ Γ

------------------------------------------------------------------------
-- Unary world and static-environment invariants
------------------------------------------------------------------------

data TypeEnvironmentLength : TyCtx → TypeEnvironment → Set where
  length-empty :
    TypeEnvironmentLength zero []

  length-cons :
    ∀ {Δ X θ} →
    TypeEnvironmentLength Δ θ →
    TypeEnvironmentLength (suc Δ) (X ∷ θ)

record AllocationRepresentation
    (W : World) (α : SealName) (A : SemanticType) : Set where
  constructor allocation-representation
  field
    allocation-type :
      Ty

    allocation-scope :
      TypeEnvironment

    allocation-present :
      allocation α allocation-type allocation-scope ∈ allocations W

    representation-eq :
      A ≡ ⟦ allocation-type ⟧[ allocation-scope ]

open AllocationRepresentation public

data StoreTyping (W : World) (θ : TypeEnvironment) :
    Store → Set where
  store-empty :
    StoreTyping W θ []

  store-cons :
    ∀ {Σ X A α} →
    lookup θ X ≡ just (seal-name α) →
    AllocationRepresentation W α ⟦ A ⟧[ θ ] →
    StoreTyping W θ Σ →
    StoreTyping W θ ((X , A) ∷ Σ)

record RuntimeContext
    (W : World) (Δ : TyCtx) (Σ : Store)
    (θ : TypeEnvironment) : Set where
  constructor runtime-context
  field
    type-length :
      TypeEnvironmentLength Δ θ

    type-scope :
      TypeEnvironmentScoped W θ

    store-typing :
      StoreTyping W θ Σ

open RuntimeContext public

data WorldTyping : World → Set₁ where
  empty-world-typed :
    WorldTyping emptyWorld

  allocate-world-typed :
    ∀ {W Δ Σ θ A} →
    WorldTyping W →
    RuntimeContext W Δ Σ θ →
    WfTy Δ A →
    WorldTyping (allocate W A θ)

data WorldExtension : World → World → Set where
  world-extension-refl :
    ∀ {W} →
    WorldExtension W W

  world-extension-allocate :
    ∀ {W U A θ} →
    WorldExtension W U →
    WorldExtension W (allocate U A θ)

------------------------------------------------------------------------
-- Semantic values and captured term environments
------------------------------------------------------------------------

mutual

  data ValueTyping :
      World → Value → SemanticType → Set₁ where
    closure-typed :
      ∀ {W Δ Σ Γ θ γ N A B} →
      WorldTyping W →
      RuntimeContext W Δ Σ θ →
      RuntimeTypeEnvironment θ →
      EnvironmentTyping W θ γ Γ →
      InterpreterTerm N →
      N._∣_∣_⊢_⦂_ Δ Σ (A ∷ Γ) N B →
      ValueTyping W (closure N γ θ)
        (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ])

    constant-typed :
      ∀ {W n} →
      ValueTyping W (constant (Primitives.κℕ n))
        (base-type `ℕ)

    tagged-typed :
      ∀ {W Δ Σ Γ θ γ V G μ}
        {gG : Ground G} →
      WorldTyping W →
      RuntimeContext W Δ Σ θ →
      RuntimeGround θ G →
      EnvironmentTyping W θ γ Γ →
      μ ∣ Δ ∣ Σ ⊢ Coercions._! G ∶ G =⇒ ★ →
      ValueTyping W V ⟦ G ⟧[ θ ] →
      ValueTyping W (tagged gG θ V) dynamic-type

    sealed-typed :
      ∀ {W Δ Σ Γ θ γ V X A α μ} →
      WorldTyping W →
      RuntimeContext W Δ Σ θ →
      EnvironmentTyping W θ γ Γ →
      μ ∣ Δ ∣ Σ ⊢ Coercions.seal A X ∶ A =⇒ ＇ X →
      lookup θ X ≡ just (seal-name α) →
      AllocationRepresentation W α ⟦ A ⟧[ θ ] →
      ValueTyping W V ⟦ A ⟧[ θ ] →
      ValueTyping W (sealed α V) (nominal-type (seal-name α))

    function-proxy-typed :
      ∀ {W Δ Σ Γ θ γ V p q A A′ B B′ μ} →
      WorldTyping W →
      RuntimeContext W Δ Σ θ →
      RuntimeTypeEnvironment θ →
      EnvironmentTyping W θ γ Γ →
      μ ∣ Δ ∣ Σ ⊢ p Coercions.↦ q
        ∶ A ⇒ B =⇒ A′ ⇒ B′ →
      ValueTyping W V
        (⟦ A ⟧[ θ ] ⇒ᵛ ⟦ B ⟧[ θ ]) →
      ValueTyping W (function-proxy p q θ V)
        (⟦ A′ ⟧[ θ ] ⇒ᵛ ⟦ B′ ⟧[ θ ])

    type-abstraction-typed :
      ∀ {W Δ Σ Γ θ γ X V A P}
        {vP : N.Value P} →
      WorldTyping W →
      RuntimeContext W Δ Σ θ →
      RuntimeTypeEnvironment θ →
      EnvironmentTyping W θ γ Γ →
      abstract-name X ∉ θ →
      ClosedValue γ (abstract-name X ∷ θ) vP V →
      InterpreterTerm P →
      N._∣_∣_⊢_⦂_
        (suc Δ) (⟰ᵗ Σ) (⤊ᵗ Γ) P A →
      ValueTyping W (type-abstraction X V)
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ))
            A))

    forall-proxy-typed :
      ∀ {W Δ Σ Γ θ γ V c A B μ} →
      WorldTyping W →
      RuntimeContext W Δ Σ θ →
      RuntimeTypeEnvironment θ →
      EnvironmentTyping W θ γ Γ →
      μ ∣ Δ ∣ Σ ⊢ Coercions.`∀ c ∶ `∀ A =⇒ `∀ B →
      ValueTyping W V
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ))
            A)) →
      ValueTyping W (forall-proxy c θ V)
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ))
            B))

    generalized-typed :
      ∀ {W Δ Σ Γ θ γ V A B c μ} →
      WorldTyping W →
      RuntimeContext W Δ Σ θ →
      RuntimeTypeEnvironment θ →
      EnvironmentTyping W θ γ Γ →
      μ ∣ Δ ∣ Σ ⊢ Coercions.gen A c ∶ A =⇒ `∀ B →
      ValueTyping W V ⟦ A ⟧[ θ ] →
      ValueTyping W (generalized A c θ V)
        (polymorphic-type
          (interpretType
            (bound-type zero ∷
              map liftSemantic (semanticEnvironment θ))
            B))

  data EnvironmentTyping
      (W : World) (θ : TypeEnvironment) :
      Environment → Ctx → Set₁ where
    environment-empty :
      EnvironmentTyping W θ [] []

    environment-cons :
      ∀ {γ Γ V A} →
      ValueTyping W V ⟦ A ⟧[ θ ] →
      EnvironmentTyping W θ γ Γ →
      EnvironmentTyping W θ (V ∷ γ) (A ∷ Γ)

------------------------------------------------------------------------
-- Error-free typed outcomes
------------------------------------------------------------------------

data OutcomeTyping
    (W : World) (A : SemanticType) :
    Outcome → Set₁ where
  timeout-typed :
    ∀ {U} →
    WorldExtension W U →
    OutcomeTyping W A (timed U)

  blame-typed :
    ∀ {U} →
    WorldExtension W U →
    OutcomeTyping W A (blamed U)

  return-typed :
    ∀ {U V} →
    WorldExtension W U →
    WorldTyping U →
    ValueTyping U V A →
    OutcomeTyping W A (returned U V)
