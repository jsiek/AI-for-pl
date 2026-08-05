module proof.InterpreterSemanticTypingProperties where

-- File Charter:
--   * Proves structural properties of unary interpreter semantic typing.
--   * Covers type interpretation, lookup, allocation, and world weakening.
--   * Contains no interpreter recursion and no reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (m<n⇒m<1+n; n<1+n; n≮n)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import Ctx using (⤊ᵗ)
open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterValueNarrowing using
  ( EnvironmentScoped
  ; ValueScoped
  ; closure-scoped
  ; constant-scoped
  ; tagged-scoped
  ; sealed-scoped
  ; function-proxy-scoped
  ; type-abstraction-scoped
  ; forall-proxy-scoped
  ; generalized-scoped
  ; []-environment-scoped
  ; _∷-environment-scoped_
  )
open import Narrowing.InterpreterWorldNarrowing using
  (Allocated; TypeEnvironmentScoped; TypeNameScoped; allocated; abstract-scoped;
   seal-scoped; []-scoped; _∷-scoped_)
open import Types
open import proof.InterpreterClosedValueStructural using
  (closed-value-scoped)

------------------------------------------------------------------------
-- Semantic typing implies runtime scope
------------------------------------------------------------------------

mutual

  value-typing-scoped :
    ∀ {W V A} →
    ValueTyping W V A →
    ValueScoped W V
  value-typing-scoped
      (closure-typed W⊢ runtime runtime-env γ⊢ image N⊢) =
    closure-scoped
      (environment-typing-scoped γ⊢) (type-scope runtime)
  value-typing-scoped constant-typed =
    constant-scoped
  value-typing-scoped
      (tagged-typed W⊢ runtime runtime-ground γ⊢ c⊢ V⊢) =
    tagged-scoped (type-scope runtime) (value-typing-scoped V⊢)
  value-typing-scoped
      (sealed-typed W⊢ runtime γ⊢ c⊢ lookup representation V⊢) =
    sealed-scoped
      (allocated (allocation-present representation))
      (value-typing-scoped V⊢)
  value-typing-scoped
      (function-proxy-typed W⊢ runtime runtime-env γ⊢ c⊢ V⊢) =
    function-proxy-scoped
      (type-scope runtime) (value-typing-scoped V⊢)
  value-typing-scoped
      (type-abstraction-typed
        W⊢ runtime runtime-env γ⊢ fresh body image V⊢) =
    type-abstraction-scoped
      (closed-value-scoped
        (environment-typing-scoped γ⊢)
        (abstract-scoped ∷-scoped (type-scope runtime))
        body)
  value-typing-scoped
      (forall-proxy-typed W⊢ runtime runtime-env γ⊢ c⊢ V⊢) =
    forall-proxy-scoped
      (type-scope runtime) (value-typing-scoped V⊢)
  value-typing-scoped
      (generalized-typed W⊢ runtime runtime-env γ⊢ c⊢ V⊢) =
    generalized-scoped
      (type-scope runtime) (value-typing-scoped V⊢)

  environment-typing-scoped :
    ∀ {W θ γ Γ} →
    EnvironmentTyping W θ γ Γ →
    EnvironmentScoped W γ
  environment-typing-scoped environment-empty =
    []-environment-scoped
  environment-typing-scoped (environment-cons V⊢ γ⊢) =
    value-typing-scoped V⊢ ∷-environment-scoped
    environment-typing-scoped γ⊢

------------------------------------------------------------------------
-- Type interpretation and lookup
------------------------------------------------------------------------

semanticLookup-map :
  ∀ f →
  (∀ X → f (unbound-type X) ≡ unbound-type X) →
  ∀ η X →
  semanticLookup (map f η) X ≡ f (semanticLookup η X)
semanticLookup-map f unbound-eq [] X =
  sym (unbound-eq X)
semanticLookup-map f unbound-eq (A ∷ η) zero = refl
semanticLookup-map f unbound-eq (A ∷ η) (suc X) =
  semanticLookup-map f unbound-eq η X

interpret-rename :
  ∀ {η η′ ρ} →
  (∀ X → semanticLookup η′ (ρ X) ≡ semanticLookup η X) →
  ∀ A → interpretType η′ (renameᵗ ρ A) ≡ interpretType η A
interpret-rename lookup-eq (＇ X) =
  lookup-eq X
interpret-rename lookup-eq (‵ ι) =
  refl
interpret-rename lookup-eq ★ =
  refl
interpret-rename lookup-eq (A ⇒ B) =
  cong₂ _⇒ᵛ_
    (interpret-rename lookup-eq A)
    (interpret-rename lookup-eq B)
interpret-rename {η} {η′} {ρ} lookup-eq (`∀ A) =
  cong polymorphic-type
    (interpret-rename under-binder A)
  where
  under-binder :
    ∀ X →
    semanticLookup
      (bound-type zero ∷ map liftSemantic η′)
      (extᵗ ρ X)
      ≡
    semanticLookup
      (bound-type zero ∷ map liftSemantic η)
      X
  under-binder zero =
    refl
  under-binder (suc X) =
    trans (semanticLookup-map liftSemantic (λ Y → refl) η′ (ρ X))
      (trans (cong liftSemantic (lookup-eq X))
        (sym (semanticLookup-map liftSemantic (λ Y → refl) η X)))

interpret-weaken :
  ∀ T η A →
  interpretType (T ∷ η) (⇑ᵗ A) ≡ interpretType η A
interpret-weaken T η A =
  interpret-rename (λ X → refl) A

interpret-context-weaken :
  ∀ X θ Γ →
  interpretContext (X ∷ θ) (⤊ᵗ Γ) ≡ interpretContext θ Γ
interpret-context-weaken X θ [] =
  refl
interpret-context-weaken X θ (A ∷ Γ)
    rewrite interpret-weaken
      (nominal-type X) (semanticEnvironment θ) A
    | interpret-context-weaken X θ Γ =
  refl

substitute-cong :
  ∀ {σ τ} →
  (∀ X → σ X ≡ τ X) →
  ∀ A →
  substituteSemantic σ A ≡ substituteSemantic τ A
substitute-cong σ≡τ (bound-type X) =
  σ≡τ X
substitute-cong σ≡τ (nominal-type X) =
  refl
substitute-cong σ≡τ (unbound-type X) =
  refl
substitute-cong σ≡τ (base-type ι) =
  refl
substitute-cong σ≡τ dynamic-type =
  refl
substitute-cong σ≡τ (A ⇒ᵛ B) =
  cong₂ _⇒ᵛ_
    (substitute-cong σ≡τ A)
    (substitute-cong σ≡τ B)
substitute-cong σ≡τ (polymorphic-type A) =
  cong polymorphic-type
    (substitute-cong under-binder A)
  where
  under-binder :
    ∀ X →
    extendSemanticSubstitution _ X ≡
    extendSemanticSubstitution _ X
  under-binder zero =
    refl
  under-binder (suc X) =
    cong liftSemantic (σ≡τ X)

substitute-rename :
  ∀ σ ρ A →
  substituteSemantic σ (renameSemantic ρ A) ≡
  substituteSemantic (λ X → σ (ρ X)) A
substitute-rename σ ρ (bound-type X) =
  refl
substitute-rename σ ρ (nominal-type X) =
  refl
substitute-rename σ ρ (unbound-type X) =
  refl
substitute-rename σ ρ (base-type ι) =
  refl
substitute-rename σ ρ dynamic-type =
  refl
substitute-rename σ ρ (A ⇒ᵛ B) =
  cong₂ _⇒ᵛ_
    (substitute-rename σ ρ A)
    (substitute-rename σ ρ B)
substitute-rename σ ρ (polymorphic-type A) =
  cong polymorphic-type
    (trans
      (substitute-rename
        (extendSemanticSubstitution σ) (extᵗ ρ) A)
      (substitute-cong pointwise A))
  where
  pointwise :
    ∀ X →
    extendSemanticSubstitution σ (extᵗ ρ X) ≡
    extendSemanticSubstitution (λ Y → σ (ρ Y)) X
  pointwise zero =
    refl
  pointwise (suc X) =
    refl

renameSemantic-cong :
  ∀ {ρ τ} →
  (∀ X → ρ X ≡ τ X) →
  ∀ A →
  renameSemantic ρ A ≡ renameSemantic τ A
renameSemantic-cong ρ≡τ (bound-type X) =
  cong bound-type (ρ≡τ X)
renameSemantic-cong ρ≡τ (nominal-type X) =
  refl
renameSemantic-cong ρ≡τ (unbound-type X) =
  refl
renameSemantic-cong ρ≡τ (base-type ι) =
  refl
renameSemantic-cong ρ≡τ dynamic-type =
  refl
renameSemantic-cong ρ≡τ (A ⇒ᵛ B) =
  cong₂ _⇒ᵛ_
    (renameSemantic-cong ρ≡τ A)
    (renameSemantic-cong ρ≡τ B)
renameSemantic-cong ρ≡τ (polymorphic-type A) =
  cong polymorphic-type
    (renameSemantic-cong under-binder A)
  where
  under-binder :
    ∀ X → extᵗ _ X ≡ extᵗ _ X
  under-binder zero =
    refl
  under-binder (suc X) =
    cong suc (ρ≡τ X)

renameSemantic-compose :
  ∀ ρ τ A →
  renameSemantic ρ (renameSemantic τ A) ≡
  renameSemantic (λ X → ρ (τ X)) A
renameSemantic-compose ρ τ (bound-type X) =
  refl
renameSemantic-compose ρ τ (nominal-type X) =
  refl
renameSemantic-compose ρ τ (unbound-type X) =
  refl
renameSemantic-compose ρ τ (base-type ι) =
  refl
renameSemantic-compose ρ τ dynamic-type =
  refl
renameSemantic-compose ρ τ (A ⇒ᵛ B) =
  cong₂ _⇒ᵛ_
    (renameSemantic-compose ρ τ A)
    (renameSemantic-compose ρ τ B)
renameSemantic-compose ρ τ (polymorphic-type A) =
  cong polymorphic-type
    (trans
      (renameSemantic-compose (extᵗ ρ) (extᵗ τ) A)
      (renameSemantic-cong pointwise A))
  where
  pointwise :
    ∀ X →
    extᵗ ρ (extᵗ τ X) ≡ extᵗ (λ Y → ρ (τ Y)) X
  pointwise zero =
    refl
  pointwise (suc X) =
    refl

rename-substitute :
  ∀ ρ σ A →
  renameSemantic ρ (substituteSemantic σ A) ≡
  substituteSemantic (λ X → renameSemantic ρ (σ X)) A
rename-substitute ρ σ (bound-type X) =
  refl
rename-substitute ρ σ (nominal-type X) =
  refl
rename-substitute ρ σ (unbound-type X) =
  refl
rename-substitute ρ σ (base-type ι) =
  refl
rename-substitute ρ σ dynamic-type =
  refl
rename-substitute ρ σ (A ⇒ᵛ B) =
  cong₂ _⇒ᵛ_
    (rename-substitute ρ σ A)
    (rename-substitute ρ σ B)
rename-substitute ρ σ (polymorphic-type A) =
  cong polymorphic-type
    (trans
      (rename-substitute
        (extᵗ ρ) (extendSemanticSubstitution σ) A)
      (substitute-cong pointwise A))
  where
  pointwise :
    ∀ X →
    renameSemantic (extᵗ ρ)
      (extendSemanticSubstitution σ X)
      ≡
    extendSemanticSubstitution
      (λ Y → renameSemantic ρ (σ Y)) X
  pointwise zero =
    refl
  pointwise (suc X) =
    trans
      (renameSemantic-compose (extᵗ ρ) suc (σ X))
      (trans
        (renameSemantic-cong (λ Y → refl) (σ X))
        (sym (renameSemantic-compose suc ρ (σ X))))

substitute-lift :
  ∀ σ A →
  substituteSemantic (extendSemanticSubstitution σ)
    (liftSemantic A)
    ≡
  liftSemantic (substituteSemantic σ A)
substitute-lift σ A =
  trans
    (substitute-rename (extendSemanticSubstitution σ) suc A)
    (sym (rename-substitute suc σ A))

substitute-interpret :
  ∀ {η η′ σ} →
  (∀ X →
    substituteSemantic σ (semanticLookup η X) ≡
    semanticLookup η′ X) →
  ∀ A →
  substituteSemantic σ (interpretType η A) ≡
    interpretType η′ A
substitute-interpret lookup-eq (＇ X) =
  lookup-eq X
substitute-interpret lookup-eq (‵ ι) =
  refl
substitute-interpret lookup-eq ★ =
  refl
substitute-interpret lookup-eq (A ⇒ B) =
  cong₂ _⇒ᵛ_
    (substitute-interpret lookup-eq A)
    (substitute-interpret lookup-eq B)
substitute-interpret {η} {η′} {σ} lookup-eq (`∀ A) =
  cong polymorphic-type
    (substitute-interpret under-binder A)
  where
  under-binder :
    ∀ X →
    substituteSemantic
      (extendSemanticSubstitution σ)
      (semanticLookup
        (bound-type zero ∷ map liftSemantic η)
        X)
      ≡
    semanticLookup
      (bound-type zero ∷ map liftSemantic η′)
      X
  under-binder zero =
    refl
  under-binder (suc X) =
    trans
      (cong
        (substituteSemantic (extendSemanticSubstitution σ))
        (semanticLookup-map
          liftSemantic (λ Y → refl) η X))
      (trans (substitute-lift σ (semanticLookup η X))
        (trans (cong liftSemantic (lookup-eq X))
          (sym (semanticLookup-map
            liftSemantic (λ Y → refl) η′ X))))

instantiate-runtime-lookup :
  ∀ T θ X →
  substituteSemantic
    (singleSemanticSubstitution T)
    (semanticLookup
      (map liftSemantic (semanticEnvironment θ))
      X)
    ≡
  semanticLookup (semanticEnvironment θ) X
instantiate-runtime-lookup T [] X =
  refl
instantiate-runtime-lookup T (name ∷ θ) zero =
  refl
instantiate-runtime-lookup T (name ∷ θ) (suc X) =
  instantiate-runtime-lookup T θ X

instantiate-interpret :
  ∀ T θ A →
  instantiateSemantic T
    (interpretType
      (bound-type zero ∷
        map liftSemantic (semanticEnvironment θ))
      A)
    ≡
  interpretType (T ∷ semanticEnvironment θ) A
instantiate-interpret T θ A =
  substitute-interpret lookup-eq A
  where
  lookup-eq :
    ∀ X →
    substituteSemantic
      (singleSemanticSubstitution T)
      (semanticLookup
        (bound-type zero ∷
          map liftSemantic (semanticEnvironment θ))
        X)
      ≡
    semanticLookup (T ∷ semanticEnvironment θ) X
  lookup-eq zero =
    refl
  lookup-eq (suc X) =
    instantiate-runtime-lookup T θ X

type-lookup-sound :
  ∀ {Δ θ X} →
  TypeEnvironmentLength Δ θ →
  X < Δ →
  ∃[ name ] lookup θ X ≡ just name
type-lookup-sound length-empty ()
type-lookup-sound {X = zero} (length-cons length) z<s =
  _ , refl
type-lookup-sound {X = suc X} (length-cons length) (s<s X<Δ) =
  type-lookup-sound length X<Δ

semantic-name-lookup :
  ∀ {θ X name} →
  lookup θ X ≡ just name →
  semanticLookup (semanticEnvironment θ) X ≡ nominal-type name
semantic-name-lookup {θ = []} ()
semantic-name-lookup {θ = name ∷ θ} {X = zero} refl =
  refl
semantic-name-lookup
    {θ = head ∷ θ} {X = suc X} {name} eq =
  semantic-name-lookup {θ = θ} {X = X} {name = name} eq

store-lookup-sound :
  ∀ {W θ Σ X A} →
  StoreTyping W θ Σ →
  (X , A) ∈ Σ →
  ∃[ α ] (lookup θ X ≡ just (seal-name α)) ×
    AllocationRepresentation W α ⟦ A ⟧[ θ ]
store-lookup-sound (store-cons X-eq X-ok store) (here refl) =
  _ , X-eq , X-ok
store-lookup-sound (store-cons Y-eq Y-ok store) (there X∈) =
  store-lookup-sound store X∈

store-representation :
  ∀ {W θ Σ X A α} →
  StoreTyping W θ Σ →
  (X , A) ∈ Σ →
  lookup θ X ≡ just (seal-name α) →
  AllocationRepresentation W α ⟦ A ⟧[ θ ]
store-representation
    (store-cons name-eq representation store)
    (here refl) observed-eq
    with trans (sym name-eq) observed-eq
store-representation
    (store-cons name-eq representation store)
    (here refl) observed-eq
    | refl =
  representation
store-representation
    (store-cons name-eq representation store)
    (there X∈) observed-eq =
  store-representation store X∈ observed-eq

environment-lookup-sound :
  ∀ {W θ γ Γ x A} →
  EnvironmentTyping W θ γ Γ →
  Γ ∋ x ⦂ A →
  ∃[ V ] (lookup γ x ≡ just V) ×
    ValueTyping W V ⟦ A ⟧[ θ ]
environment-lookup-sound environment-empty ()
environment-lookup-sound (environment-cons V⊢ γ⊢) Z =
  _ , refl , V⊢
environment-lookup-sound (environment-cons V⊢ γ⊢) (S x∈) =
  environment-lookup-sound γ⊢ x∈

allocation-bound :
  ∀ {W k A θ} →
  WorldTyping W →
  allocation (seal-name-id k) A θ ∈ allocations W →
  k < next-name W
allocation-bound empty-world-typed ()
allocation-bound
    (allocate-world-typed {W = W} W⊢ runtime hA)
    (here refl) =
  n<1+n (next-name W)
allocation-bound
    (allocate-world-typed W⊢ runtime hA)
    (there present) =
  m<n⇒m<1+n (allocation-bound W⊢ present)

representation-functional :
  ∀ {W α A B} →
  WorldTyping W →
  AllocationRepresentation W α A →
  AllocationRepresentation W α B →
  A ≡ B
representation-functional empty-world-typed
    (allocation-representation A θ () eqA) repB
representation-functional
    (allocate-world-typed {W = W} W⊢ runtime hA)
    (allocation-representation A θ (here refl) eqA)
    (allocation-representation .A .θ (here refl) eqB) =
  trans eqA (sym eqB)
representation-functional
    (allocate-world-typed {W = W} W⊢ runtime hA)
    (allocation-representation A θ (here refl) eqA)
    (allocation-representation B σ (there present) eqB) =
  ⊥-elim (n≮n (next-name W)
    (allocation-bound W⊢ present))
representation-functional
    (allocate-world-typed {W = W} W⊢ runtime hA)
    (allocation-representation A θ (there present) eqA)
    (allocation-representation B σ (here refl) eqB) =
  ⊥-elim (n≮n (next-name W)
    (allocation-bound W⊢ present))
representation-functional
    (allocate-world-typed W⊢ runtime hA)
    (allocation-representation A θ (there presentA) eqA)
    (allocation-representation B σ (there presentB) eqB) =
  representation-functional W⊢
    (allocation-representation A θ presentA eqA)
    (allocation-representation B σ presentB eqB)

------------------------------------------------------------------------
-- World extension
------------------------------------------------------------------------

world-extension-trans :
  ∀ {W U T} →
  WorldExtension W U →
  WorldExtension U T →
  WorldExtension W T
world-extension-trans W≤U world-extension-refl =
  W≤U
world-extension-trans W≤U (world-extension-allocate U≤T) =
  world-extension-allocate (world-extension-trans W≤U U≤T)

allocated-weaken :
  ∀ {W U α} →
  WorldExtension W U →
  Allocated W α →
  Allocated U α
allocated-weaken world-extension-refl α-ok =
  α-ok
allocated-weaken (world-extension-allocate W≤U) α-ok
    with allocated-weaken W≤U α-ok
allocated-weaken (world-extension-allocate W≤U) α-ok
    | allocated α∈ =
  allocated (there α∈)

representation-weaken :
  ∀ {W U α A} →
  WorldExtension W U →
  AllocationRepresentation W α A →
  AllocationRepresentation U α A
representation-weaken world-extension-refl representation =
  representation
representation-weaken (world-extension-allocate W≤U)
    representation
    with representation-weaken W≤U representation
representation-weaken (world-extension-allocate W≤U)
    representation
    | allocation-representation A θ present eq =
  allocation-representation A θ (there present) eq

scope-weaken :
  ∀ {W U θ} →
  WorldExtension W U →
  TypeEnvironmentScoped W θ →
  TypeEnvironmentScoped U θ
scope-weaken W≤U []-scoped =
  []-scoped
scope-weaken W≤U (abstract-scoped ∷-scoped θ-ok) =
  abstract-scoped ∷-scoped scope-weaken W≤U θ-ok
scope-weaken W≤U (seal-scoped α-ok ∷-scoped θ-ok) =
  seal-scoped (allocated-weaken W≤U α-ok)
    ∷-scoped scope-weaken W≤U θ-ok

store-weaken :
  ∀ {W U θ Σ} →
  WorldExtension W U →
  StoreTyping W θ Σ →
  StoreTyping U θ Σ
store-weaken W≤U store-empty =
  store-empty
store-weaken W≤U (store-cons X-eq X-ok store) =
  store-cons X-eq
    (representation-weaken W≤U X-ok)
    (store-weaken W≤U store)

runtime-context-weaken :
  ∀ {W U Δ Σ θ} →
  WorldExtension W U →
  RuntimeContext W Δ Σ θ →
  RuntimeContext U Δ Σ θ
runtime-context-weaken W≤U
    (runtime-context length scope store) =
  runtime-context length
    (scope-weaken W≤U scope)
    (store-weaken W≤U store)

allocated-here :
  ∀ {W A θ} →
  Allocated (allocate W A θ) (freshSealName W)
allocated-here =
  allocated (here refl)

store-shift :
  ∀ {W U θ Σ} X →
  WorldExtension W U →
  StoreTyping W θ Σ →
  StoreTyping U (X ∷ θ) (⟰ᵗ Σ)
store-shift X W≤U store-empty =
  store-empty
store-shift {θ = θ} X W≤U
    (store-cons {A = A} {α = α} name-eq name-ok store) =
  store-cons name-eq
    (subst
      (AllocationRepresentation _ α)
      (sym (interpret-weaken
        (nominal-type X) (semanticEnvironment θ) A))
      (representation-weaken W≤U name-ok))
    (store-shift X W≤U store)

runtime-context-name :
  ∀ {W Δ Σ θ X} →
  TypeNameScoped W X →
  RuntimeContext W Δ Σ θ →
  RuntimeContext W (suc Δ) (⟰ᵗ Σ) (X ∷ θ)
runtime-context-name X-ok
    (runtime-context length scope store) =
  runtime-context
    (length-cons length)
    (X-ok ∷-scoped scope)
    (store-shift _ world-extension-refl store)

runtime-context-abstract :
  ∀ {W Δ Σ θ} X →
  RuntimeContext W Δ Σ θ →
  RuntimeContext W (suc Δ) (⟰ᵗ Σ) (abstract-name X ∷ θ)
runtime-context-abstract X =
  runtime-context-name abstract-scoped

runtime-context-seal :
  ∀ {W Δ Σ θ A} →
  RuntimeContext W Δ Σ θ →
  RuntimeContext
    (allocate W A θ)
    (suc Δ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
    (seal-name (freshSealName W) ∷ θ)
runtime-context-seal {W} {A = A}
    (runtime-context length scope store) =
  runtime-context
    (length-cons length)
    (seal-scoped allocated-here
      ∷-scoped scope-weaken
        (world-extension-allocate world-extension-refl)
        scope)
    (store-cons refl
      (allocation-representation A _
        (here refl)
        (interpret-weaken
          (nominal-type (seal-name (freshSealName W)))
          (semanticEnvironment _) A))
      (store-shift
        (seal-name (freshSealName W))
        (world-extension-allocate world-extension-refl)
        store))

environment-type-weaken :
  ∀ {W θ γ Γ} X →
  EnvironmentTyping W θ γ Γ →
  EnvironmentTyping W (X ∷ θ) γ (⤊ᵗ Γ)
environment-type-weaken X environment-empty =
  environment-empty
environment-type-weaken {θ = θ} X
    (environment-cons {A = A} V⊢ γ⊢)
    rewrite sym (interpret-weaken
      (nominal-type X) (semanticEnvironment θ) A) =
  environment-cons V⊢ (environment-type-weaken X γ⊢)

mutual

  value-weaken :
    ∀ {W U V A} →
    WorldExtension W U →
    WorldTyping U →
    ValueTyping W V A →
    ValueTyping U V A
  value-weaken W≤U U⊢
      (closure-typed W⊢ runtime runtime-env γ⊢ image N⊢) =
    closure-typed U⊢
      (runtime-context-weaken W≤U runtime)
      runtime-env
      (environment-weaken W≤U U⊢ γ⊢)
      image N⊢
  value-weaken W≤U U⊢ constant-typed =
    constant-typed
  value-weaken W≤U U⊢
      (tagged-typed W⊢ runtime runtime-ground γ⊢ c⊢ V⊢) =
    tagged-typed U⊢
      (runtime-context-weaken W≤U runtime)
      runtime-ground
      (environment-weaken W≤U U⊢ γ⊢)
      c⊢ (value-weaken W≤U U⊢ V⊢)
  value-weaken W≤U U⊢
      (sealed-typed W⊢ runtime γ⊢ c⊢ X-eq rep V⊢) =
    sealed-typed U⊢
      (runtime-context-weaken W≤U runtime)
      (environment-weaken W≤U U⊢ γ⊢)
      c⊢ X-eq (representation-weaken W≤U rep)
      (value-weaken W≤U U⊢ V⊢)
  value-weaken W≤U U⊢
      (function-proxy-typed W⊢ runtime runtime-env γ⊢ c⊢ V⊢) =
    function-proxy-typed U⊢
      (runtime-context-weaken W≤U runtime)
      runtime-env
      (environment-weaken W≤U U⊢ γ⊢)
      c⊢ (value-weaken W≤U U⊢ V⊢)
  value-weaken W≤U U⊢
      (type-abstraction-typed {A = A}
        W⊢ runtime runtime-env γ⊢ fresh closed image P⊢) =
    type-abstraction-typed {A = A} U⊢
      (runtime-context-weaken W≤U runtime)
      runtime-env
      (environment-weaken W≤U U⊢ γ⊢)
      fresh closed image P⊢
  value-weaken W≤U U⊢
      (forall-proxy-typed W⊢ runtime runtime-env γ⊢ c⊢ V⊢) =
    forall-proxy-typed U⊢
      (runtime-context-weaken W≤U runtime)
      runtime-env
      (environment-weaken W≤U U⊢ γ⊢)
      c⊢ (value-weaken W≤U U⊢ V⊢)
  value-weaken W≤U U⊢
      (generalized-typed W⊢ runtime runtime-env γ⊢ c⊢ V⊢) =
    generalized-typed U⊢
      (runtime-context-weaken W≤U runtime)
      runtime-env
      (environment-weaken W≤U U⊢ γ⊢)
      c⊢ (value-weaken W≤U U⊢ V⊢)

  environment-weaken :
    ∀ {W U θ γ Γ} →
    WorldExtension W U →
    WorldTyping U →
    EnvironmentTyping W θ γ Γ →
    EnvironmentTyping U θ γ Γ
  environment-weaken W≤U U⊢ environment-empty =
    environment-empty
  environment-weaken W≤U U⊢ (environment-cons V⊢ γ⊢) =
    environment-cons
      (value-weaken W≤U U⊢ V⊢)
      (environment-weaken W≤U U⊢ γ⊢)

outcome-rebase :
  ∀ {W U A o} →
  WorldExtension W U →
  OutcomeTyping U A o →
  OutcomeTyping W A o
outcome-rebase W≤U (timeout-typed U≤T) =
  timeout-typed (world-extension-trans W≤U U≤T)
outcome-rebase W≤U (blame-typed U≤T) =
  blame-typed (world-extension-trans W≤U U≤T)
outcome-rebase W≤U (return-typed U≤T T⊢ V⊢) =
  return-typed
    (world-extension-trans W≤U U≤T) T⊢ V⊢

outcome-type-transport :
  ∀ {W A B o} →
  A ≡ B →
  OutcomeTyping W A o →
  OutcomeTyping W B o
outcome-type-transport refl typed =
  typed
