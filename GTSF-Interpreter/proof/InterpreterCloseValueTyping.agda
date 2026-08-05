module proof.InterpreterCloseValueTyping where

-- File Charter:
--   * Proves semantic typing for the proof-relevant graph of `closeValue`.
--   * Handles every official syntactic value form.
--   * Stores nested polymorphic close evidence for later direct
--     instantiation; it uses no reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Interpreter
open import Runtime.InterpreterClosedValue
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape using
  (InterpreterTerm; closure-term; type-abstraction-term;
   constant-term; coercion-application-term)
import NuTerms as N
open import Primitives using (κℕ)
open import proof.InterpreterClosedValueProof using
  (closeValue-closed; closedValue-replace)
open import proof.InterpreterSemanticTypingProperties using
  (environment-type-weaken; runtime-context-abstract;
   semantic-name-lookup; store-lookup-sound; store-representation)
open import Types
open import Coercions using
  (cast-tag; cast-seal; cast-fun; cast-all; cast-gen)

syntactic-variable-value-runtime-ground :
  ∀ {W Δ Σ Γ θ P X} →
  RuntimeContext W Δ Σ θ →
  N.Value P →
  N._∣_∣_⊢_⦂_ Δ Σ Γ P (＇ X) →
  RuntimeGround θ (＇ X)
syntactic-variable-value-runtime-ground runtime (N.ƛ P) ()
syntactic-variable-value-runtime-ground runtime (N.Λ vP) ()
syntactic-variable-value-runtime-ground runtime (N.$ (κℕ n)) ()
syntactic-variable-value-runtime-ground runtime
    (vP N.⟨ Coercions._! G ⟩) (N.⊢⟨⟩ () P⊢)
syntactic-variable-value-runtime-ground runtime
    (vP N.⟨ Coercions.seal A X ⟩)
    (N.⊢⟨⟩ (cast-seal hA X∈ allowed) P⊢)
    with store-lookup-sound (store-typing runtime) X∈
syntactic-variable-value-runtime-ground runtime
    (vP N.⟨ Coercions.seal A X ⟩)
    (N.⊢⟨⟩ (cast-seal hA X∈ allowed) P⊢)
    | α , lookup-eq , representation =
  seal-variable-ground lookup-eq
syntactic-variable-value-runtime-ground runtime
    (vP N.⟨ p Coercions.↦ q ⟩) (N.⊢⟨⟩ () P⊢)
syntactic-variable-value-runtime-ground runtime
    (vP N.⟨ Coercions.`∀ c ⟩) (N.⊢⟨⟩ () P⊢)
syntactic-variable-value-runtime-ground runtime
    (vP N.⟨ Coercions.gen A c ⟩) (N.⊢⟨⟩ () P⊢)

syntactic-ground-value-runtime-ground :
  ∀ {W Δ Σ Γ θ P G} →
  RuntimeContext W Δ Σ θ →
  N.Value P →
  N._∣_∣_⊢_⦂_ Δ Σ Γ P G →
  Ground G →
  RuntimeGround θ G
syntactic-ground-value-runtime-ground runtime vP P⊢ (＇ X) =
  syntactic-variable-value-runtime-ground runtime vP P⊢
syntactic-ground-value-runtime-ground runtime vP P⊢ (‵ ι) =
  base-ground ι
syntactic-ground-value-runtime-ground runtime vP P⊢ ★⇒★ =
  function-ground

syntacticValue-complete :
  ∀ {P} →
  (vP : N.Value P) →
  ∃[ vP′ ] syntacticValue? P ≡ yes vP′
syntacticValue-complete {P} vP
    with syntacticValue? P in decision-eq
syntacticValue-complete vP | yes vP′ =
  vP′ , refl
syntacticValue-complete vP | no ¬vP =
  ⊥-elim (¬vP vP)

closeValue-defined :
  ∀ {W Δ Σ Γ θ γ P A} →
  RuntimeContext W Δ Σ θ →
  EnvironmentTyping W θ γ Γ →
  InterpreterTerm P →
  (vP : N.Value P) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ P A →
  ∃[ U ] closeValue vP γ θ ≡ just U
closeValue-defined runtime γ⊢ (closure-term body-image)
    (N.ƛ P) (N.⊢ƛ hA P⊢) =
  _ , refl
closeValue-defined {θ = θ} runtime γ⊢
    (type-abstraction-term vImage body-image)
    (N.Λ vP) (N.⊢Λ vTyping P⊢)
    with closeValue-defined
      (runtime-context-abstract (nextAbstractName θ) runtime)
      (environment-type-weaken
        (abstract-name (nextAbstractName θ)) γ⊢)
      body-image vP P⊢
closeValue-defined {θ = θ} runtime γ⊢
    (type-abstraction-term vImage body-image)
    (N.Λ vP) (N.⊢Λ vTyping P⊢)
    | U , U-eq
    rewrite U-eq =
  _ , refl
closeValue-defined runtime γ⊢ (constant-term (κℕ n))
    (N.$ .(κℕ n)) (N.⊢$ .(κℕ n)) =
  _ , refl
closeValue-defined {θ = θ} runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions._! G ⟩)
    (N.⊢⟨⟩ (cast-tag hG gG allowed) P⊢)
    with ground? θ G
closeValue-defined {θ = θ} runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions._! G ⟩)
    (N.⊢⟨⟩ (cast-tag hG gG allowed) P⊢)
    | no not-runtime-ground =
  ⊥-elim
    (not-runtime-ground
      (syntactic-ground-value-runtime-ground runtime vP P⊢ gG))
closeValue-defined {θ = θ} runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions._! G ⟩)
    (N.⊢⟨⟩ (cast-tag hG gG allowed) P⊢)
    | yes runtime-ground
    with closeValue-defined runtime γ⊢ body-image vP P⊢
closeValue-defined {θ = θ} runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions._! G ⟩)
    (N.⊢⟨⟩ (cast-tag hG gG allowed) P⊢)
    | yes runtime-ground | U , U-eq
    rewrite U-eq =
  _ , refl
closeValue-defined {θ = θ} runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions.seal A X ⟩)
    (N.⊢⟨⟩ (cast-seal hA X∈ allowed) P⊢)
    with store-lookup-sound (store-typing runtime) X∈
closeValue-defined {θ = θ} runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions.seal A X ⟩)
    (N.⊢⟨⟩ (cast-seal hA X∈ allowed) P⊢)
    | α , name-eq , α-ok
    with closeValue-defined runtime γ⊢ body-image vP P⊢
closeValue-defined {θ = θ} runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions.seal A X ⟩)
    (N.⊢⟨⟩ (cast-seal hA X∈ allowed) P⊢)
    | α , name-eq , α-ok | U , U-eq
    rewrite name-eq | U-eq =
  _ , refl
closeValue-defined runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ p Coercions.↦ q ⟩)
    (N.⊢⟨⟩ (cast-fun p⊢ q⊢) P⊢)
    with closeValue-defined runtime γ⊢ body-image vP P⊢
closeValue-defined runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ p Coercions.↦ q ⟩)
    (N.⊢⟨⟩ (cast-fun p⊢ q⊢) P⊢)
    | U , U-eq
    rewrite U-eq =
  _ , refl
closeValue-defined runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions.`∀ c ⟩)
    (N.⊢⟨⟩ (cast-all c⊢) P⊢)
    with closeValue-defined runtime γ⊢ body-image vP P⊢
closeValue-defined runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions.`∀ c ⟩)
    (N.⊢⟨⟩ (cast-all c⊢) P⊢)
    | U , U-eq
    rewrite U-eq =
  _ , refl
closeValue-defined runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions.gen A c ⟩)
    (N.⊢⟨⟩ (cast-gen hA occurs c⊢) P⊢)
    with closeValue-defined runtime γ⊢ body-image vP P⊢
closeValue-defined runtime γ⊢
    (coercion-application-term body-image)
    (vP N.⟨ Coercions.gen A c ⟩)
    (N.⊢⟨⟩ (cast-gen hA occurs c⊢) P⊢)
    | U , U-eq
    rewrite U-eq =
  _ , refl

closedValue-typing :
  ∀ {W Δ Σ Γ θ γ P U A}
    {vP : N.Value P} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ →
  RuntimeTypeEnvironment θ →
  EnvironmentTyping W θ γ Γ →
  InterpreterTerm P →
  N._∣_∣_⊢_⦂_ Δ Σ Γ P A →
  ClosedValue γ θ vP U →
  ValueTyping W U ⟦ A ⟧[ θ ]
closedValue-typing W⊢ runtime runtime-env γ⊢ (closure-term body-image)
    (N.⊢ƛ hA P⊢) closed-closure =
  closure-typed W⊢ runtime runtime-env γ⊢
    body-image P⊢
closedValue-typing W⊢ runtime runtime-env γ⊢
    (type-abstraction-term vImage body-image)
    (N.⊢Λ vTyping P⊢)
    (closed-type-abstraction closed-fresh closed) =
  type-abstraction-typed W⊢ runtime runtime-env γ⊢
    closed-fresh closed
    body-image P⊢
closedValue-typing W⊢ runtime runtime-env γ⊢
    (constant-term (κℕ n))
    (N.⊢$ .(κℕ n)) (closed-constant .(κℕ n)) =
  constant-typed
closedValue-typing W⊢ runtime runtime-env γ⊢
    (coercion-application-term body-image)
    (N.⊢⟨⟩ (cast-tag hG gG allowed) P⊢)
    (closed-tagged {vV = vP} closed) =
  tagged-typed W⊢ runtime
    (syntactic-ground-value-runtime-ground runtime vP P⊢ gG)
    γ⊢
    (cast-tag hG gG allowed)
    (closedValue-typing W⊢ runtime runtime-env γ⊢
      body-image P⊢ closed)
closedValue-typing {θ = θ} W⊢ runtime runtime-env γ⊢
    (coercion-application-term body-image)
    (N.⊢⟨⟩
      (cast-seal {μ = μ} {α = X} {A = A}
        hA X∈ allowed)
      P⊢)
    (closed-sealed name-eq closed) =
  subst
    (ValueTyping _ _)
    (sym (semantic-name-lookup {θ = θ} name-eq))
    (sealed-typed {X = X} {A = A} {μ = μ}
      W⊢ runtime γ⊢
      (cast-seal hA X∈ allowed) name-eq
      (store-representation
        (store-typing runtime) X∈ name-eq)
      (closedValue-typing W⊢ runtime runtime-env γ⊢
        body-image P⊢ closed))
closedValue-typing W⊢ runtime runtime-env γ⊢
    (coercion-application-term body-image)
    (N.⊢⟨⟩ (cast-fun p⊢ q⊢) P⊢)
    (closed-function-proxy closed) =
  function-proxy-typed W⊢ runtime runtime-env γ⊢
    (cast-fun p⊢ q⊢)
    (closedValue-typing W⊢ runtime runtime-env γ⊢
      body-image P⊢ closed)
closedValue-typing W⊢ runtime runtime-env γ⊢
    (coercion-application-term body-image)
    (N.⊢⟨⟩ (cast-all c⊢) P⊢)
    (closed-forall-proxy closed) =
  forall-proxy-typed W⊢ runtime runtime-env γ⊢ (cast-all c⊢)
    (closedValue-typing W⊢ runtime runtime-env γ⊢
      body-image P⊢ closed)
closedValue-typing W⊢ runtime runtime-env γ⊢
    (coercion-application-term body-image)
    (N.⊢⟨⟩ (cast-gen hA occurs c⊢) P⊢)
    (closed-generalized closed) =
  generalized-typed W⊢ runtime runtime-env γ⊢
    (cast-gen hA occurs c⊢)
    (closedValue-typing W⊢ runtime runtime-env γ⊢
      body-image P⊢ closed)

closeValue-preserves-semantic-typing :
  ∀ {W Δ Σ Γ θ γ P A} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ →
  RuntimeTypeEnvironment θ →
  EnvironmentTyping W θ γ Γ →
  InterpreterTerm P →
  (vP : N.Value P) →
  N._∣_∣_⊢_⦂_ Δ Σ Γ P A →
  ∃[ U ] (closeValue vP γ θ ≡ just U) ×
    ValueTyping W U ⟦ A ⟧[ θ ]
closeValue-preserves-semantic-typing
    W⊢ runtime runtime-env γ⊢ image vP P⊢
    with closeValue-defined runtime γ⊢ image vP P⊢
closeValue-preserves-semantic-typing
    W⊢ runtime runtime-env γ⊢ image vP P⊢
    | U , close-eq =
  U , close-eq ,
    closedValue-typing W⊢ runtime runtime-env γ⊢ image P⊢
      (closeValue-closed vP close-eq)

substituteName-closedValue-typing :
  ∀ {W Δ Σ Γ θ θ′ γ P U A X α}
    {vP : N.Value P} →
  WorldTyping W →
  RuntimeContext W Δ Σ θ′ →
  RuntimeTypeEnvironment θ′ →
  EnvironmentTyping W θ′ γ Γ →
  InterpreterTerm P →
  N._∣_∣_⊢_⦂_ Δ Σ Γ P A →
  abstract-name X ∈ θ →
  replaceName X α θ ≡ θ′ →
  ClosedValue γ θ vP U →
  ValueTyping W (substituteName X α U) ⟦ A ⟧[ θ′ ]
substituteName-closedValue-typing
    {γ = γ} {U = U} {X = X} {α = α} {vP = vP}
    W⊢ runtime runtime-env γ⊢ image P⊢ X∈ replace-eq closed =
  closedValue-typing W⊢ runtime runtime-env γ⊢ image P⊢
    (subst
      (λ θ′ →
        ClosedValue γ θ′ vP (substituteName X α U))
      replace-eq
      (closedValue-replace X∈ closed))
