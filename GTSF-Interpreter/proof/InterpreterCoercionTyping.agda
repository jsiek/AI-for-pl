module proof.InterpreterCoercionTyping where

-- File Charter:
--   * Supplies tag and representation lemmas used by typed coercion
--     interpretation.
--   * Separates coercion-local canonical facts from the mutual interpreter
--     typing recursion.
--   * Contains no reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Product using (_,_; ∃; ∃-syntax)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import proof.InterpreterSemanticTypingProperties using
  (semantic-name-lookup; type-lookup-sound)
open import Types

tagSemanticType : Tag → SemanticType
tagSemanticType (variable-tag X) = nominal-type X
tagSemanticType (base-tag ι) = base-type ι
tagSemanticType function-tag = dynamic-type ⇒ᵛ dynamic-type

ground?-complete :
  ∀ {θ G} →
  (runtime-ground : RuntimeGround θ G) →
  ∃[ runtime-ground′ ] ground? θ G ≡ yes runtime-ground′
ground?-complete {θ} {G} runtime-ground
    with ground? θ G in decision-eq
ground?-complete runtime-ground | yes runtime-ground′ =
  runtime-ground′ , refl
ground?-complete runtime-ground | no not-runtime-ground =
  ⊥-elim (not-runtime-ground runtime-ground)

runtime-variable-ground :
  ∀ {Δ θ X} →
  RuntimeTypeEnvironment θ →
  TypeEnvironmentLength Δ θ →
  X < Δ →
  ∃[ α ] lookup θ X ≡ just (seal-name α)
runtime-variable-ground runtime-type-empty length-empty ()
runtime-variable-ground {X = zero} (runtime-type-seal runtime-env)
    (length-cons length) z<s =
  _ , refl
runtime-variable-ground {X = suc X} (runtime-type-seal runtime-env)
    (length-cons length) (s<s X<Δ) =
  runtime-variable-ground runtime-env length X<Δ

runtime-ground-from-typing :
  ∀ {W Δ Σ θ G} →
  RuntimeTypeEnvironment θ →
  RuntimeContext W Δ Σ θ →
  WfTy Δ G →
  Ground G →
  RuntimeGround θ G
runtime-ground-from-typing runtime-env runtime
    (wfVar X<Δ) (＇ X)
    with runtime-variable-ground runtime-env
      (type-length runtime) X<Δ
runtime-ground-from-typing runtime-env runtime
    (wfVar X<Δ) (＇ X) | α , lookup-eq =
  seal-variable-ground lookup-eq
runtime-ground-from-typing runtime-env runtime wfBase (‵ ι) =
  base-ground ι
runtime-ground-from-typing runtime-env runtime
    (wf⇒ wf★ wf★) ★⇒★ =
  function-ground

tagOf-complete :
  ∀ {W Δ Σ θ G} →
  RuntimeContext W Δ Σ θ →
  WfTy Δ G →
  (gG : Ground G) →
  ∃[ tag ] tagOf θ gG ≡ just tag
tagOf-complete runtime (wfVar X<Δ) (＇ X)
    with type-lookup-sound (type-length runtime) X<Δ
tagOf-complete runtime (wfVar X<Δ) (＇ X)
    | name , name-eq
    rewrite name-eq =
  variable-tag name , refl
tagOf-complete runtime wfBase (‵ ι) =
  base-tag ι , refl
tagOf-complete runtime (wf⇒ wf★ wf★) ★⇒★ =
  function-tag , refl

tagOf-sound :
  ∀ {θ G tag} →
  (gG : Ground G) →
  tagOf θ gG ≡ just tag →
  ⟦ G ⟧[ θ ] ≡ tagSemanticType tag
tagOf-sound {θ} (＇ X) eq with lookup θ X in name-eq
tagOf-sound {θ} (＇ X) () | nothing
tagOf-sound {θ} (＇ X) refl | just name =
  semantic-name-lookup {θ = θ} {X = X} {name = name} name-eq
tagOf-sound (‵ ι) refl =
  refl
tagOf-sound ★⇒★ refl =
  refl

matching-tags-type-eq :
  ∀ {θ θ′ G H tag}
    (gG : Ground G) (gH : Ground H) →
  tagOf θ gG ≡ just tag →
  tagOf θ′ gH ≡ just tag →
  ⟦ G ⟧[ θ ] ≡ ⟦ H ⟧[ θ′ ]
matching-tags-type-eq gG gH G-eq H-eq =
  trans (tagOf-sound gG G-eq)
    (sym (tagOf-sound gH H-eq))
