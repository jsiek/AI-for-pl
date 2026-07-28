module Interpreter where

-- File Charter:
--   * Direct, fuel-indexed interpreter for compiled Nu GTSF terms.
--   * Implements the official eight-form value grammar directly: only term
--     abstractions are closures; type abstractions contain semantic values.
--   * Uses an explicit runtime allocation world and direct coercion
--     application; it does not invoke either reduction relation.
--   * Distinguishes timeout, blame, runtime error, and returned semantic value.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)

open import Coercions
  using (Coercion; Inert)
  renaming
    ( id to idᶜ
    ; _︔_ to _︔ᶜ_
    ; _↦_ to _↦ᶜ_
    ; `∀ to ∀ᶜ
    ; _! to _!ᶜ
    ; _？ to _？ᶜ
    ; seal to sealᶜ
    ; unseal to unsealᶜ
    ; gen to genᶜ
    ; inst to instᶜ
    )
open import NuTerms
  using (Term)
  renaming
    ( `_ to `ᴵ_
    ; ƛ_ to ƛᴵ_
    ; _·_ to _·ᴵ_
    ; Λ_ to Λᴵ_
    ; _• to _•ᴵ
    ; ν to νᴵ
    ; $ to $ᴵ
    ; _⊕[_]_ to _⊕ᴵ[_]_
    ; _⟨_⟩ to _⟨ᴵ_⟩
    ; blame to blameᴵ
    ; Value to SyntacticValue
    )
open import Primitives using (Const; Prim; addℕ; κℕ)
open import Types

------------------------------------------------------------------------
-- Runtime names, semantic values, and environments
------------------------------------------------------------------------

StepIndex : Set
StepIndex = ℕ

Name : Set
Name = ℕ

TypeEnvironment : Set
TypeEnvironment = List Name

data Tag : Set where
  seal-tag : Name → Tag
  base-tag : Base → Tag
  function-tag : Tag

data Value : Set where
  closure :
    Term →
    List Value →
    TypeEnvironment →
    Value

  constant :
    Const →
    Value

  tagged :
    Ty →
    TypeEnvironment →
    Value →
    Value

  sealed :
    TyVar →
    TypeEnvironment →
    Value →
    Value

  function-proxy :
    Coercion →
    Coercion →
    TypeEnvironment →
    Value →
    Value

  type-abstraction :
    (Name → Value) →
    Value

  forall-proxy :
    Coercion →
    TypeEnvironment →
    Value →
    Value

  generalized :
    Ty →
    Coercion →
    TypeEnvironment →
    Value →
    Value

Environment : Set
Environment = List Value

------------------------------------------------------------------------
-- Syntax-directed construction of the official value forms
------------------------------------------------------------------------

inert? : (c : Coercion) → Maybe (Inert c)
inert? (idᶜ A) = nothing
inert? (c ︔ᶜ d) = nothing
inert? (c ↦ᶜ d) = just (c ↦ᶜ d)
inert? (∀ᶜ c) = just (∀ᶜ c)
inert? (G !ᶜ) = just (G !ᶜ)
inert? (G ？ᶜ) = nothing
inert? (sealᶜ A X) = just (sealᶜ A X)
inert? (unsealᶜ X A) = nothing
inert? (genᶜ A c) = just (genᶜ A c)
inert? (instᶜ B c) = nothing

syntacticValue? : (M : Term) → Maybe (SyntacticValue M)
syntacticValue? (`ᴵ x) = nothing
syntacticValue? (ƛᴵ N) = just (ƛᴵ N)
syntacticValue? (L ·ᴵ M) = nothing
syntacticValue? (Λᴵ V) with syntacticValue? V
syntacticValue? (Λᴵ V) | just vV = just (Λᴵ vV)
syntacticValue? (Λᴵ V) | nothing = nothing
syntacticValue? (M •ᴵ) = nothing
syntacticValue? (νᴵ A L c) = nothing
syntacticValue? ($ᴵ κ) = just ($ᴵ κ)
syntacticValue? (L ⊕ᴵ[ op ] M) = nothing
syntacticValue? (V ⟨ᴵ c ⟩) with syntacticValue? V | inert? c
syntacticValue? (V ⟨ᴵ c ⟩) | just vV | just ic =
  just (vV ⟨ᴵ ic ⟩)
syntacticValue? (V ⟨ᴵ c ⟩) | just vV | nothing = nothing
syntacticValue? (V ⟨ᴵ c ⟩) | nothing | just ic = nothing
syntacticValue? (V ⟨ᴵ c ⟩) | nothing | nothing = nothing
syntacticValue? blameᴵ = nothing

closeValue :
  ∀ {V} →
  SyntacticValue V →
  Environment →
  TypeEnvironment →
  Value
closeValue (ƛᴵ N) γ θ =
  closure N γ θ
closeValue (Λᴵ vV) γ θ =
  type-abstraction (λ α → closeValue vV γ (α ∷ θ))
closeValue ($ᴵ κ) γ θ =
  constant κ
closeValue (vV ⟨ᴵ G !ᶜ ⟩) γ θ =
  tagged G θ (closeValue vV γ θ)
closeValue (vV ⟨ᴵ sealᶜ A X ⟩) γ θ =
  sealed X θ (closeValue vV γ θ)
closeValue (vV ⟨ᴵ p ↦ᶜ q ⟩) γ θ =
  function-proxy p q θ (closeValue vV γ θ)
closeValue (vV ⟨ᴵ ∀ᶜ c ⟩) γ θ =
  forall-proxy c θ (closeValue vV γ θ)
closeValue (vV ⟨ᴵ genᶜ A c ⟩) γ θ =
  generalized A c θ (closeValue vV γ θ)

------------------------------------------------------------------------
-- Allocation world
------------------------------------------------------------------------

record Allocation : Set where
  constructor allocation
  field
    name : Name
    declared-type : Ty
    type-scope : TypeEnvironment

open Allocation public

record World : Set where
  constructor world
  field
    next-name : Name
    allocations : List Allocation

open World public

emptyWorld : World
emptyWorld = world zero []

freshName : World → Name
freshName = next-name

allocate : World → Ty → TypeEnvironment → World
allocate (world next cells) A θ =
  world (suc next) (allocation next A θ ∷ cells)

------------------------------------------------------------------------
-- Four-way interpreter outcome
------------------------------------------------------------------------

data Timeout : Set where
  timed-out-at : World → Timeout

data Blame : Set where
  blamed-at : World → Blame

data ErrorKind : Set where
  unbound-variable : Var → ErrorKind
  unbound-type-name : TyVar → ErrorKind
  expected-function : ErrorKind
  expected-polymorphic-value : ErrorKind
  expected-value-under-type-abstraction : ErrorKind
  expected-natural : ErrorKind
  invalid-ground-tag : Ty → ErrorKind
  expected-tagged-value : ErrorKind
  expected-sealed-value : ErrorKind
  seal-name-mismatch : ErrorKind
  unreachable-runtime-bullet : ErrorKind

record Error : Set where
  constructor runtime-error
  field
    error-world : World
    error-kind : ErrorKind

record Returned : Set where
  constructor return
  field
    returned-world : World
    returned-value : Value

Outcome : Set
Outcome = Timeout ⊎ (Blame ⊎ (Error ⊎ Returned))

pattern timed W = inj₁ (timed-out-at W)
pattern blamed W = inj₂ (inj₁ (blamed-at W))
pattern failed W e = inj₂ (inj₂ (inj₁ (runtime-error W e)))
pattern returned W V = inj₂ (inj₂ (inj₂ (return W V)))

------------------------------------------------------------------------
-- Environment and tag decisions
------------------------------------------------------------------------

lookup : ∀ {A : Set} → List A → ℕ → Maybe A
lookup [] x = nothing
lookup (a ∷ as) zero = just a
lookup (a ∷ as) (suc x) = lookup as x

infix 4 _≟Tag_
_≟Tag_ : (G H : Tag) → Dec (G ≡ H)
seal-tag α ≟Tag seal-tag β with α ≟ β
seal-tag α ≟Tag seal-tag β | yes refl = yes refl
seal-tag α ≟Tag seal-tag β | no α≢β =
  no (λ { refl → α≢β refl })
seal-tag α ≟Tag base-tag ι = no (λ ())
seal-tag α ≟Tag function-tag = no (λ ())
base-tag ι ≟Tag seal-tag α = no (λ ())
base-tag ι ≟Tag base-tag ι′ with ι ≟Base ι′
base-tag ι ≟Tag base-tag ι′ | yes refl = yes refl
base-tag ι ≟Tag base-tag ι′ | no ι≢ι′ =
  no (λ { refl → ι≢ι′ refl })
base-tag ι ≟Tag function-tag = no (λ ())
function-tag ≟Tag seal-tag α = no (λ ())
function-tag ≟Tag base-tag ι = no (λ ())
function-tag ≟Tag function-tag = yes refl

tagOf : TypeEnvironment → Ty → Maybe Tag
tagOf θ (＇ X) with lookup θ X
tagOf θ (＇ X) | just α = just (seal-tag α)
tagOf θ (＇ X) | nothing = nothing
tagOf θ (‵ ι) = just (base-tag ι)
tagOf θ ★ = nothing
tagOf θ (A ⇒ B) = just function-tag
tagOf θ (`∀ A) = nothing

------------------------------------------------------------------------
-- Primitive interpretation
------------------------------------------------------------------------

applyPrimitive : World → Prim → Value → Value → Outcome
applyPrimitive W addℕ (constant (κℕ m)) (constant (κℕ n)) =
  returned W (constant (κℕ (m + n)))
applyPrimitive W addℕ V₁ V₂ =
  failed W expected-natural

------------------------------------------------------------------------
-- Direct interpretation
------------------------------------------------------------------------

mutual

  interpret :
    World →
    Environment →
    TypeEnvironment →
    Term →
    StepIndex →
    Outcome

  interpret W γ θ M zero =
    timed W

  interpret W γ θ (`ᴵ x) (suc n) with lookup γ x
  interpret W γ θ (`ᴵ x) (suc n) | just V =
    returned W V
  interpret W γ θ (`ᴵ x) (suc n) | nothing =
    failed W (unbound-variable x)

  interpret W γ θ (ƛᴵ N) (suc n) =
    returned W (closure N γ θ)

  interpret W γ θ (L ·ᴵ M) (suc n)
      with interpret W γ θ L n
  interpret W γ θ (L ·ᴵ M) (suc n) | timed W₁ =
    timed W₁
  interpret W γ θ (L ·ᴵ M) (suc n) | blamed W₁ =
    blamed W₁
  interpret W γ θ (L ·ᴵ M) (suc n) | failed W₁ e =
    failed W₁ e
  interpret W γ θ (L ·ᴵ M) (suc n) | returned W₁ V
      with interpret W₁ γ θ M n
  interpret W γ θ (L ·ᴵ M) (suc n) | returned W₁ V
      | timed W₂ =
    timed W₂
  interpret W γ θ (L ·ᴵ M) (suc n) | returned W₁ V
      | blamed W₂ =
    blamed W₂
  interpret W γ θ (L ·ᴵ M) (suc n) | returned W₁ V
      | failed W₂ e =
    failed W₂ e
  interpret W γ θ (L ·ᴵ M) (suc n) | returned W₁ V
      | returned W₂ U =
    applyValue W₂ V U n

  interpret W γ θ (Λᴵ V) (suc n) with syntacticValue? V
  interpret W γ θ (Λᴵ V) (suc n) | just vV =
    returned W (type-abstraction (λ α → closeValue vV γ (α ∷ θ)))
  interpret W γ θ (Λᴵ V) (suc n) | nothing =
    failed W expected-value-under-type-abstraction

  -- `_•` is introduced only by the small-step `ν` rule. The direct
  -- interpreter performs that instantiation inside the `ν` case instead.
  interpret W γ θ (M •ᴵ) (suc n) =
    failed W unreachable-runtime-bullet

  interpret W γ θ (νᴵ A L c) (suc n)
      with interpret W γ θ L n
  interpret W γ θ (νᴵ A L c) (suc n) | timed W₁ =
    timed W₁
  interpret W γ θ (νᴵ A L c) (suc n) | blamed W₁ =
    blamed W₁
  interpret W γ θ (νᴵ A L c) (suc n) | failed W₁ e =
    failed W₁ e
  interpret W γ θ (νᴵ A L c) (suc n) | returned W₁ V
      with instantiateValue W₂ α V n
    where
    α : Name
    α = freshName W₁

    W₂ : World
    W₂ = allocate W₁ A θ
  interpret W γ θ (νᴵ A L c) (suc n) | returned W₁ V
      | timed W₃ =
    timed W₃
  interpret W γ θ (νᴵ A L c) (suc n) | returned W₁ V
      | blamed W₃ =
    blamed W₃
  interpret W γ θ (νᴵ A L c) (suc n) | returned W₁ V
      | failed W₃ e =
    failed W₃ e
  interpret W γ θ (νᴵ A L c) (suc n) | returned W₁ V
      | returned W₃ U =
    coerceValue W₃ (freshName W₁ ∷ θ) c U n

  interpret W γ θ ($ᴵ κ) (suc n) =
    returned W (constant κ)

  interpret W γ θ (L ⊕ᴵ[ op ] M) (suc n)
      with interpret W γ θ L n
  interpret W γ θ (L ⊕ᴵ[ op ] M) (suc n) | timed W₁ =
    timed W₁
  interpret W γ θ (L ⊕ᴵ[ op ] M) (suc n) | blamed W₁ =
    blamed W₁
  interpret W γ θ (L ⊕ᴵ[ op ] M) (suc n) | failed W₁ e =
    failed W₁ e
  interpret W γ θ (L ⊕ᴵ[ op ] M) (suc n) | returned W₁ V
      with interpret W₁ γ θ M n
  interpret W γ θ (L ⊕ᴵ[ op ] M) (suc n) | returned W₁ V
      | timed W₂ =
    timed W₂
  interpret W γ θ (L ⊕ᴵ[ op ] M) (suc n) | returned W₁ V
      | blamed W₂ =
    blamed W₂
  interpret W γ θ (L ⊕ᴵ[ op ] M) (suc n) | returned W₁ V
      | failed W₂ e =
    failed W₂ e
  interpret W γ θ (L ⊕ᴵ[ op ] M) (suc n) | returned W₁ V
      | returned W₂ U =
    applyPrimitive W₂ op V U

  interpret W γ θ (M ⟨ᴵ c ⟩) (suc n)
      with interpret W γ θ M n
  interpret W γ θ (M ⟨ᴵ c ⟩) (suc n) | timed W₁ =
    timed W₁
  interpret W γ θ (M ⟨ᴵ c ⟩) (suc n) | blamed W₁ =
    blamed W₁
  interpret W γ θ (M ⟨ᴵ c ⟩) (suc n) | failed W₁ e =
    failed W₁ e
  interpret W γ θ (M ⟨ᴵ c ⟩) (suc n) | returned W₁ V =
    coerceValue W₁ θ c V n

  interpret W γ θ blameᴵ (suc n) =
    blamed W

  applyValue :
    World →
    Value →
    Value →
    StepIndex →
    Outcome

  applyValue W V U zero =
    timed W

  applyValue W (closure N γ θ) U (suc n) =
    interpret W (U ∷ γ) θ N n

  applyValue W (function-proxy p q θ V) U (suc n)
      with coerceValue W θ p U n
  applyValue W (function-proxy p q θ V) U (suc n) | timed W₁ =
    timed W₁
  applyValue W (function-proxy p q θ V) U (suc n) | blamed W₁ =
    blamed W₁
  applyValue W (function-proxy p q θ V) U (suc n)
      | failed W₁ e =
    failed W₁ e
  applyValue W (function-proxy p q θ V) U (suc n)
      | returned W₁ U′
      with applyValue W₁ V U′ n
  applyValue W (function-proxy p q θ V) U (suc n)
      | returned W₁ U′ | timed W₂ =
    timed W₂
  applyValue W (function-proxy p q θ V) U (suc n)
      | returned W₁ U′ | blamed W₂ =
    blamed W₂
  applyValue W (function-proxy p q θ V) U (suc n)
      | returned W₁ U′ | failed W₂ e =
    failed W₂ e
  applyValue W (function-proxy p q θ V) U (suc n)
      | returned W₁ U′ | returned W₂ V′ =
    coerceValue W₂ θ q V′ n

  applyValue W (type-abstraction V) U (suc n) =
    failed W expected-function
  applyValue W (constant κ) U (suc n) =
    failed W expected-function
  applyValue W (tagged G θ V) U (suc n) =
    failed W expected-function
  applyValue W (sealed X θ V) U (suc n) =
    failed W expected-function
  applyValue W (forall-proxy c θ V) U (suc n) =
    failed W expected-function
  applyValue W (generalized A c θ V) U (suc n) =
    failed W expected-function

  instantiateValue :
    World →
    Name →
    Value →
    StepIndex →
    Outcome

  instantiateValue W α V zero =
    timed W

  instantiateValue W α (type-abstraction V) (suc n) =
    returned W (V α)

  instantiateValue W α (forall-proxy c θ V) (suc n)
      with instantiateValue W α V n
  instantiateValue W α (forall-proxy c θ V) (suc n) | timed W₁ =
    timed W₁
  instantiateValue W α (forall-proxy c θ V) (suc n) | blamed W₁ =
    blamed W₁
  instantiateValue W α (forall-proxy c θ V) (suc n)
      | failed W₁ e =
    failed W₁ e
  instantiateValue W α (forall-proxy c θ V) (suc n)
      | returned W₁ U =
    coerceValue W₁ (α ∷ θ) c U n

  instantiateValue W α (generalized A c θ V) (suc n) =
    coerceValue W (α ∷ θ) c V n

  instantiateValue W α (closure N γ θ) (suc n) =
    failed W expected-polymorphic-value
  instantiateValue W α (constant κ) (suc n) =
    failed W expected-polymorphic-value
  instantiateValue W α (tagged G θ V) (suc n) =
    failed W expected-polymorphic-value
  instantiateValue W α (sealed X θ V) (suc n) =
    failed W expected-polymorphic-value
  instantiateValue W α (function-proxy p q θ V) (suc n) =
    failed W expected-polymorphic-value

  coerceValue :
    World →
    TypeEnvironment →
    Coercion →
    Value →
    StepIndex →
    Outcome

  coerceValue W θ c V zero =
    timed W

  coerceValue W θ (idᶜ A) V (suc n) =
    returned W V

  coerceValue W θ (c ︔ᶜ d) V (suc n)
      with coerceValue W θ c V n
  coerceValue W θ (c ︔ᶜ d) V (suc n) | timed W₁ =
    timed W₁
  coerceValue W θ (c ︔ᶜ d) V (suc n) | blamed W₁ =
    blamed W₁
  coerceValue W θ (c ︔ᶜ d) V (suc n) | failed W₁ e =
    failed W₁ e
  coerceValue W θ (c ︔ᶜ d) V (suc n) | returned W₁ U =
    coerceValue W₁ θ d U n

  coerceValue W θ (p ↦ᶜ q) V (suc n) =
    returned W (function-proxy p q θ V)

  coerceValue W θ (∀ᶜ c) V (suc n) =
    returned W (forall-proxy c θ V)

  coerceValue W θ (G !ᶜ) V (suc n) with tagOf θ G
  coerceValue W θ (G !ᶜ) V (suc n) | just tag =
    returned W (tagged G θ V)
  coerceValue W θ (G !ᶜ) V (suc n) | nothing =
    failed W (invalid-ground-tag G)

  coerceValue W θ (G ？ᶜ) V (suc n) with tagOf θ G
  coerceValue W θ (G ？ᶜ) V (suc n) | nothing =
    failed W (invalid-ground-tag G)
  coerceValue W θ (G ？ᶜ) (tagged H θ′ V) (suc n)
      | just expected
      with tagOf θ′ H
  coerceValue W θ (G ？ᶜ) (tagged H θ′ V) (suc n)
      | just expected | nothing =
    failed W (invalid-ground-tag H)
  coerceValue W θ (G ？ᶜ) (tagged H θ′ V) (suc n)
      | just expected | just actual
      with expected ≟Tag actual
  coerceValue W θ (G ？ᶜ) (tagged H θ′ V) (suc n)
      | just expected | just actual | yes refl =
    returned W V
  coerceValue W θ (G ？ᶜ) (tagged H θ′ V) (suc n)
      | just expected | just actual | no expected≢actual =
    blamed W
  coerceValue W θ (G ？ᶜ) (closure N γ θ′) (suc n)
      | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (type-abstraction V) (suc n)
      | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (constant κ) (suc n)
      | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (sealed X θ′ V) (suc n)
      | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (function-proxy p q θ′ V) (suc n)
      | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (forall-proxy c θ′ V) (suc n)
      | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (generalized A c θ′ V) (suc n)
      | just expected =
    failed W expected-tagged-value

  coerceValue W θ (sealᶜ A X) V (suc n) with lookup θ X
  coerceValue W θ (sealᶜ A X) V (suc n) | just α =
    returned W (sealed X θ V)
  coerceValue W θ (sealᶜ A X) V (suc n) | nothing =
    failed W (unbound-type-name X)

  coerceValue W θ (unsealᶜ X A) V (suc n) with lookup θ X
  coerceValue W θ (unsealᶜ X A) V (suc n) | nothing =
    failed W (unbound-type-name X)
  coerceValue W θ (unsealᶜ X A) (sealed Y θ′ V) (suc n)
      | just α
      with lookup θ′ Y
  coerceValue W θ (unsealᶜ X A) (sealed Y θ′ V) (suc n)
      | just α | nothing =
    failed W (unbound-type-name Y)
  coerceValue W θ (unsealᶜ X A) (sealed Y θ′ V) (suc n)
      | just α | just β
      with α ≟ β
  coerceValue W θ (unsealᶜ X A) (sealed Y θ′ V) (suc n)
      | just α | just .α | yes refl =
    returned W V
  coerceValue W θ (unsealᶜ X A) (sealed Y θ′ V) (suc n)
      | just α | just β | no α≢β =
    failed W seal-name-mismatch
  coerceValue W θ (unsealᶜ X A) (closure N γ θ′) (suc n)
      | just α =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (type-abstraction V) (suc n)
      | just α =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (constant κ) (suc n)
      | just α =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (tagged G θ′ V) (suc n)
      | just α =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (function-proxy p q θ′ V) (suc n)
      | just α =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (forall-proxy c θ′ V) (suc n)
      | just α =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (generalized B c θ′ V) (suc n)
      | just α =
    failed W expected-sealed-value

  coerceValue W θ (genᶜ A c) V (suc n) =
    returned W (generalized A c θ V)

  coerceValue W θ (instᶜ B c) V (suc n)
      with instantiateValue W₂ α V n
    where
    α : Name
    α = freshName W

    W₂ : World
    W₂ = allocate W ★ θ
  coerceValue W θ (instᶜ B c) V (suc n) | timed W₃ =
    timed W₃
  coerceValue W θ (instᶜ B c) V (suc n) | blamed W₃ =
    blamed W₃
  coerceValue W θ (instᶜ B c) V (suc n) | failed W₃ e =
    failed W₃ e
  coerceValue W θ (instᶜ B c) V (suc n) | returned W₃ U =
    coerceValue W₃ (freshName W ∷ θ) c U n

run : Term → StepIndex → Outcome
run = interpret emptyWorld [] []
