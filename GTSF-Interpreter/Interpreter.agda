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
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≟_)
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

-- `Name` ranges over the abstract variables bound by `ΛX`.
data Name : Set where
  type-name : ℕ → Name

-- `SealName` ranges over the fresh nominal names allocated by `ν`.
data SealName : Set where
  seal-name-id : ℕ → SealName

data TypeName : Set where
  abstract-name : Name → TypeName
  seal-name : SealName → TypeName

infix 4 _≟Name_
_≟Name_ : (X Y : Name) → Dec (X ≡ Y)
type-name X ≟Name type-name Y with X ≟ Y
type-name X ≟Name type-name Y | yes refl = yes refl
type-name X ≟Name type-name Y | no X≢Y =
  no (λ { refl → X≢Y refl })

infix 4 _≟SealName_
_≟SealName_ : (α β : SealName) → Dec (α ≡ β)
seal-name-id α ≟SealName seal-name-id β with α ≟ β
seal-name-id α ≟SealName seal-name-id β | yes refl = yes refl
seal-name-id α ≟SealName seal-name-id β | no α≢β =
  no (λ { refl → α≢β refl })

TypeEnvironment : Set
TypeEnvironment = List TypeName

data Tag : Set where
  variable-tag : TypeName → Tag
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
    ∀ {G} →
    Ground G →
    TypeEnvironment →
    Value →
    Value

  sealed :
    SealName →
    Value →
    Value

  function-proxy :
    Coercion →
    Coercion →
    TypeEnvironment →
    Value →
    Value

  type-abstraction :
    Name →
    Value →
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

lookup : ∀ {A : Set} → List A → ℕ → Maybe A
lookup [] x = nothing
lookup (a ∷ as) zero = just a
lookup (a ∷ as) (suc x) = lookup as x

------------------------------------------------------------------------
-- Syntax-directed construction of the official value forms
------------------------------------------------------------------------

ground? : (G : Ty) → Dec (Ground G)
ground? (＇ X) = yes (＇ X)
ground? (‵ ι) = yes (‵ ι)
ground? ★ = no (λ ())
ground? (A ⇒ B) with A ≟Ty ★ | B ≟Ty ★
ground? (A ⇒ B) | yes refl | yes refl = yes ★⇒★
ground? (A ⇒ B) | no A≢★ | B≟★ =
  no (λ { ★⇒★ → A≢★ refl })
ground? (A ⇒ B) | yes refl | no B≢★ =
  no (λ { ★⇒★ → B≢★ refl })
ground? (`∀ A) = no (λ ())

inert? : (c : Coercion) → Dec (Inert c)
inert? (idᶜ A) = no (λ ())
inert? (c ︔ᶜ d) = no (λ ())
inert? (c ↦ᶜ d) = yes (c ↦ᶜ d)
inert? (∀ᶜ c) = yes (∀ᶜ c)
inert? (G !ᶜ) = yes (G !ᶜ)
inert? (G ？ᶜ) = no (λ ())
inert? (sealᶜ A X) = yes (sealᶜ A X)
inert? (unsealᶜ X A) = no (λ ())
inert? (genᶜ A c) = yes (genᶜ A c)
inert? (instᶜ B c) = no (λ ())

syntacticValue? : (M : Term) → Dec (SyntacticValue M)
syntacticValue? (`ᴵ x) = no (λ ())
syntacticValue? (ƛᴵ N) = yes (ƛᴵ N)
syntacticValue? (L ·ᴵ M) = no (λ ())
syntacticValue? (Λᴵ V) with syntacticValue? V
syntacticValue? (Λᴵ V) | yes vV = yes (Λᴵ vV)
syntacticValue? (Λᴵ V) | no ¬vV =
  no (λ { (Λᴵ vV) → ¬vV vV })
syntacticValue? (M •ᴵ) = no (λ ())
syntacticValue? (νᴵ A L c) = no (λ ())
syntacticValue? ($ᴵ κ) = yes ($ᴵ κ)
syntacticValue? (L ⊕ᴵ[ op ] M) = no (λ ())
syntacticValue? (V ⟨ᴵ c ⟩) with syntacticValue? V | inert? c
syntacticValue? (V ⟨ᴵ c ⟩) | yes vV | yes ic =
  yes (vV ⟨ᴵ ic ⟩)
syntacticValue? (V ⟨ᴵ c ⟩) | no ¬vV | ic =
  no (λ { (vV ⟨ᴵ i ⟩) → ¬vV vV })
syntacticValue? (V ⟨ᴵ c ⟩) | yes vV | no ¬ic =
  no (λ { (vV′ ⟨ᴵ ic ⟩) → ¬ic ic })
syntacticValue? blameᴵ = no (λ ())

nextAbstractIndex : TypeEnvironment → ℕ
nextAbstractIndex [] = zero
nextAbstractIndex (abstract-name (type-name X) ∷ θ) =
  suc X ⊔ nextAbstractIndex θ
nextAbstractIndex (seal-name α ∷ θ) =
  nextAbstractIndex θ

nextAbstractName : TypeEnvironment → Name
nextAbstractName θ =
  type-name (nextAbstractIndex θ)

closeValue :
  ∀ {V} →
  SyntacticValue V →
  Environment →
  TypeEnvironment →
  Maybe Value
closeValue (ƛᴵ N) γ θ =
  just (closure N γ θ)
closeValue (Λᴵ vV) γ θ
    with closeValue vV γ (abstract-name X ∷ θ)
  where
  X : Name
  X = nextAbstractName θ
closeValue (Λᴵ vV) γ θ | just V =
  just (type-abstraction (nextAbstractName θ) V)
closeValue (Λᴵ vV) γ θ | nothing =
  nothing
closeValue ($ᴵ κ) γ θ =
  just (constant κ)
closeValue (vV ⟨ᴵ G !ᶜ ⟩) γ θ
    with ground? G | closeValue vV γ θ
closeValue (vV ⟨ᴵ G !ᶜ ⟩) γ θ | yes gG | just V =
  just (tagged gG θ V)
closeValue (vV ⟨ᴵ G !ᶜ ⟩) γ θ | yes gG | nothing =
  nothing
closeValue (vV ⟨ᴵ G !ᶜ ⟩) γ θ | no ¬gG | result =
  nothing
closeValue (vV ⟨ᴵ sealᶜ A X ⟩) γ θ
    with lookup θ X | closeValue vV γ θ
closeValue (vV ⟨ᴵ sealᶜ A X ⟩) γ θ
    | just (seal-name α) | just V =
  just (sealed α V)
closeValue (vV ⟨ᴵ sealᶜ A X ⟩) γ θ
    | just (seal-name α) | nothing =
  nothing
closeValue (vV ⟨ᴵ sealᶜ A X ⟩) γ θ
    | just (abstract-name Y) | result =
  nothing
closeValue (vV ⟨ᴵ sealᶜ A X ⟩) γ θ | nothing | result =
  nothing
closeValue (vV ⟨ᴵ p ↦ᶜ q ⟩) γ θ with closeValue vV γ θ
closeValue (vV ⟨ᴵ p ↦ᶜ q ⟩) γ θ | just V =
  just (function-proxy p q θ V)
closeValue (vV ⟨ᴵ p ↦ᶜ q ⟩) γ θ | nothing =
  nothing
closeValue (vV ⟨ᴵ ∀ᶜ c ⟩) γ θ with closeValue vV γ θ
closeValue (vV ⟨ᴵ ∀ᶜ c ⟩) γ θ | just V =
  just (forall-proxy c θ V)
closeValue (vV ⟨ᴵ ∀ᶜ c ⟩) γ θ | nothing =
  nothing
closeValue (vV ⟨ᴵ genᶜ A c ⟩) γ θ with closeValue vV γ θ
closeValue (vV ⟨ᴵ genᶜ A c ⟩) γ θ | just V =
  just (generalized A c θ V)
closeValue (vV ⟨ᴵ genᶜ A c ⟩) γ θ | nothing =
  nothing

replaceName :
  Name →
  SealName →
  TypeEnvironment →
  TypeEnvironment
replaceName X α [] = []
replaceName X α (abstract-name Y ∷ θ) with X ≟Name Y
replaceName X α (abstract-name .X ∷ θ) | yes refl =
  seal-name α ∷ replaceName X α θ
replaceName X α (abstract-name Y ∷ θ) | no X≢Y =
  abstract-name Y ∷ replaceName X α θ
replaceName X α (seal-name β ∷ θ) =
  seal-name β ∷ replaceName X α θ

substituteName : Name → SealName → Value → Value
substituteName X α (closure N γ θ) =
  closure N γ (replaceName X α θ)
substituteName X α (constant κ) =
  constant κ
substituteName X α (tagged gG θ V) =
  tagged gG (replaceName X α θ) (substituteName X α V)
substituteName X α (sealed β V) =
  sealed β (substituteName X α V)
substituteName X α (function-proxy p q θ V) =
  function-proxy p q (replaceName X α θ) (substituteName X α V)
substituteName X α (type-abstraction Y V) with X ≟Name Y
substituteName X α (type-abstraction .X V) | yes refl =
  type-abstraction X V
substituteName X α (type-abstraction Y V) | no X≢Y =
  type-abstraction Y (substituteName X α V)
substituteName X α (forall-proxy c θ V) =
  forall-proxy c (replaceName X α θ) (substituteName X α V)
substituteName X α (generalized A c θ V) =
  generalized A c (replaceName X α θ) (substituteName X α V)

------------------------------------------------------------------------
-- Allocation world
------------------------------------------------------------------------

record Allocation : Set where
  constructor allocation
  field
    name : SealName
    declared-type : Ty
    type-scope : TypeEnvironment

open Allocation public

record World : Set where
  constructor world
  field
    next-name : ℕ
    allocations : List Allocation

open World public

emptyWorld : World
emptyWorld = world zero []

freshSealName : World → SealName
freshSealName W =
  seal-name-id (next-name W)

allocate : World → Ty → TypeEnvironment → World
allocate (world next cells) A θ =
  world (suc next) (allocation (seal-name-id next) A θ ∷ cells)

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
  expected-runtime-seal-name : ErrorKind
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

infix 4 _≟TypeName_
_≟TypeName_ : (X Y : TypeName) → Dec (X ≡ Y)
abstract-name X ≟TypeName abstract-name Y with X ≟Name Y
abstract-name X ≟TypeName abstract-name Y | yes refl = yes refl
abstract-name X ≟TypeName abstract-name Y | no X≢Y =
  no (λ { refl → X≢Y refl })
abstract-name X ≟TypeName seal-name α = no (λ ())
seal-name α ≟TypeName abstract-name X = no (λ ())
seal-name α ≟TypeName seal-name β with α ≟SealName β
seal-name α ≟TypeName seal-name β | yes refl = yes refl
seal-name α ≟TypeName seal-name β | no α≢β =
  no (λ { refl → α≢β refl })

infix 4 _≟Tag_
_≟Tag_ : (G H : Tag) → Dec (G ≡ H)
variable-tag X ≟Tag variable-tag Y with X ≟TypeName Y
variable-tag X ≟Tag variable-tag Y | yes refl = yes refl
variable-tag X ≟Tag variable-tag Y | no X≢Y =
  no (λ { refl → X≢Y refl })
variable-tag X ≟Tag base-tag ι = no (λ ())
variable-tag X ≟Tag function-tag = no (λ ())
base-tag ι ≟Tag variable-tag X = no (λ ())
base-tag ι ≟Tag base-tag ι′ with ι ≟Base ι′
base-tag ι ≟Tag base-tag ι′ | yes refl = yes refl
base-tag ι ≟Tag base-tag ι′ | no ι≢ι′ =
  no (λ { refl → ι≢ι′ refl })
base-tag ι ≟Tag function-tag = no (λ ())
function-tag ≟Tag variable-tag X = no (λ ())
function-tag ≟Tag base-tag ι = no (λ ())
function-tag ≟Tag function-tag = yes refl

tagOf : ∀ {G} → TypeEnvironment → Ground G → Maybe Tag
tagOf θ (＇ X) with lookup θ X
tagOf θ (＇ X) | just name = just (variable-tag name)
tagOf θ (＇ X) | nothing = nothing
tagOf θ (‵ ι) = just (base-tag ι)
tagOf θ ★⇒★ = just function-tag

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
  interpret W γ θ (Λᴵ V) (suc n) | no ¬vV =
    failed W expected-value-under-type-abstraction
  interpret W γ θ (Λᴵ V) (suc n) | yes vV
      with closeValue (Λᴵ vV) γ θ
  interpret W γ θ (Λᴵ V) (suc n) | yes vV | just U =
    returned W U
  interpret W γ θ (Λᴵ V) (suc n) | yes vV | nothing =
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
    α : SealName
    α = freshSealName W₁

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
    coerceValue W₃ (seal-name (freshSealName W₁) ∷ θ) c U n

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

  applyValue W (type-abstraction X V) U (suc n) =
    failed W expected-function
  applyValue W (constant κ) U (suc n) =
    failed W expected-function
  applyValue W (tagged gG θ V) U (suc n) =
    failed W expected-function
  applyValue W (sealed α V) U (suc n) =
    failed W expected-function
  applyValue W (forall-proxy c θ V) U (suc n) =
    failed W expected-function
  applyValue W (generalized A c θ V) U (suc n) =
    failed W expected-function

  instantiateValue :
    World →
    SealName →
    Value →
    StepIndex →
    Outcome

  instantiateValue W α V zero =
    timed W

  instantiateValue W α (type-abstraction X V) (suc n) =
    returned W (substituteName X α V)

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
    coerceValue W₁ (seal-name α ∷ θ) c U n

  instantiateValue W α (generalized A c θ V) (suc n) =
    coerceValue W (seal-name α ∷ θ) c V n

  instantiateValue W α (closure N γ θ) (suc n) =
    failed W expected-polymorphic-value
  instantiateValue W α (constant κ) (suc n) =
    failed W expected-polymorphic-value
  instantiateValue W α (tagged gG θ V) (suc n) =
    failed W expected-polymorphic-value
  instantiateValue W α (sealed β V) (suc n) =
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

  coerceValue W θ (G !ᶜ) V (suc n) with ground? G
  coerceValue W θ (G !ᶜ) V (suc n) | no ¬gG =
    failed W (invalid-ground-tag G)
  coerceValue W θ (G !ᶜ) V (suc n) | yes gG
      with tagOf θ gG
  coerceValue W θ (G !ᶜ) V (suc n) | yes gG | just tag =
    returned W (tagged gG θ V)
  coerceValue W θ (G !ᶜ) V (suc n) | yes gG | nothing =
    failed W (invalid-ground-tag G)

  coerceValue W θ (G ？ᶜ) V (suc n) with ground? G
  coerceValue W θ (G ？ᶜ) V (suc n) | no ¬gG =
    failed W (invalid-ground-tag G)
  coerceValue W θ (G ？ᶜ) V (suc n) | yes gG
      with tagOf θ gG
  coerceValue W θ (G ？ᶜ) V (suc n) | yes gG | nothing =
    failed W (invalid-ground-tag G)
  coerceValue W θ (G ？ᶜ) (tagged {G = H} gH θ′ V) (suc n)
      | yes gG | just expected
      with tagOf θ′ gH
  coerceValue W θ (G ？ᶜ) (tagged {G = H} gH θ′ V) (suc n)
      | yes gG | just expected | nothing =
    failed W (invalid-ground-tag H)
  coerceValue W θ (G ？ᶜ) (tagged {G = H} gH θ′ V) (suc n)
      | yes gG | just expected | just actual
      with expected ≟Tag actual
  coerceValue W θ (G ？ᶜ) (tagged {G = H} gH θ′ V) (suc n)
      | yes gG | just expected | just actual | yes refl =
    returned W V
  coerceValue W θ (G ？ᶜ) (tagged {G = H} gH θ′ V) (suc n)
      | yes gG | just expected | just actual | no expected≢actual =
    blamed W
  coerceValue W θ (G ？ᶜ) (closure N γ θ′) (suc n)
      | yes gG | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (type-abstraction X V) (suc n)
      | yes gG | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (constant κ) (suc n)
      | yes gG | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (sealed α V) (suc n)
      | yes gG | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (function-proxy p q θ′ V) (suc n)
      | yes gG | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (forall-proxy c θ′ V) (suc n)
      | yes gG | just expected =
    failed W expected-tagged-value
  coerceValue W θ (G ？ᶜ) (generalized A c θ′ V) (suc n)
      | yes gG | just expected =
    failed W expected-tagged-value

  coerceValue W θ (sealᶜ A X) V (suc n) with lookup θ X
  coerceValue W θ (sealᶜ A X) V (suc n)
      | just (seal-name α) =
    returned W (sealed α V)
  coerceValue W θ (sealᶜ A X) V (suc n)
      | just (abstract-name Y) =
    failed W expected-runtime-seal-name
  coerceValue W θ (sealᶜ A X) V (suc n) | nothing =
    failed W (unbound-type-name X)

  coerceValue W θ (unsealᶜ X A) V (suc n) with lookup θ X
  coerceValue W θ (unsealᶜ X A) V (suc n) | nothing =
    failed W (unbound-type-name X)
  coerceValue W θ (unsealᶜ X A) V (suc n)
      | just (abstract-name Y) =
    failed W expected-runtime-seal-name
  coerceValue W θ (unsealᶜ X A) (sealed β V) (suc n)
      | just (seal-name α)
      with α ≟SealName β
  coerceValue W θ (unsealᶜ X A) (sealed .α V) (suc n)
      | just (seal-name α) | yes refl =
    returned W V
  coerceValue W θ (unsealᶜ X A) (sealed β V) (suc n)
      | just (seal-name α) | no α≢β =
    failed W seal-name-mismatch
  coerceValue W θ (unsealᶜ X A) (closure N γ θ′) (suc n)
      | just (seal-name α) =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (type-abstraction Y V) (suc n)
      | just (seal-name α) =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (constant κ) (suc n)
      | just (seal-name α) =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (tagged gG θ′ V) (suc n)
      | just (seal-name α) =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (function-proxy p q θ′ V) (suc n)
      | just (seal-name α) =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (forall-proxy c θ′ V) (suc n)
      | just (seal-name α) =
    failed W expected-sealed-value
  coerceValue W θ (unsealᶜ X A) (generalized B c θ′ V) (suc n)
      | just (seal-name α) =
    failed W expected-sealed-value

  coerceValue W θ (genᶜ A c) V (suc n) =
    returned W (generalized A c θ V)

  coerceValue W θ (instᶜ B c) V (suc n)
      with instantiateValue W₂ α V n
    where
    α : SealName
    α = freshSealName W

    W₂ : World
    W₂ = allocate W ★ θ
  coerceValue W θ (instᶜ B c) V (suc n) | timed W₃ =
    timed W₃
  coerceValue W θ (instᶜ B c) V (suc n) | blamed W₃ =
    blamed W₃
  coerceValue W θ (instᶜ B c) V (suc n) | failed W₃ e =
    failed W₃ e
  coerceValue W θ (instᶜ B c) V (suc n) | returned W₃ U =
    coerceValue W₃ (seal-name (freshSealName W) ∷ θ) c U n

run : Term → StepIndex → Outcome
run = interpret emptyWorld [] []
