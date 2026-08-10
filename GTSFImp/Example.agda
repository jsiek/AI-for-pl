module Example where

-- File Charter:
--   * Closed examples that exercise inst, gen, variable-ground
--     injection/projection, the empty universal fallback, and blame from a
--     non-parametric function.
--   * Each example includes a typing derivation and an executable evaluation
--     check.

open import Data.Bool using (Bool; false; true)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (store-empty)
open import Consistency
open import Primitives
open import CastTerms
open import Reduction
open import Eval
import TermCtx

------------------------------------------------------------------------
-- Shared types, terms, and casts
------------------------------------------------------------------------

∅ : Ctx
∅ = ⟨ 0 , store-empty , [] ⟩

X⇒X : Ty 1
X⇒X = ＇ 0 ⇒ ＇ 0

ℕᵗ : Ty 0
ℕᵗ = ‵ `ℕ

𝔹ᵗ : Ty 0
𝔹ᵗ = ‵ `𝔹

instance
  X∈X⇒X-instance : 0 ∈ᵗ X⇒X
  X∈X⇒X-instance = ∈-fun-left var-∈

polyId : Term 0
polyId = Λ (ƛ (` 0))

polyId-⊢ : ∅ ⊢ polyId ⦂ `∀ X⇒X
polyId-⊢ = ⊢Λ (ƛ (` 0)) (⊢ƛ (⊢` TermCtx.Z))

id★ : Term 0
id★ = ƛ (` 0)

id★-⊢ : ∅ ⊢ id★ ⦂ (★ ⇒ ★)
id★-⊢ = ⊢ƛ (⊢` TermCtx.Z)

nat : ℕ → Term 0
nat n = $ (κℕ n)

nat-⊢ : ∀ n → ∅ ⊢ nat n ⦂ ℕᵗ
nat-⊢ n = ⊢$ (κℕ n)

bool : Bool → Term 0
bool b = $ (κ𝔹 b)

bool-⊢ : ∀ b → ∅ ⊢ bool b ⦂ 𝔹ᵗ
bool-⊢ b = ⊢$ (κ𝔹 b)

ℕ! : ℕᵗ ∼ ★
ℕ! = id (‵ `ℕ) !

ℕ? : ★ ∼ ℕᵗ
ℕ? = ？ (id (‵ `ℕ))

nat★ : ℕ → Term 0
nat★ n = nat n ⟨ ℕ! ⟩

nat★-⊢ : ∀ n → ∅ ⊢ nat★ n ⦂ ★
nat★-⊢ n = ⊢⟨⟩ (nat-⊢ n) ℕ!

------------------------------------------------------------------------
-- The empty universal fallback eagerly blames
------------------------------------------------------------------------

UniversalGround : Ty 0
UniversalGround = `∀ ★

Bottom : Ty 0
Bottom = `∀ (＇ 0)

ℕ!¹ : _∼_ {Δ = 1} (‵ `ℕ) ★
ℕ!¹ = id (‵ `ℕ) !

universalDynamic : Term 0
universalDynamic = Λ (($ (κℕ 0)) ⟨ ℕ!¹ ⟩)

universalDynamic-⊢ : ∅ ⊢ universalDynamic ⦂ UniversalGround
universalDynamic-⊢ =
  ⊢Λ (($ (κℕ 0)) 《 inj 》) (⊢⟨⟩ (⊢$ (κℕ 0)) ℕ!¹)

botIntroExample : Term 0
botIntroExample =
  universalDynamic ⟨ bot-intro {μ = idᶜ {Δ = 0}} ⟩

botIntroExample-⊢ : ∅ ⊢ botIntroExample ⦂ Bottom
botIntroExample-⊢ = ⊢⟨⟩ universalDynamic-⊢ bot-intro

botIntroExample-→ : botIntroExample —→ blame
botIntroExample-→ =
  blame-bot-intro (Λ (($ (κℕ 0)) 《 inj 》))

UniversalGround! : UniversalGround ∼ ★
UniversalGround! =
  idᵍ ∀★ !

star∼Bottom : ★ ∼ Bottom
star∼Bottom = ？ bot-intro

botFromStarExample : Term 0
botFromStarExample =
  (universalDynamic ⟨ UniversalGround! ⟩) ⟨ star∼Bottom ⟩

botFromStarExample-⊢ : ∅ ⊢ botFromStarExample ⦂ Bottom
botFromStarExample-⊢ =
  ⊢⟨⟩ (⊢⟨⟩ universalDynamic-⊢ UniversalGround!) star∼Bottom

------------------------------------------------------------------------
-- Instantiate polymorphic identity at ★ ⇒ ★
------------------------------------------------------------------------

X! : instᵐ (idᶜ {Δ = 0}) ⊢ ＇ 0 ∼ ★
X! = id (＇ 0) !

?X-inst-domain : flipᵐ (instᵐ (idᶜ {Δ = 0})) ⊢ ★ ∼ ＇ 0
?X-inst-domain = ？ (id (＇ 0))

instId : (`∀ X⇒X) ∼ (★ ⇒ ★)
instId = (inst (?X-inst-domain ↦ X!)) (λ ())

instExample : Term 0
instExample =
  ((polyId ⟨ instId ⟩) · nat★ 42) ⟨ ℕ? ⟩

instExample-⊢ : ∅ ⊢ instExample ⦂ ℕᵗ
instExample-⊢ =
  ⊢⟨⟩
    (⊢· (⊢⟨⟩ polyId-⊢ instId) (nat★-⊢ 42))
    ℕ?

------------------------------------------------------------------------
-- Generalize the dynamic identity, then instantiate it at ℕ
------------------------------------------------------------------------

?X : genᵐ (idᶜ {Δ = 0}) ⊢ ★ ∼ ＇ 0
?X = ？ (id (＇ 0))

X!-gen-domain : flipᵐ (genᵐ (idᶜ {Δ = 0})) ⊢ ＇ 0 ∼ ★
X!-gen-domain = id (＇ 0) !

genId : (★ ⇒ ★) ∼ (`∀ X⇒X)
genId = (gen (X!-gen-domain ↦ ?X)) (λ ())

genExample : Term 0
genExample =
  ((id★ ⟨ genId ⟩) ⦂∀ X⇒X [ ℕᵗ ]) · nat 42

genExample-⊢ : ∅ ⊢ genExample ⦂ ℕᵗ
genExample-⊢ =
  ⊢· (⊢• (⊢⟨⟩ id★-⊢ genId)) (nat-⊢ 42)

------------------------------------------------------------------------
-- A non-parametric function cast to a polymorphic first projection
------------------------------------------------------------------------

X⇒Y⇒X : Ty 2
X⇒Y⇒X = ＇ 1 ⇒ ＇ 0 ⇒ ＇ 1

polyFirstBody : Ty 1
polyFirstBody = `∀ X⇒Y⇒X

natFirstBody : Ty 1
natFirstBody = ‵ `ℕ ⇒ ＇ 0 ⇒ ‵ `ℕ

instance
  Y∈X⇒Y⇒X-instance : 0 ∈ᵗ X⇒Y⇒X
  Y∈X⇒Y⇒X-instance =
    ∈-fun-right (∉-var (λ ())) (∈-fun-left var-∈)

  X∈polyFirstBody-instance : 0 ∈ᵗ polyFirstBody
  X∈polyFirstBody-instance = ∈-all (∈-fun-left var-∈)

?X₂ : genᵐ (genᵐ (idᶜ {Δ = 0}))
    ⊢ ★ ∼ ＇ 1
?X₂ = ？ (id (＇ 1))

?Y₂ : genᵐ (genᵐ (idᶜ {Δ = 0})) ⊢ ★ ∼ ＇ 0
?Y₂ = ？ (id (＇ 0))

X!₂-domain : flipᵐ (genᵐ (genᵐ (idᶜ {Δ = 0}))) ⊢ ＇ 1 ∼ ★
X!₂-domain = id (＇ 1) !

Y!₂-domain : flipᵐ (genᵐ (genᵐ (idᶜ {Δ = 0}))) ⊢ ＇ 0 ∼ ★
Y!₂-domain = id (＇ 0) !

genFirst : (★ ⇒ ★ ⇒ ★) ∼ `∀ polyFirstBody
genFirst =
  (gen ((gen (X!₂-domain ↦ Y!₂-domain ↦ ?X₂)) (λ ()))) (λ ())

second★ : Term 0
second★ = ƛ (ƛ (` 0))

second★-⊢ : ∅ ⊢ second★ ⦂ (★ ⇒ ★ ⇒ ★)
second★-⊢ = ⊢ƛ (⊢ƛ (⊢` TermCtx.Z))

blameExample : Term 0
blameExample =
  ((((second★ ⟨ genFirst ⟩) ⦂∀ polyFirstBody [ ℕᵗ ])
      ⦂∀ natFirstBody [ 𝔹ᵗ ])
    · nat 42)
    · bool true

blameExample-⊢ : ∅ ⊢ blameExample ⦂ ℕᵗ
blameExample-⊢ =
  ⊢·
    (⊢·
      (⊢• (⊢• (⊢⟨⟩ second★-⊢ genFirst)))
      (nat-⊢ 42))
    (bool-⊢ true)

------------------------------------------------------------------------
-- Executable checks
------------------------------------------------------------------------

gas : ℕ
gas = 100

isNat : ∀ {Δ} → Term Δ → Maybe ℕ
isNat ($ (κℕ n)) = just n
isNat M = nothing

evalNat : ∀ {M A}
  → (fuel : ℕ)
  → ∅ ⊢ M ⦂ A
  → Maybe ℕ
evalNat {M = M} fuel M⊢ with eval fuel M
evalNat {M = M} fuel M⊢ | nothing = nothing
evalNat {M = M} fuel M⊢ | just r = isNat (finalTerm r)

isBlame : ∀ {Δ} → Term Δ → Bool
isBlame blame = true
isBlame M = false

evalBlame : ∀ {M A}
  → (fuel : ℕ)
  → ∅ ⊢ M ⦂ A
  → Maybe Bool
evalBlame {M = M} fuel M⊢ with eval fuel M
evalBlame {M = M} fuel M⊢ | nothing = nothing
evalBlame {M = M} fuel M⊢ | just r = just (isBlame (finalTerm r))

instExample-test : evalNat gas instExample-⊢ ≡ just 42
instExample-test = refl

genExample-test : evalNat gas genExample-⊢ ≡ just 42
genExample-test = refl

blameExample-test : evalBlame gas blameExample-⊢ ≡ just true
blameExample-test = refl

botIntroExample-test : evalBlame gas botIntroExample-⊢ ≡ just true
botIntroExample-test = refl

botFromStarExample-test : evalBlame gas botFromStarExample-⊢ ≡ just true
botFromStarExample-test = refl
