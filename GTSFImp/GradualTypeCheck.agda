module GradualTypeCheck where

-- File Charter:
--   * Maybe-valued type synthesis for the GTSFImp gradual source language.
--   * Returns a synthesized type together with a `GradualTerms` typing
--     derivation, plus an expected-type wrapper for examples and clients.
--   * Uses `Consistency2.lower?` to decide consistency and converts successful
--     searches to the declarative evidence stored in typing derivations.
--   * The checker is positive-only: failure returns `nothing` rather than a
--     proof that no typing derivation exists.

open import Agda.Primitive using (Level)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (inspect; refl; subst; sym; [_])
open import Relation.Nullary using (no; yes)

open import Types
open import TermCtx
open import Consistency using (_∼_)
import Consistency2 as Unique
open import GradualTerms
open import Primitives
  using (Const; constTy; primArgTy; primResultTy)
import proof.Consistency2 as UniqueProof

------------------------------------------------------------------------
-- Result predicates and Maybe witnesses
------------------------------------------------------------------------

HasSomeType : (Δ : TyCtx) → TermCtx Δ → GTerm Δ → Set
HasSomeType Δ Γ M = Σ[ A ∈ Ty Δ ] Δ ∣ Γ ⊢ M ⦂ A

WellTyped : GTerm Nat.zero → Set
WellTyped M = HasSomeType Nat.zero [] M

data IsJust {a : Level} {A : Set a} : Maybe A → Set a where
  is-just : ∀ {x} → IsJust (just x)

fromJust : ∀ {a : Level} {A : Set a} → (m : Maybe A) → IsJust m → A
fromJust (just x) is-just = x
fromJust nothing ()

------------------------------------------------------------------------
-- Decidable fragments used by the checker
------------------------------------------------------------------------

lookup? : ∀ {Δ} (Γ : TermCtx Δ) (x : Var)
  → Maybe (Σ[ A ∈ Ty Δ ] Γ ∋ x ⦂ A)
lookup? [] x = nothing
lookup? (A ∷ Γ) Nat.zero = just (A , Z)
lookup? (A ∷ Γ) (Nat.suc x) with lookup? Γ x
lookup? (A ∷ Γ) (Nat.suc x) | just (B , x∈) = just (B , S x∈)
lookup? (A ∷ Γ) (Nat.suc x) | nothing = nothing

value? : ∀ {Δ} (M : GTerm Δ) → Maybe (Value M)
value? (` x) = nothing
value? (ƛ A ⇒ M) = just (ƛ A ⇒ M)
value? (L ·[ ℓ ] M) = nothing
value? (Λ M) = just (Λ M)
value? (M `[ A ]) = nothing
value? ($ κ) = just ($ κ)
value? (L ⊕[ op at ℓ ] M) = nothing

consistent? : ∀ {Δ} (A B : Ty Δ) → Maybe (A ∼ B)
consistent? A B
    with Unique.lower? A B | inspect (Unique.lower? A) B
consistent? A B | just C | [ eq ] =
  just (UniqueProof.∼ᵘ→∼
    (subst Unique.IsJust (sym eq) Unique.is-just))
consistent? A B | nothing | [ eq ] = nothing

------------------------------------------------------------------------
-- Type checking
------------------------------------------------------------------------

type-check-app-from : ∀ {Δ} {Γ : TermCtx Δ} {L M : GTerm Δ}
  → (ℓ : Label)
  → (A : Ty Δ)
  → Δ ∣ Γ ⊢ L ⦂ A
  → (B : Ty Δ)
  → Δ ∣ Γ ⊢ M ⦂ B
  → Maybe (HasSomeType Δ Γ (L ·[ ℓ ] M))
type-check-app-from ℓ (＇ X) L⊢ B M⊢ = nothing
type-check-app-from ℓ (‵ ι) L⊢ B M⊢ = nothing
type-check-app-from ℓ ★ L⊢ B M⊢ with consistent? B ★
type-check-app-from ℓ ★ L⊢ B M⊢ | just B∼★ =
  just (★ , ⊢·★ L⊢ M⊢ B∼★)
type-check-app-from ℓ ★ L⊢ B M⊢ | nothing = nothing
type-check-app-from ℓ (A ⇒ C) L⊢ B M⊢ with consistent? A B
type-check-app-from ℓ (A ⇒ C) L⊢ B M⊢ | just A∼B =
  just (C , ⊢· L⊢ M⊢ A∼B)
type-check-app-from ℓ (A ⇒ C) L⊢ B M⊢ | nothing = nothing
type-check-app-from ℓ (`∀ A) L⊢ B M⊢ = nothing

type-check : (Δ : TyCtx) → (Γ : TermCtx Δ) → (M : GTerm Δ)
  → Maybe (HasSomeType Δ Γ M)
type-check Δ Γ (` x) with lookup? Γ x
type-check Δ Γ (` x) | just (A , x∈) = just (A , ⊢` x∈)
type-check Δ Γ (` x) | nothing = nothing
type-check Δ Γ (ƛ A ⇒ M) with type-check Δ (A ∷ Γ) M
type-check Δ Γ (ƛ A ⇒ M) | just (B , M⊢) =
  just (A ⇒ B , ⊢ƛ M⊢)
type-check Δ Γ (ƛ A ⇒ M) | nothing = nothing
type-check Δ Γ (L ·[ ℓ ] M)
    with type-check Δ Γ L | type-check Δ Γ M
type-check Δ Γ (L ·[ ℓ ] M)
    | just (A , L⊢) | just (B , M⊢) =
  type-check-app-from ℓ A L⊢ B M⊢
type-check Δ Γ (L ·[ ℓ ] M) | nothing | _ = nothing
type-check Δ Γ (L ·[ ℓ ] M) | just _ | nothing = nothing
type-check Δ Γ (Λ M) with value? M
type-check Δ Γ (Λ M) | nothing = nothing
type-check Δ Γ (Λ M) | just vM
    with type-check (Nat.suc Δ) (⇑ᶜ Γ) M
type-check Δ Γ (Λ M) | just vM | nothing = nothing
type-check Δ Γ (Λ M) | just vM | just (A , M⊢)
    with occurs? Fin.zero A
type-check Δ Γ (Λ M) | just vM | just (A , M⊢)
    | present zero∈A =
  just (`∀ A , ⊢Λ {zero∈A = zero∈A} vM M⊢)
type-check Δ Γ (Λ M) | just vM | just (A , M⊢)
    | absent zero∉A = nothing
type-check Δ Γ (M `[ A ]) with type-check Δ Γ M
type-check Δ Γ (M `[ A ]) | just (＇ X , M⊢) = nothing
type-check Δ Γ (M `[ A ]) | just (‵ ι , M⊢) = nothing
type-check Δ Γ (M `[ A ]) | just (★ , M⊢) = nothing
type-check Δ Γ (M `[ A ]) | just (B ⇒ C , M⊢) = nothing
type-check Δ Γ (M `[ A ]) | just (`∀ B , M⊢) =
  just (B [ A ]ᵗ , ⊢• M⊢)
type-check Δ Γ (M `[ A ]) | nothing = nothing
type-check Δ Γ ($ κ) = just (constTy κ , ⊢$ κ)
type-check Δ Γ (L ⊕[ op at ℓ ] M)
    with type-check Δ Γ L | type-check Δ Γ M
type-check Δ Γ (L ⊕[ op at ℓ ] M)
    | just (A , L⊢) | just (B , M⊢)
    with consistent? A (primArgTy op) | consistent? B (primArgTy op)
type-check Δ Γ (L ⊕[ op at ℓ ] M)
    | just (A , L⊢) | just (B , M⊢) | just A∼arg | just B∼arg =
  just (primResultTy op , ⊢⊕ op L⊢ A∼arg M⊢ B∼arg)
type-check Δ Γ (L ⊕[ op at ℓ ] M)
    | just (A , L⊢) | just (B , M⊢) | nothing | _ = nothing
type-check Δ Γ (L ⊕[ op at ℓ ] M)
    | just (A , L⊢) | just (B , M⊢) | just _ | nothing = nothing
type-check Δ Γ (L ⊕[ op at ℓ ] M) | nothing | _ = nothing
type-check Δ Γ (L ⊕[ op at ℓ ] M) | just _ | nothing = nothing

type-check-expect : (Δ : TyCtx) → (Γ : TermCtx Δ) → (M : GTerm Δ)
  → (A : Ty Δ)
  → Maybe (Δ ∣ Γ ⊢ M ⦂ A)
type-check-expect Δ Γ M A with type-check Δ Γ M
type-check-expect Δ Γ M A | nothing = nothing
type-check-expect Δ Γ M A | just (B , M⊢) with B ≟Ty A
type-check-expect Δ Γ M A | just (B , M⊢) | yes refl = just M⊢
type-check-expect Δ Γ M A | just (B , M⊢) | no B≢A = nothing
