module proof.LR.SwapRename where

-- File Charter:
--   * The renaming facts behind the swap of `gen (inst d)` to
--     `inst (gen d̃)` (notes/denotational-dgg.md, Section 7a): the
--     exchange `swapᵗ` of the two innermost type variables, the renaming
--     `liftSwap ρ` under which `d̃` is read, and the type and mode
--     equations it satisfies.
--   * Also small facts about renaming: identity renaming, `NonVar` and
--     occurrence in a renamed type.

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Nat using () renaming (suc to sucℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import Types
open import Consistency using (Env∼; _‼_; genᵐ; instᵐ; X∼★; ★∼X)
open import proof.ImprecisionConsistency
  using (fin-suc-injective; ext-injective; rename-preimage; found)

------------------------------------------------------------------------
-- The exchange of the two innermost variables
------------------------------------------------------------------------

swapᵗ : ∀ {Δ} → sucℕ (sucℕ Δ) ⇒ʳ sucℕ (sucℕ Δ)
swapᵗ zero = suc zero
swapᵗ (suc zero) = zero
swapᵗ (suc (suc X)) = suc (suc X)

swapᵗ-injective : ∀ {Δ} {X Y : TyVar (sucℕ (sucℕ Δ))}
  → swapᵗ X ≡ swapᵗ Y → X ≡ Y
swapᵗ-injective {X = zero} {Y = zero} eq = refl
swapᵗ-injective {X = zero} {Y = suc zero} ()
swapᵗ-injective {X = zero} {Y = suc (suc Y)} ()
swapᵗ-injective {X = suc zero} {Y = zero} ()
swapᵗ-injective {X = suc zero} {Y = suc zero} eq = refl
swapᵗ-injective {X = suc zero} {Y = suc (suc Y)} ()
swapᵗ-injective {X = suc (suc X)} {Y = zero} ()
swapᵗ-injective {X = suc (suc X)} {Y = suc zero} ()
swapᵗ-injective {X = suc (suc X)} {Y = suc (suc Y)} eq = eq

-- `d` in `gen (inst d)` lives under (inst var, then the variables of
-- the `gen` body); after the swap, `gen`'s variable is innermost.
liftSwap : ∀ {Δ Δ′} → Δ ⇒ʳ sucℕ Δ′ → sucℕ Δ ⇒ʳ sucℕ (sucℕ Δ′)
liftSwap ρ X = swapᵗ (extᵗ ρ X)

liftSwap-injective : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ sucℕ Δ′}
  → (∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y)
  → ∀ {X Y} → liftSwap ρ X ≡ liftSwap ρ Y → X ≡ Y
liftSwap-injective inj eq = ext-injective inj (swapᵗ-injective eq)

swap-ext-suc : ∀ {Δ} (X : TyVar (sucℕ Δ))
  → swapᵗ (extᵗ suc X) ≡ suc X
swap-ext-suc zero = refl
swap-ext-suc (suc X) = refl

liftSwap-suc : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ sucℕ Δ′) (X : TyVar Δ)
  → liftSwap ρ (suc X) ≡ extᵗ suc (ρ X)
liftSwap-suc ρ X with ρ X
liftSwap-suc ρ X | zero = refl
liftSwap-suc ρ X | suc Y = refl

------------------------------------------------------------------------
-- The type and mode equations of the swap
------------------------------------------------------------------------

-- the source of the swapped body is a shift
liftSwap-source : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ sucℕ Δ′)
    {C₁ : Ty (sucℕ Δ)} {C₀ : Ty (sucℕ Δ′)}
  → renameᵗ (extᵗ ρ) C₁ ≡ renameᵗ (extᵗ suc) C₀
  → renameᵗ (liftSwap ρ) C₁ ≡ ⇑ᵗ C₀
liftSwap-source ρ {C₁} {C₀} eq =
  trans (sym (renameᵗ-comp (extᵗ ρ) swapᵗ C₁))
    (trans (cong (renameᵗ swapᵗ) eq)
      (trans (renameᵗ-comp (extᵗ suc) swapᵗ C₀)
        (renameᵗ-cong C₀ swap-ext-suc)))

-- the target of the swapped body
liftSwap-target : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ sucℕ Δ′) (B : Ty Δ)
  → renameᵗ (liftSwap ρ) (⇑ᵗ B) ≡ renameᵗ (extᵗ suc) (renameᵗ ρ B)
liftSwap-target ρ B =
  trans (renameᵗ-comp suc (liftSwap ρ) B)
    (trans (renameᵗ-cong B (liftSwap-suc ρ))
      (sym (renameᵗ-comp ρ (extᵗ suc) B)))

-- the modes: `gen`'s variable is ★∼X and the instantiated one X∼★
liftSwap-env : ∀ {Δ Δ′} {ν : Env∼ Δ} {μ : Env∼ Δ′}
  → (ρ : Δ ⇒ʳ sucℕ Δ′)
  → (∀ X → genᵐ μ ‼ (ρ X) ≡ ν ‼ X)
  → ∀ X → genᵐ (instᵐ μ) ‼ liftSwap ρ X ≡ instᵐ ν ‼ X
liftSwap-env ρ eq zero = refl
liftSwap-env ρ eq (suc X) with ρ X | eq X
liftSwap-env ρ eq (suc X) | zero | e = e
liftSwap-env ρ eq (suc X) | suc Y | e = e

------------------------------------------------------------------------
-- Small facts about renaming
------------------------------------------------------------------------

renameᵗ-id : ∀ {Δ} (A : Ty Δ) → renameᵗ (λ X → X) A ≡ A
renameᵗ-id (＇ X) = refl
renameᵗ-id (‵ ι) = refl
renameᵗ-id ★ = refl
renameᵗ-id (A ⇒ B) rewrite renameᵗ-id A | renameᵗ-id B = refl
renameᵗ-id (`∀ A) =
  cong `∀ (trans (renameᵗ-cong A ext-id) (renameᵗ-id A))
  where
  ext-id : ∀ X → extᵗ (λ Y → Y) X ≡ X
  ext-id zero = refl
  ext-id (suc X) = refl

unrenameNonVar : ∀ {Δ Δ′} {A : Ty Δ} (ρ : Δ ⇒ʳ Δ′)
  → NonVar (renameᵗ ρ A)
  → NonVar A
unrenameNonVar {A = ＇ X} ρ ()
unrenameNonVar {A = ‵ ι} ρ nv = nonvar-base
unrenameNonVar {A = ★} ρ nv = nonvar-star
unrenameNonVar {A = A ⇒ B} ρ nv = nonvar-fun
unrenameNonVar {A = `∀ A} ρ nv = nonvar-all

-- the innermost variable occurs in A if it occurs in A shifted
-- under one binder
unshift-zero : ∀ {Δ} {A : Ty (sucℕ Δ)}
  → zero ∈ᵗ renameᵗ (extᵗ suc) A
  → zero ∈ᵗ A
unshift-zero z∈ with rename-preimage z∈
unshift-zero z∈ | found zero refl X∈A = X∈A
unshift-zero z∈ | found (suc X) () X∈A

∈→≢★ : ∀ {Δ} {X : TyVar Δ} {A : Ty Δ} → X ∈ᵗ A → A ≢ ★
∈→≢★ {A = ＇ Y} X∈ ()
∈→≢★ {A = ‵ ι} X∈ ()
∈→≢★ {A = ★} () refl
∈→≢★ {A = A ⇒ B} X∈ ()
∈→≢★ {A = `∀ A} X∈ ()
