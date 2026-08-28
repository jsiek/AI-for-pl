module alt.probes.LooseIdCancelRecheck where

-- File Charter:
--   * Rechecks the ladder-1 loose `id-cancel` counterexample against the
--     current sigma-indexed telescope and anchor-directed `rep?`.
--   * A mismatched identity pair over a constant is typeable and its
--     cancellation preserves the base type.  Base typing alone is not a
--     sufficient guard: an adapter-region operand gives a second checked
--     counterexample.  At a variable atom, a third live crossing gives the
--     historical counterexample shape directly.
--   * Consequently the adapter value is still necessary.  This module adds
--     only a hypothetical probe relation; it does not change reduction,
--     typing, or the value predicates.
--
-- Commit c5ee0351 recorded the original shape
--
--   (($ 7 ↓[ 0 ≔ 0 ] seal) ↓[ 0 ≔ 0 ] id↓)
--     ↑[ 2 ≔ 1 ] id↑  —→  ($ 7 ↓[ 0 ≔ 0 ] seal).
--
-- The current fixture gives the three live roles explicit names in its
-- construction: beta is the inner crossing, gamma is the foreign crossing,
-- and alpha is the outer crossing.  Their indices are 0, 1, and 2.

open import Data.Fin using (zero; suc)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

------------------------------------------------------------------------
-- A local model of the rejected loose rule
------------------------------------------------------------------------

infix 4 _⊢_—loose→_

data _⊢_—loose→_ {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) :
    Term Θ Δ → Term Θ Δ → Set where
  loose-id-cancel : ∀ {R : Term Θ Δ}
      {X Y : TyVar (suc Δ)} {α β : TyVar Θ}
    → Result R
      ------------------------------------------------------------
    → Ψ ⊢ (R ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑ —loose→ R

------------------------------------------------------------------------
-- Three anchors and two live crossings outside the candidate redex
------------------------------------------------------------------------

beta gamma alpha : TyVar 3
beta = zero
gamma = suc zero
alpha = suc (suc zero)

empty-fresh : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
empty-fresh ()

second-fresh : gamma ∉ᵛ (just beta Vec.∷ Vec.[])
second-fresh zero ()

third-fresh : alpha ∉ᵛ
  (just beta Vec.∷ just gamma Vec.∷ Vec.[])
third-fresh zero ()
third-fresh (suc zero) ()

baseΣ : Vec.Vec (Maybe (TyVar 3)) 2
baseΣ = just beta Vec.∷ just gamma Vec.∷ Vec.[]

outerΣ : Vec.Vec (Maybe (TyVar 3)) 3
outerΣ = just beta Vec.∷ just gamma Vec.∷ just alpha Vec.∷ Vec.[]

insideΣ : Vec.Vec (Maybe (TyVar 3)) 2
insideΣ = just gamma Vec.∷ just alpha Vec.∷ Vec.[]

rootEnv : TyEnv 3 zero Vec.[]
rootEnv = ∅ ,:= ℕᵗ ,:= ℕᵗ ,:= ℕᵗ

baseEnv : TyEnv 3 2 baseΣ
baseEnv =
  (rootEnv ,begin[ zero ≔ beta ]⟨ empty-fresh ⟩)
    ,begin[ suc zero ≔ gamma ]⟨ second-fresh ⟩

outerEnv : TyEnv 3 3 outerΣ
outerEnv =
  baseEnv ,begin[ suc (suc zero) ≔ alpha ]⟨ third-fresh ⟩

insideEnv : TyEnv 3 2 insideΣ
insideEnv = outerEnv ,end[ zero ]

beta-slot gamma-slot : TyVar 2
beta-slot = zero
gamma-slot = suc zero

------------------------------------------------------------------------
-- Harmless flavor: the shared atom is a base type
------------------------------------------------------------------------

baseOperand : Term 3 2
baseOperand = $ (κℕ zero)

baseInner : Term 3 3
baseInner = baseOperand ↓[ zero ≔ beta ] id↓

baseRedex : Term 3 2
baseRedex =
  baseInner ↑[ suc (suc zero) ≔ alpha ] id↑

baseOperand-typed-inside : insideEnv ∣ [] ⊢ baseOperand ⦂ ℕᵗ
baseOperand-typed-inside = ⊢$ (κℕ zero)

baseInner-typed : outerEnv ∣ [] ⊢ baseInner ⦂ ℕᵗ
baseInner-typed =
  ⊢conceal refl refl (⊢id↓ (‵ `ℕ)) baseOperand-typed-inside

baseRedex-typed : baseEnv ∣ [] ⊢ baseRedex ⦂ ℕᵗ
baseRedex-typed = ⊢reveal refl (⊢id↑ (‵ `ℕ)) baseInner-typed

baseOperand-typed-outside : baseEnv ∣ [] ⊢ baseOperand ⦂ ℕᵗ
baseOperand-typed-outside = ⊢$ (κℕ zero)

base-loose-step : baseEnv ⊢ baseRedex —loose→ baseOperand
base-loose-step = loose-id-cancel (result-val ($ (κℕ zero)))

baseMiddle : Term 3 2
baseMiddle = ($ (κℕ zero)) ↑[ suc (suc zero) ≔ alpha ] id↑

-- The existing rules also dissolve this harmless pair in two ordinary steps.
base-current-first-step : baseEnv ⊢ baseRedex —→ baseMiddle
base-current-first-step = ξ-reveal {fresh = third-fresh} id-conceal

base-current-second-step : baseEnv ⊢ baseMiddle —→ baseOperand
base-current-second-step = id-reveal

base-loose-preservation :
  (baseEnv ∣ [] ⊢ baseRedex ⦂ ℕᵗ)
  × (baseEnv ⊢ baseRedex —loose→ baseOperand
    × (baseEnv ∣ [] ⊢ baseOperand ⦂ ℕᵗ))
base-loose-preservation =
  baseRedex-typed , base-loose-step , baseOperand-typed-outside

------------------------------------------------------------------------
-- Base-typed is not by itself a sufficient guard
------------------------------------------------------------------------

beta-reentered-fresh : beta ∉ᵛ insideΣ
beta-reentered-fresh zero ()
beta-reentered-fresh (suc zero) ()

baseSensitiveRegion : Term 3 3
baseSensitiveRegion = ν[ ＇ zero ] $ (κℕ zero)

baseSensitiveOperand : Term 3 2
baseSensitiveOperand =
  baseSensitiveRegion ↑[ zero ≔ beta ] id↑

baseSensitiveOperand-typed-inside :
  insideEnv ∣ [] ⊢ baseSensitiveOperand ⦂ ℕᵗ
baseSensitiveOperand-typed-inside =
  ⊢reveal {fresh = beta-reentered-fresh} refl (⊢id↑ (‵ `ℕ))
    (⊢ν (⊢$ (κℕ zero)))

baseSensitiveRegion-result : Result baseSensitiveRegion
baseSensitiveRegion-result = result-ν (result-val ($ (κℕ zero)))

baseSensitiveOperand-value : Value baseSensitiveOperand
baseSensitiveOperand-value =
  baseSensitiveRegion-result ↑[ zero ≔ beta ]
    adapter-region (result-val ($ (κℕ zero))) var-∈

baseSensitiveOperand-result : Result baseSensitiveOperand
baseSensitiveOperand-result = result-val baseSensitiveOperand-value

baseSensitiveInner : Term 3 3
baseSensitiveInner = baseSensitiveOperand ↓[ zero ≔ beta ] id↓

baseSensitiveRedex : Term 3 2
baseSensitiveRedex =
  baseSensitiveInner ↑[ suc (suc zero) ≔ alpha ] id↑

baseSensitiveInner-typed :
  outerEnv ∣ [] ⊢ baseSensitiveInner ⦂ ℕᵗ
baseSensitiveInner-typed =
  ⊢conceal refl refl (⊢id↓ (‵ `ℕ))
    baseSensitiveOperand-typed-inside

baseSensitiveRedex-typed :
  baseEnv ∣ [] ⊢ baseSensitiveRedex ⦂ ℕᵗ
baseSensitiveRedex-typed =
  ⊢reveal refl (⊢id↑ (‵ `ℕ)) baseSensitiveInner-typed

baseSensitive-loose-step :
  baseEnv ⊢ baseSensitiveRedex —loose→ baseSensitiveOperand
baseSensitive-loose-step = loose-id-cancel baseSensitiveOperand-result

-- The operand's reveal tries to re-enter beta, but beta is already live in
-- baseEnv.  Thus a guard that mentions only the base endpoint is unsound.
baseSensitiveOperand-not-typed-outside :
  ¬ (baseEnv ∣ [] ⊢ baseSensitiveOperand ⦂ ℕᵗ)
baseSensitiveOperand-not-typed-outside
    (⊢reveal {fresh = beta-fresh} rep-eq conversion⊢ region⊢) =
  beta-fresh zero refl

base-typed-guard-counterexample :
  (baseEnv ∣ [] ⊢ baseSensitiveRedex ⦂ ℕᵗ)
  × (baseEnv ⊢ baseSensitiveRedex —loose→ baseSensitiveOperand
    × ¬ (baseEnv ∣ [] ⊢ baseSensitiveOperand ⦂ ℕᵗ))
base-typed-guard-counterexample =
  baseSensitiveRedex-typed , baseSensitive-loose-step ,
    baseSensitiveOperand-not-typed-outside

------------------------------------------------------------------------
-- Refuting flavor: the shared atom is the third crossing gamma
------------------------------------------------------------------------

foreignSeed : Term 3 1
foreignSeed = $ (κℕ zero)

foreignOperand : Term 3 2
foreignOperand = foreignSeed ↓[ zero ≔ gamma ] seal

foreignOperand-typed-inside :
  insideEnv ∣ [] ⊢ foreignOperand ⦂ ＇ zero
foreignOperand-typed-inside =
  ⊢conceal refl refl ⊢seal (⊢$ (κℕ zero))

variableInner : Term 3 3
variableInner = foreignOperand ↓[ zero ≔ beta ] id↓

variableRedex : Term 3 2
variableRedex =
  variableInner ↑[ suc (suc zero) ≔ alpha ] id↑

-- Both identity conversions really do see `＇ 1`: ending beta inserts at
-- zero, while ending alpha inserts at two and leaves gamma at one.
foreign-weakening-equation :
  wkᵗ alpha (＇ gamma-slot) ≡ wkᵗ beta (＇ beta-slot)
foreign-weakening-equation = refl

variableInner-typed : outerEnv ∣ [] ⊢ variableInner ⦂ ＇ suc zero
variableInner-typed =
  ⊢conceal refl refl (⊢id↓ (＇ suc zero))
    foreignOperand-typed-inside

variableRedex-typed : baseEnv ∣ [] ⊢ variableRedex ⦂ ＇ suc zero
variableRedex-typed =
  ⊢reveal refl (⊢id↑ (＇ suc zero)) variableInner-typed

foreignOperand-value : Value foreignOperand
foreignOperand-value =
  ($ (κℕ zero)) ↓[ zero ≔ gamma ] sealᵥ

foreignOperand-canonical : CanonicalInterior foreignOperand
foreignOperand-canonical = sealed ($ (κℕ zero)) zero gamma

foreignOperand-result : Result foreignOperand
foreignOperand-result = result-val foreignOperand-value

variableInner-value : Value variableInner
variableInner-value =
  foreignOperand-value ↓[ zero ≔ beta ]
    delimiter foreignOperand-canonical

variableInner-result : Result variableInner
variableInner-result = result-val variableInner-value

variable-node-pair-mismatch : ¬ (alpha ≡ beta × alpha ≡ beta)
variable-node-pair-mismatch (() , anchor-eq)

-- The current calculus classifies the mismatched pair as an adapter value.
variableRedex-value : Value variableRedex
variableRedex-value =
  variableInner-result ↑[ suc (suc zero) ≔ alpha ]
    adapter foreignOperand-result variable-node-pair-mismatch

variableRedex-no-current-step : ∀ {M′}
  → ¬ (baseEnv ⊢ variableRedex —→ M′)
variableRedex-no-current-step = value-no-step variableRedex-value

variable-loose-step : baseEnv ⊢ variableRedex —loose→ foreignOperand
variable-loose-step = loose-id-cancel foreignOperand-result

-- After cancellation the sealing node says that slot zero belongs to gamma,
-- but baseEnv says that slot zero belongs to beta.  This is the exact current
-- sigma equation that prevents the reduct from receiving the redex type.
reduct-anchor-equation-impossible :
  Vec.lookup baseΣ zero ≢ just gamma
reduct-anchor-equation-impossible ()

foreignOperand-not-typed-at-redex-type :
  ¬ (baseEnv ∣ [] ⊢ foreignOperand ⦂ ＇ suc zero)
foreignOperand-not-typed-at-redex-type
    (⊢conceal anchor-eq rep-eq conversion⊢ seed⊢) =
  reduct-anchor-equation-impossible anchor-eq

-- Diagram:
--   baseEnv ∣ [] ⊢ variableRedex ⦂ ＇ 1
--                    │ loose-id-cancel
--                    ▼
--               foreignOperand
--   baseEnv ∣ [] ⊬ foreignOperand ⦂ ＇ 1
variable-preservation-counterexample :
  (baseEnv ∣ [] ⊢ variableRedex ⦂ ＇ suc zero)
  × (baseEnv ⊢ variableRedex —loose→ foreignOperand
    × ¬ (baseEnv ∣ [] ⊢ foreignOperand ⦂ ＇ suc zero))
variable-preservation-counterexample =
  variableRedex-typed , variable-loose-step ,
    foreignOperand-not-typed-at-redex-type

-- Verdict: loose cancellation is still refutable.  The requested paper-level
-- guard "matched node pair OR identity at `‵ ι`" is sound only if its base
-- branch means a syntactic ambient-parametric base result (`ν* $ κ`), not
-- merely that typing assigned the identity endpoint `‵ ι`.  The latter is
-- refuted above by adapter-region.  The matched branch is current
-- `id-cancel`.  For the corrected base branch, induction on the nu prefix
-- rebuilds `⊢ν` and ends at ambient-parametric `⊢$`; also
-- `wkᵗ X (‵ ι) ≡ ‵ ι` for every X.  That discharges its preservation
-- obligation on paper.  No guarded rule is implemented here.
