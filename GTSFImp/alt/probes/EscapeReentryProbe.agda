module alt.probes.EscapeReentryProbe where

-- File Charter:
--   * Checks the escape/re-entry example from alt/Design.md against the live
--     GTSFImp calculus.
--   * Records the generated consistency evidence, typing, evaluation traces,
--     and the escaped sealed-and-tagged value.

-- SPEC DEVIATION (not a blocker):
-- The two requested trace types with index `bind (‵ `ℕ) ∷ []` are not
-- derivable using the live `Reduction._—↠[_]_`.  Its `↠-step` constructor
-- records one `StoreChange` per reduction step, while `pure-step` embeds a
-- pure reduction with change `keep`.  The escape needs five pure steps after
-- `β-gen`, so its checked index is `bind (‵ `ℕ) ∷ keepSteps 5`;
-- re-entry needs
-- 32 pure steps, so its checked index is
-- `bind (‵ `ℕ) ∷ keepSteps 32`.  In both traces `β-gen` is the sole
-- `bind`;
-- all remaining steps are `pure-step`.  The behavioral claim itself is
-- confirmed below, including the sibling variable-ground `tag-untag`.

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore; store-empty)
open import Consistency
open import Conversion
open import Primitives
open import CastTerms
open import Reduction
open import Eval
import TermCtx
import proof.DGG.OneStep as Step

------------------------------------------------------------------------
-- Shared closed context and constants
------------------------------------------------------------------------

∅ : Ctx
∅ = ⟨ 0 , store-empty , [] ⟩

ℕᵗ : Ty 0
ℕᵗ = ‵ `ℕ

$9 $7 $5 : Term 0
$9 = $ (κℕ 9)
$7 = $ (κℕ 7)
$5 = $ (κℕ 5)

keepSteps : ∀ {Δ} → ℕ → StoreChanges Δ Δ
keepSteps 0 = []
keepSteps (suc n) = keep ∷ keepSteps n

------------------------------------------------------------------------
-- Part 1: escape a sealed-and-tagged value through a positive ★ channel
------------------------------------------------------------------------

B₁ : Ty 1
B₁ = ＇ 0 ⇒ ★

instance
  0∈B₁-instance : 0 ∈ᵗ B₁
  0∈B₁-instance = ∈-fun-left var-∈

W₁ : Term 0
W₁ = ƛ (` 0)

c₁ : genᵐ (idᶜ {Δ = 0}) ⊢ ⇑ᵗ (★ ⇒ ★) ∼ B₁
c₁ = (id (＇ 0) !) ↦ id ★

c₁-safe : GenSafe c₁
c₁-safe = safe-⇒

escape : Term 0
escape = ((W₁ ⟨ (gen c₁) (λ ()) ⟩) ⦂∀ B₁ [ ℕᵗ ]) · $7

escape-after-bind : Term 1
escape-after-bind =
  (⇑ᵗᵐ W₁ ⟨ c₁ ⟩ ↑ (seal 0 (‵ `ℕ) ↦↑ id↑ ★))
    · $ (κℕ 7)

escape-allocation : escape —→[ bind ℕᵗ ] escape-after-bind
escape-allocation = ξ-·₁ (β-gen (ƛ (` 0)) (λ ()) c₁-safe) refl

escape-endpoint : Term 1
escape-endpoint =
  (($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id {μ = flipᵐ (genᵐ (idᶜ {Δ = 0}))} (＇ 0) ! ⟩)

escape-endpoint-value : Value escape-endpoint
escape-endpoint-value = (($ (κℕ 7)) ↓ seal) 《 inj 》

------------------------------------------------------------------------
-- Part 2: re-enter the sibling region created by the same allocation
------------------------------------------------------------------------

B : Ty 1
B = ＇ 0 ⇒ ((★ ⇒ ★) ⇒ ＇ 0)

instance
  0∈B-instance : 0 ∈ᵗ B
  0∈B-instance = ∈-fun-left var-∈

W : Term 0
W = ƛ (ƛ ((` 0) · (` 1)))

c : genᵐ (idᶜ {Δ = 0})
    ⊢ ⇑ᵗ (★ ⇒ ((★ ⇒ ★) ⇒ ★)) ∼ B
c = (id (＇ 0) !) ↦ ((id ★ ↦ id ★) ↦ ？ (id (＇ 0)))

c-safe : GenSafe c
c-safe = safe-⇒

P : Term 0
P =
  (ƛ (((` 0) · $9) ·
    (ƛ ((ƛ (` 1)) · (((` 1) · $5) · (ƛ (` 1)))))))
  · ((W ⟨ (gen c) (λ ()) ⟩) ⦂∀ B [ ℕᵗ ])

P-after-bind : Term 1
P-after-bind =
  ⇑ᵗᵐ
    (ƛ (((` 0) · $9) ·
      (ƛ ((ƛ (` 1)) · (((` 1) · $5) · (ƛ (` 1)))))))
  · (⇑ᵗᵐ W ⟨ c ⟩ ↑
      (seal 0 (‵ `ℕ) ↦↑
        ((id↑ ★ ↦↓ id↓ ★) ↦↑ unseal 0 (‵ `ℕ))))

P-allocation : P —→[ bind ℕᵗ ] P-after-bind
P-allocation =
  ξ-·₂
    (ƛ (((` 0) · $9) ·
      (ƛ ((ƛ (` 1)) · (((` 1) · $5) · (ƛ (` 1)))))))
    (β-gen (ƛ (ƛ ((` 0) · (` 1)))) (λ ()) c-safe)
    refl

P-⊢ : ∅ ⊢ P ⦂ ℕᵗ
P-⊢ =
  ⊢·
    (⊢ƛ
      (⊢·
        (⊢· (⊢` TermCtx.Z) (⊢$ (κℕ 9)))
        (⊢ƛ
          (⊢·
            (⊢ƛ (⊢` (TermCtx.S TermCtx.Z)))
            (⊢·
              (⊢· (⊢` (TermCtx.S TermCtx.Z)) (⊢$ (κℕ 5)))
              (⊢ƛ (⊢` (TermCtx.S TermCtx.Z))))))))
    (⊢• (⊢⟨⟩
      (⊢ƛ (⊢ƛ (⊢· (⊢` TermCtx.Z)
                      (⊢` (TermCtx.S TermCtx.Z)))))
      ((gen c) (λ ()))))

------------------------------------------------------------------------
-- Executable, proof-producing baseline checks
------------------------------------------------------------------------

private
  returned-result : ∀ {M : Term 0} {gas : ℕ} {r : EvalResult M}
    → eval gas M ≡ just (returned r)
    → EvalResult M
  returned-result {r = r} eq = r

escape-result : EvalResult escape
escape-result = returned-result {gas = 100} refl

escape-final : term escape-result ≡ escape-endpoint
escape-final = refl

escape-reduction : escape —↠[ changes escape-result ] escape-endpoint
escape-reduction rewrite escape-final = trace escape-result

P-result : EvalResult P
P-result = returned-result {gas = 100} refl

P-final : term P-result ≡ $ (κℕ 9)
P-final = refl

P-final-value : Value $9
P-final-value = $ (κℕ 9)

P-reduction : P —↠[ changes P-result ] $ (κℕ 9)
P-reduction rewrite P-final = trace P-result

escape-changes : changes escape-result ≡ bind ℕᵗ ∷ keepSteps 5
escape-changes = refl

escape-live-reduction :
  escape —↠[ bind ℕᵗ ∷ keepSteps 5 ] escape-endpoint
escape-live-reduction rewrite escape-changes = escape-reduction

P-changes : changes P-result ≡ bind ℕᵗ ∷ keepSteps 32
P-changes = refl

P-live-reduction : P —↠[ bind ℕᵗ ∷ keepSteps 32 ] $ (κℕ 9)
P-live-reduction rewrite P-changes = P-reduction

------------------------------------------------------------------------
-- The essential sibling re-entry step
------------------------------------------------------------------------

record Prefix {Δ : TyCtx} (Σ : TyStore Δ) (M : Term Δ) : Set where
  constructor prefix
  field
    prefixCtx : TyCtx
    prefixChanges : StoreChanges Δ prefixCtx
    prefixTerm : Term prefixCtx
    prefixTrace : M —↠[ prefixChanges ] prefixTerm

open Prefix public

runSteps : ∀ {Δ} → ℕ → (Σ : TyStore Δ) → (M : Term Δ)
  → Maybe (Prefix Σ M)
runSteps 0 Σ M = just (prefix _ [] M (M ∎[]))
runSteps (suc n) Σ M with step? Σ M
runSteps (suc n) Σ M | nothing = nothing
runSteps (suc n) Σ M | just (step-result χ N M→N)
    with runSteps n (χ ▷ˢ Σ) N
runSteps (suc n) Σ M | just (step-result χ N M→N) | nothing = nothing
runSteps (suc n) Σ M | just (step-result χ N M→N)
    | just (prefix Δ′ χs P′ N↠P′) =
  just (prefix Δ′ (χ ∷ χs) P′ (↠-step M→N N↠P′))

private
  prefix-result : ∀ {Δ} {n : ℕ} {Σ : TyStore Δ} {M : Term Δ}
      {r : Prefix Σ M}
    → runSteps n Σ M ≡ just r
    → Prefix Σ M
  prefix-result {r = r} eq = r

-- One allocation and the first 25 pure steps lead to the source of the
-- sibling call's matching variable-ground tag/projection cancellation.
reentry-prefix : Prefix store-empty P
reentry-prefix = prefix-result {n = 26} refl

reentry-prefix-changes :
  prefixChanges reentry-prefix ≡ bind ℕᵗ ∷ keepSteps 25
reentry-prefix-changes = refl

reentry-moment : Term (prefixCtx reentry-prefix)
reentry-moment = prefixTerm reentry-prefix

reentry-moment-reached :
  P —↠[ prefixChanges reentry-prefix ] reentry-moment
reentry-moment-reached = prefixTrace reentry-prefix

reentry-context : prefixCtx reentry-prefix ≡ 1
reentry-context = refl

reentry-step :
  Step.OneStep
    (prefixChanges reentry-prefix ▶ˢ store-empty)
    reentry-moment
reentry-step =
  Step.from-just-step
    (step? (prefixChanges reentry-prefix ▶ˢ store-empty) reentry-moment)
    refl

reentry-step-is-pure : Step.change reentry-step ≡ keep
reentry-step-is-pure = refl

data VariableTagUntagStep : ∀ {Δ Δ′} {M : Term Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N
  → Set where

  variable-tag-untag : ∀ {Δ} {V : Term Δ} {μ ν : Env∼ Δ}
      {X : TyVar Δ}
      ⦃ X∼★ : μ ⊢ ＇ X ∼★ ⦄ ⦃ ★∼X : ν ⊢★∼ ＇ X ⦄
    → (vV : Value V)
    → VariableTagUntagStep
        (pure-step
          (tag-untag {μ = μ} {ν = ν} {G = ＇ X}
            ⦃ G∼★ = X∼★ ⦄ ⦃ ★∼G = ★∼X ⦄ vV))

  under-·₂ : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {V M : Term Δ} {V′ M′ : Term Δ′}
      {vV : Value V} {M→M′ : M —→[ χ ] M′}
      {eq : V′ ≡ χ ▷ᵀ V}
    → VariableTagUntagStep M→M′
    → VariableTagUntagStep (ξ-·₂ vV M→M′ eq)

  under-cast : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′} {μ : Env∼ Δ}
      {A B : Ty Δ} {c₀ : μ ⊢ A ∼ B}
      {c₀′ : χ ▷ᵉ μ ⊢ χ ▷ᵗ A ∼ χ ▷ᵗ B}
      {M→M′ : M —→[ χ ] M′} {eq : c₀′ ≡ χ ▷ᶜ c₀}
    → VariableTagUntagStep M→M′
    → VariableTagUntagStep (ξ-⟨⟩ M→M′ eq)

  under-reveal : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′} {A B : Ty Δ}
      {c₀ : Conv↑ Δ A B}
      {c₀′ : Conv↑ Δ′
        (renameᵗ (λ X → χ ▷ᵛ X) A)
        (renameᵗ (λ X → χ ▷ᵛ X) B)}
      {M→M′ : M —→[ χ ] M′}
      {eq : c₀′ ≡ rename↑ (λ X → χ ▷ᵛ X) c₀}
    → VariableTagUntagStep M→M′
    → VariableTagUntagStep (ξ-reveal M→M′ eq)

  under-conceal : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
      {M : Term Δ} {M′ : Term Δ′} {A B : Ty Δ}
      {c₀ : Conv↓ Δ A B}
      {c₀′ : Conv↓ Δ′
        (renameᵗ (λ X → χ ▷ᵛ X) A)
        (renameᵗ (λ X → χ ▷ᵛ X) B)}
      {M→M′ : M —→[ χ ] M′}
      {eq : c₀′ ≡ rename↓ (λ X → χ ▷ᵛ X) c₀}
    → VariableTagUntagStep M→M′
    → VariableTagUntagStep (ξ-conceal M→M′ eq)

reentry-is-variable-tag-untag :
  VariableTagUntagStep (Step.reduction reentry-step)
reentry-is-variable-tag-untag =
  under-reveal
    (under-cast
      (under-cast
        (under-conceal
          (under-·₂
            (under-reveal
              (variable-tag-untag (($ (κℕ 9)) ↓ seal)))))))
