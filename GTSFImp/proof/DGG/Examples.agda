module proof.DGG.Examples where

-- File Charter:
--   * Ports Cambridge26 Example 12 to the GTSFImp cast calculus.
--   * Records the two executable programs from that example without proving
--     their imprecision relation yet.
--   * Uses Eval to compute reduction traces that finish in returned values.

open import Data.Bool using (Bool; false; true)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore; store-empty)
open import TermCtx using (Z)
open import Consistency
open import Conversion
open import Primitives
open import CastTerms
open import Reduction
open import Eval

------------------------------------------------------------------------
-- Shared closed instance of the schematic Cambridge26 terms
------------------------------------------------------------------------

∅ : Ctx
∅ = ⟨ 0 , store-empty , [] ⟩

ℕᵗ : Ty 0
ℕᵗ = ‵ `ℕ

X⇒X : Ty 1
X⇒X = ＇ 0 ⇒ ＇ 0

instance
  X∈X⇒X-instance : ∀ {Δ} → 0 ∈ᵗ (＇_ {suc Δ} 0 ⇒ ＇ 0)
  X∈X⇒X-instance = ∈-fun-left var-∈

polyId : Term 0
polyId = Λ (ƛ (` 0))

polyId-⊢ : ∅ ⊢ polyId ⦂ `∀ X⇒X
polyId-⊢ = ⊢Λ (ƛ (` 0)) (⊢ƛ (⊢` Z))

c : Term 0
c = $ (κℕ 7)

c-⊢ : ∅ ⊢ c ⦂ ℕᵗ
c-⊢ = ⊢$ (κℕ 7)

X! : instᵐ (idᶜ {Δ = 0}) ⊢ ＇ 0 ∼ ★
X! = id (＇ 0) !

X? : genᵐ (idᶜ {Δ = 0}) ⊢ ★ ∼ ＇ 0
X? = ？ (id (＇ 0))

ν̅α-α♯→α♭ : (`∀ X⇒X) ∼ (★ ⇒ ★)
ν̅α-α♯→α♭ = (inst (X! ↦ X!)) (λ ())

να-α!→α? : (★ ⇒ ★) ∼ (`∀ X⇒X)
να-α!→α? = (gen (X? ↦ X?)) (λ ())

------------------------------------------------------------------------
-- Cambridge26 Example 12: up and then down
------------------------------------------------------------------------

example12-left : Term 0
example12-left =
  (((polyId ⟨ ν̅α-α♯→α♭ ⟩) ⟨ να-α!→α? ⟩) ⦂∀ X⇒X [ ℕᵗ ]) · c

example12-left-⊢ : ∅ ⊢ example12-left ⦂ ℕᵗ
example12-left-⊢ =
  ⊢·
    (⊢• (⊢⟨⟩ (⊢⟨⟩ polyId-⊢ ν̅α-α♯→α♭) να-α!→α?))
    c-⊢

example12-right : Term 0
example12-right = (polyId ⦂∀ X⇒X [ ℕᵗ ]) · c

example12-right-⊢ : ∅ ⊢ example12-right ⦂ ℕᵗ
example12-right-⊢ = ⊢· (⊢• polyId-⊢) c-⊢

------------------------------------------------------------------------
-- Checked one-step traces from Eval
------------------------------------------------------------------------

record OneStep {Δ : TyCtx} (Σ : TyStore Δ) (M : Term Δ) : Set where
  constructor one-step
  field
    Δ′ : TyCtx
    change : StoreChange Δ Δ′
    next : Term Δ′
    reduction : M —→[ change ] next

open OneStep

hasStep? : ∀ {Δ} {M : Term Δ} → Maybe (Step M) → Bool
hasStep? (just _) = true
hasStep? nothing = false

from-just-step : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ}
  → (s : Maybe (Step M))
  → hasStep? s ≡ true
  → OneStep Σ M
from-just-step (just (step-result χ N M→N)) refl =
  one-step _ χ N M→N
from-just-step nothing ()

store-after : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ}
  → (s : OneStep Σ M)
  → TyStore (Δ′ s)
store-after {Σ = Σ} s = change s ▷ˢ Σ

hasValue? : ∀ {Δ} {M : Term Δ} → Maybe (Value M) → Bool
hasValue? (just _) = true
hasValue? nothing = false

from-just-value : ∀ {Δ} {M : Term Δ}
  → (v : Maybe (Value M))
  → hasValue? v ≡ true
  → Value M
from-just-value (just v) refl = v
from-just-value nothing ()

------------------------------------------------------------------------
-- Left program: up through ν̅, down through ν, instantiate, and apply
------------------------------------------------------------------------

left₀ : Term 0
left₀ =
  ((((Λ (ƛ (` 0)))
    ⟨ (inst_ {μ = idᶜ {Δ = 0}} ⦃ z∈A = ∈-fun-left var-∈ ⦄
        ((id {μ = instᵐ (idᶜ {Δ = 0})} (＇ 0) !) ↦
         (id {μ = instᵐ (idᶜ {Δ = 0})} (＇ 0) !))
        (λ ())) ⟩)
    ⟨ (gen_ {μ = idᶜ {Δ = 0}} ⦃ z∈B = ∈-fun-left var-∈ ⦄
        ((？ (id (＇ 0))) ↦ (？ (id (＇ 0)))) (λ ())) ⟩)
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)

left-store₀ : TyStore 0
left-store₀ = store-empty

-- 1. β-inst for the ν̅α.α♯→α♭ cast.
left-step₀ : OneStep left-store₀ left₀
left-step₀ = from-just-step (step? left-store₀ left₀) refl

left₁ : Term (Δ′ left-step₀)
left₁ =
  ((((Λ (ƛ (` 0))) ⦂∀ (＇ 0 ⇒ ＇ 0) [ ＇ 0 ])
      ↑ (seal 0 ★ ↦↑ unseal 0 ★)
      ⟨ id {μ = renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})} ★ ↦ id ★ ⟩
      ⟨ (gen_ {μ = extᵐ (idᶜ {Δ = 0})}
          ⦃ z∈B = ∈-fun-left var-∈ ⦄
          ((？ (id (＇ 0))) ↦ (？ (id (＇ 0)))) (λ ())) ⟩)
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)

left-store₁ : TyStore (Δ′ left-step₀)
left-store₁ = store-after left-step₀

-- 2. β-Λ under the first reveal/cast wrappers.
left-step₁ : OneStep left-store₁ left₁
left-step₁ = from-just-step (step? left-store₁ left₁) refl

left₂ : Term (Δ′ left-step₁)
left₂ =
  (((((ƛ (` 0))
    ↑ (seal 0 (＇ 1) ↦↑ unseal 0 (＇ 1)))
    ↑ (seal 1 ★ ↦↑ unseal 1 ★))
    ⟨ id {μ = applyEnv (bind (＇ 0))
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★ ↦ id ★ ⟩)
    ⟨ (gen_ {μ = extᵐ (extᵐ (idᶜ {Δ = 0}))}
        ⦃ z∈B = ∈-fun-left var-∈ ⦄
        ((？ (id (＇ 0))) ↦ (？ (id (＇ 0)))) (λ ())) ⟩
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)

left-store₂ : TyStore (Δ′ left-step₁)
left-store₂ = store-after left-step₁

-- 3. β-gen for the να.α!→α? cast at the ℕ instantiation.
left-step₂ : OneStep left-store₂ left₂
left-step₂ = from-just-step (step? left-store₂ left₂) refl

left₃ : Term (Δ′ left-step₂)
left₃ =
  ((((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    ⟨ id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦ id ★ ⟩)
    ⟨ (？_ {μ = genᵐ
          (applyEnv (bind (＇ 0))
            (applyEnv (bind ★) (idᶜ {Δ = 0})))}
        (id (＇ 0)))
      ↦ (？_ {μ = genᵐ
          (applyEnv (bind (＇ 0))
            (applyEnv (bind ★) (idᶜ {Δ = 0})))}
        (id (＇ 0))) ⟩)
    ↑ (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ)))
    · $ (κℕ 7)

left-store₃ : TyStore (Δ′ left-step₂)
left-store₃ = store-after left-step₂

-- 4. β-reveal-⇒ distributes the outer function reveal.
left-step₃ : OneStep left-store₃ left₃
left-step₃ = from-just-step (step? left-store₃ left₃) refl

left₄ : Term (Δ′ left-step₃)
left₄ =
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    ⟨ id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦ id ★ ⟩)
    ⟨ (？_ {μ = genᵐ
          (applyEnv (bind (＇ 0))
            (applyEnv (bind ★) (idᶜ {Δ = 0})))}
        (id (＇ 0)))
      ↦ (？_ {μ = genᵐ
          (applyEnv (bind (＇ 0))
            (applyEnv (bind ★) (idᶜ {Δ = 0})))}
        (id (＇ 0))) ⟩)
    · ($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)

left-store₄ : TyStore (Δ′ left-step₃)
left-store₄ = store-after left-step₃

-- 5. β-⇒ pushes the first function cast to the argument/result.
left-step₄ : OneStep left-store₄ left₄
left-step₄ = from-just-step (step? left-store₄ left₄) refl

left₅ : Term (Δ′ left-step₄)
left₅ =
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    ⟨ id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ↦ id ★ ⟩)
    · (($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id {μ = flipᵐ (genᵐ
          (applyEnv (bind (＇ 0))
            (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
        (＇ 0) ! ⟩))
    ⟨ ？_ {μ = genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
      (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)

left-store₅ : TyStore (Δ′ left-step₄)
left-store₅ = store-after left-step₄

-- 6. β-⇒ pushes the second function cast to the argument/result.
left-step₅ : OneStep left-store₅ left₅
left-step₅ = from-just-step (step? left-store₅ left₅) refl

left₆ : Term (Δ′ left-step₅)
left₆ =
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    · ((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id {μ = flipᵐ (genᵐ
          (applyEnv (bind (＇ 0))
            (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
        (＇ 0) ! ⟩)
      ⟨ id {μ = flipᵐ (renameEnv∼ wk↪ᵗ
          (applyEnv (bind (＇ 0))
            (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))))} ★ ⟩))
    ⟨ id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ⟩)
    ⟨ ？_ {μ = genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
      (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)

left-store₆ : TyStore (Δ′ left-step₅)
left-store₆ = store-after left-step₅

-- 7. β-id removes an administrative identity cast from the argument.
left-step₆ : OneStep left-store₆ left₆
left-step₆ = from-just-step (step? left-store₆ left₆) refl

left₇ : Term (Δ′ left-step₆)
left₇ =
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    · (($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id {μ = flipᵐ (genᵐ
          (applyEnv (bind (＇ 0))
            (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
        (＇ 0) ! ⟩))
    ⟨ id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ⟩)
    ⟨ ？_ {μ = genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
      (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)

left-store₇ : TyStore (Δ′ left-step₆)
left-store₇ = store-after left-step₆

-- 8. β-reveal-⇒ distributes the next function reveal.
left-step₇ : OneStep left-store₇ left₇
left-step₇ = from-just-step (step? left-store₇ left₇) refl

left₈ : Term (Δ′ left-step₇)
left₈ =
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    · ((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id {μ = flipᵐ (genᵐ
          (applyEnv (bind (＇ 0))
            (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
        (＇ 0) ! ⟩)
      ↓ seal 2 ★))
    ↑ unseal 2 ★)
    ⟨ id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ⟩)
    ⟨ ？_ {μ = genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
      (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)

left-store₈ : TyStore (Δ′ left-step₇)
left-store₈ = store-after left-step₇

-- 9. β-reveal-⇒ distributes the innermost function reveal.
left-step₈ : OneStep left-store₈ left₈
left-step₈ = from-just-step (step? left-store₈ left₈) refl

left₉ : Term (Δ′ left-step₈)
left₉ =
  (((((ƛ (` 0))
    · (((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id {μ = flipᵐ (genᵐ
          (applyEnv (bind (＇ 0))
            (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
        (＇ 0) ! ⟩)
      ↓ seal 2 ★)
      ↓ seal 1 (＇ 2)))
    ↑ unseal 1 (＇ 2))
    ↑ unseal 2 ★)
    ⟨ id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ⟩)
    ⟨ ？_ {μ = genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
      (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)

left-store₉ : TyStore (Δ′ left-step₈)
left-store₉ = store-after left-step₈

-- 10. β substitutes the fully wrapped argument into the identity body.
left-step₉ : OneStep left-store₉ left₉
left-step₉ = from-just-step (step? left-store₉ left₉) refl

left₁₀ : Term (Δ′ left-step₉)
left₁₀ =
  ((((((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id {μ = flipᵐ (genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
      (＇ 0) ! ⟩)
    ↓ seal 2 ★)
    ↓ seal 1 (＇ 2))
    ↑ unseal 1 (＇ 2))
    ↑ unseal 2 ★)
    ⟨ id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ⟩)
    ⟨ ？_ {μ = genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
      (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)

left-store₁₀ : TyStore (Δ′ left-step₉)
left-store₁₀ = store-after left-step₉

-- 11. conceal-reveal cancels one abstract-boundary round trip.
left-step₁₀ : OneStep left-store₁₀ left₁₀
left-step₁₀ = from-just-step (step? left-store₁₀ left₁₀) refl

left₁₁ : Term (Δ′ left-step₁₀)
left₁₁ =
  ((((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id {μ = flipᵐ (genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
      (＇ 0) ! ⟩)
    ↓ seal 2 ★)
    ↑ unseal 2 ★)
    ⟨ id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ⟩)
    ⟨ ？_ {μ = genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
      (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)

left-store₁₁ : TyStore (Δ′ left-step₁₀)
left-store₁₁ = store-after left-step₁₀

-- 12. conceal-reveal cancels the next abstract-boundary round trip.
left-step₁₁ : OneStep left-store₁₁ left₁₁
left-step₁₁ = from-just-step (step? left-store₁₁ left₁₁) refl

left₁₂ : Term (Δ′ left-step₁₁)
left₁₂ =
  (((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id {μ = flipᵐ (genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
      (＇ 0) ! ⟩)
    ⟨ id {μ = renameEnv∼ wk↪ᵗ
        (applyEnv (bind (＇ 0))
          (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★ ⟩)
    ⟨ ？_ {μ = genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
      (id (＇ 0)) ⟩)
  ↑ unseal 0 (‵ `ℕ)

left-store₁₂ : TyStore (Δ′ left-step₁₁)
left-store₁₂ = store-after left-step₁₁

-- 13. β-id removes the remaining administrative identity cast.
left-step₁₂ : OneStep left-store₁₂ left₁₂
left-step₁₂ = from-just-step (step? left-store₁₂ left₁₂) refl

left₁₃ : Term (Δ′ left-step₁₂)
left₁₃ =
  ((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id {μ = flipᵐ (genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
      (＇ 0) ! ⟩)
    ⟨ ？_ {μ = genᵐ
        (applyEnv (bind (＇ 0))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
      (id (＇ 0)) ⟩)
  ↑ unseal 0 (‵ `ℕ)

left-store₁₃ : TyStore (Δ′ left-step₁₂)
left-store₁₃ = store-after left-step₁₂

-- 14. tag-untag cancels the matching variable-ground tag pair.
left-step₁₃ : OneStep left-store₁₃ left₁₃
left-step₁₃ = from-just-step (step? left-store₁₃ left₁₃) refl

left₁₄ : Term (Δ′ left-step₁₃)
left₁₄ =
  ($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)

left-store₁₄ : TyStore (Δ′ left-step₁₃)
left-store₁₄ = store-after left-step₁₃

-- 15. conceal-reveal exposes the original natural-number value.
left-step₁₄ : OneStep left-store₁₄ left₁₄
left-step₁₄ = from-just-step (step? left-store₁₄ left₁₄) refl

left-final : Term (Δ′ left-step₁₄)
left-final = $ (κℕ 7)

left-final-is-7 : left-final ≡ $ (κℕ 7)
left-final-is-7 = refl

left-final-value : Value left-final
left-final-value = from-just-value (value? left-final) refl

left-changes : StoreChanges 0 (Δ′ left-step₁₄)
left-changes =
  bind ★ ∷ bind (＇ 0) ∷ bind (‵ `ℕ) ∷
  keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
  keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ []

example12-left-reduction : example12-left —↠[ left-changes ] left-final
example12-left-reduction =
  ((((Λ (ƛ (` 0)))
    ⟨ ((inst ((id (＇ 0) !) ↦ (id (＇ 0) !))) (λ ())) ⟩)
    ⟨ ((gen ((？ (id (＇ 0))) ↦ (？ (id (＇ 0))))) (λ ())) ⟩)
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)
  —→[ bind ★ ]⟨ reduction left-step₀ ⟩
  ((((Λ (ƛ (` 0))) ⦂∀ (＇ 0 ⇒ ＇ 0) [ ＇ 0 ])
      ↑ (seal 0 ★ ↦↑ unseal 0 ★)
      ⟨ id ★ ↦ id ★ ⟩
      ⟨ ((gen ((？ (id (＇ 0))) ↦ (？ (id (＇ 0))))) (λ ())) ⟩)
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)
  —→[ bind (＇ 0) ]⟨ reduction left-step₁ ⟩
  (((((ƛ (` 0))
    ↑ (seal 0 (＇ 1) ↦↑ unseal 0 (＇ 1)))
    ↑ (seal 1 ★ ↦↑ unseal 1 ★))
    ⟨ id ★ ↦ id ★ ⟩)
    ⟨ ((gen ((？ (id (＇ 0))) ↦ (？ (id (＇ 0))))) (λ ())) ⟩
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)
  —→[ bind (‵ `ℕ) ]⟨ reduction left-step₂ ⟩
  ((((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    ⟨ id ★ ↦ id ★ ⟩)
    ⟨ (？ (id (＇ 0))) ↦ (？ (id (＇ 0))) ⟩)
    ↑ (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ)))
    · $ (κℕ 7)
  —→[ keep ]⟨ reduction left-step₃ ⟩
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    ⟨ id ★ ↦ id ★ ⟩)
    ⟨ (？ (id (＇ 0))) ↦ (？ (id (＇ 0))) ⟩)
    · ($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₄ ⟩
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    ⟨ id ★ ↦ id ★ ⟩)
    · (($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id (＇ 0) ! ⟩))
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₅ ⟩
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    · ((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id (＇ 0) ! ⟩)
      ⟨ id ★ ⟩))
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₆ ⟩
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    · (($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id (＇ 0) ! ⟩))
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₇ ⟩
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    · ((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id (＇ 0) ! ⟩)
      ↓ seal 2 ★))
    ↑ unseal 2 ★)
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₈ ⟩
  (((((ƛ (` 0))
    · (((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id (＇ 0) ! ⟩)
      ↓ seal 2 ★)
      ↓ seal 1 (＇ 2)))
    ↑ unseal 1 (＇ 2))
    ↑ unseal 2 ★)
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₉ ⟩
  ((((((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id (＇ 0) ! ⟩)
    ↓ seal 2 ★)
    ↓ seal 1 (＇ 2))
    ↑ unseal 1 (＇ 2))
    ↑ unseal 2 ★)
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₁₀ ⟩
  ((((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id (＇ 0) ! ⟩)
    ↓ seal 2 ★)
    ↑ unseal 2 ★)
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₁₁ ⟩
  (((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id (＇ 0) ! ⟩)
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩)
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₁₂ ⟩
  ((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id (＇ 0) ! ⟩)
    ⟨ ？ (id (＇ 0)) ⟩)
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₁₃ ⟩
  ($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₁₄ ⟩
  $ (κℕ 7) ∎[]

example12-left-trace :
  Σ TyCtx (λ Δ′ →
  Σ (StoreChanges 0 Δ′) (λ χs →
  Σ (Term Δ′) (λ V →
    (example12-left —↠[ χs ] V) × Value V)))
example12-left-trace =
  Δ′ left-step₁₄ , left-changes , left-final ,
  example12-left-reduction , left-final-value

------------------------------------------------------------------------
-- Right program: ordinary polymorphic identity instantiated at ℕ
------------------------------------------------------------------------

right₀ : Term 0
right₀ = ((Λ (ƛ (` 0))) ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)

right-store₀ : TyStore 0
right-store₀ = store-empty

-- 1. β-Λ allocates the ℕ representation for the type application.
right-step₀ : OneStep right-store₀ right₀
right-step₀ = from-just-step (step? right-store₀ right₀) refl

right₁ : Term (Δ′ right-step₀)
right₁ =
  ((ƛ (` 0)) ↑ (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ)))
    · $ (κℕ 7)

right-store₁ : TyStore (Δ′ right-step₀)
right-store₁ = store-after right-step₀

-- 2. β-reveal-⇒ distributes the generated conversion across application.
right-step₁ : OneStep right-store₁ right₁
right-step₁ = from-just-step (step? right-store₁ right₁) refl

right₂ : Term (Δ′ right-step₁)
right₂ =
  ((ƛ (` 0)) ·
    (($ (κℕ 7)) ↓ seal 0 (‵ `ℕ)))
  ↑ unseal 0 (‵ `ℕ)

right-store₂ : TyStore (Δ′ right-step₁)
right-store₂ = store-after right-step₁

-- 3. β substitutes the sealed argument into the identity body.
right-step₂ : OneStep right-store₂ right₂
right-step₂ = from-just-step (step? right-store₂ right₂) refl

right₃ : Term (Δ′ right-step₂)
right₃ =
  (($ (κℕ 7)) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)

right-store₃ : TyStore (Δ′ right-step₂)
right-store₃ = store-after right-step₂

-- 4. conceal-reveal exposes the natural-number value.
right-step₃ : OneStep right-store₃ right₃
right-step₃ = from-just-step (step? right-store₃ right₃) refl

right-final : Term (Δ′ right-step₃)
right-final = $ (κℕ 7)

right-final-is-7 : right-final ≡ $ (κℕ 7)
right-final-is-7 = refl

right-final-value : Value right-final
right-final-value = from-just-value (value? right-final) refl

right-changes : StoreChanges 0 (Δ′ right-step₃)
right-changes =
  bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ []

example12-right-reduction : example12-right —↠[ right-changes ] right-final
example12-right-reduction =
  ((Λ (ƛ (` 0))) ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)
  —→[ bind (‵ `ℕ) ]⟨ reduction right-step₀ ⟩
  ((ƛ (` 0)) ↑ (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ)))
    · $ (κℕ 7)
  —→[ keep ]⟨ reduction right-step₁ ⟩
  ((ƛ (` 0)) · (($ (κℕ 7)) ↓ seal 0 (‵ `ℕ)))
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₂ ⟩
  (($ (κℕ 7)) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₃ ⟩
  $ (κℕ 7) ∎[]
