module proof.DGG.ExampleTerms where

-- File Charter:
--   * Ports Cambridge26 Example 12 to the GTSFImp cast calculus.
--   * Records the two executable programs from that example and their typing
--     derivations.
--   * Uses Eval and OneStep to compute reduction traces that finish in
--     returned values.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore; store-empty)
open import TermCtx using (Z)
open import Consistency
open import Conversion
open import Primitives
open import CastTerms
open import Reduction
open import Eval using (step?; value?)
import proof.DGG.OneStep as Step
open Step using
  (OneStep; Δ′; reduction; from-just-step; store-after;
   from-just-value)

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

-- GTSFImp writes imprecision as source ⊑ target: the left term is more
-- precise, and the right term is less precise.

example12-right : Term 0
example12-right =
  (((polyId ⟨ ν̅α-α♯→α♭ ⟩) ⟨ να-α!→α? ⟩)
    ⦂∀ X⇒X [ ℕᵗ ]) · c

example12-right-⊢ : ∅ ⊢ example12-right ⦂ ℕᵗ
example12-right-⊢ =
  ⊢·
    (⊢• (⊢⟨⟩
      (⊢⟨⟩ polyId-⊢ ν̅α-α♯→α♭) να-α!→α?))
    c-⊢

example12-left : Term 0
example12-left = (polyId ⦂∀ X⇒X [ ℕᵗ ]) · c

example12-left-⊢ : ∅ ⊢ example12-left ⦂ ℕᵗ
example12-left-⊢ = ⊢· (⊢• polyId-⊢) c-⊢

------------------------------------------------------------------------
-- Checked one-step traces from Eval
------------------------------------------------------------------------

-- The helper record and conversion from executable `Maybe` results live in
-- proof.DGG.OneStep; this module keeps the concrete Example 12 traces.

------------------------------------------------------------------------
-- Right program: up through ν̅, down through ν, instantiate, and apply
------------------------------------------------------------------------

right₀ : Term 0
right₀ =
  ((((Λ (ƛ (` 0)))
    ⟨ (inst_ {μ = idᶜ {Δ = 0}} ⦃ z∈A = ∈-fun-left var-∈ ⦄
        ((id {μ = instᵐ (idᶜ {Δ = 0})} (＇ 0) !) ↦
         (id {μ = instᵐ (idᶜ {Δ = 0})} (＇ 0) !))
        (λ ())) ⟩)
    ⟨ (gen_ {μ = idᶜ {Δ = 0}} ⦃ z∈B = ∈-fun-left var-∈ ⦄
        ((？ (id (＇ 0))) ↦ (？ (id (＇ 0)))) (λ ())) ⟩)
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)

right-store₀ : TyStore 0
right-store₀ = store-empty

-- 1. β-inst for the ν̅α.α♯→α♭ cast.
right-step₀ : OneStep right-store₀ right₀
right-step₀ = from-just-step (step? right-store₀ right₀) refl

right₁ : Term (Δ′ right-step₀)
right₁ =
  ((((Λ (ƛ (` 0))) ⦂∀ (＇ 0 ⇒ ＇ 0) [ ＇ 0 ])
      ↑ (seal 0 ★ ↦↑ unseal 0 ★)
      ⟨ id {μ = renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})} ★ ↦ id ★ ⟩
      ⟨ (gen_ {μ = extᵐ (idᶜ {Δ = 0})}
          ⦃ z∈B = ∈-fun-left var-∈ ⦄
          ((？ (id (＇ 0))) ↦ (？ (id (＇ 0)))) (λ ())) ⟩)
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)

right-store₁ : TyStore (Δ′ right-step₀)
right-store₁ = store-after right-step₀

-- 2. β-Λ under the first reveal/cast wrappers.
right-step₁ : OneStep right-store₁ right₁
right-step₁ = from-just-step (step? right-store₁ right₁) refl

right₂ : Term (Δ′ right-step₁)
right₂ =
  (((((ƛ (` 0))
    ↑ (seal 0 (＇ 1) ↦↑ unseal 0 (＇ 1)))
    ↑ (seal 1 ★ ↦↑ unseal 1 ★))
    ⟨ id {μ = applyEnv (bind (＇ 0))
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★ ↦ id ★ ⟩)
    ⟨ (gen_ {μ = extᵐ (extᵐ (idᶜ {Δ = 0}))}
        ⦃ z∈B = ∈-fun-left var-∈ ⦄
        ((？ (id (＇ 0))) ↦ (？ (id (＇ 0)))) (λ ())) ⟩
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)

right-store₂ : TyStore (Δ′ right-step₁)
right-store₂ = store-after right-step₁

-- 3. β-gen for the να.α!→α? cast at the ℕ instantiation.
right-step₂ : OneStep right-store₂ right₂
right-step₂ = from-just-step (step? right-store₂ right₂) refl

right₃ : Term (Δ′ right-step₂)
right₃ =
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

right-store₃ : TyStore (Δ′ right-step₂)
right-store₃ = store-after right-step₂

-- 4. β-reveal-⇒ distributes the outer function reveal.
right-step₃ : OneStep right-store₃ right₃
right-step₃ = from-just-step (step? right-store₃ right₃) refl

right₄ : Term (Δ′ right-step₃)
right₄ =
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

right-store₄ : TyStore (Δ′ right-step₃)
right-store₄ = store-after right-step₃

-- 5. β-⇒ pushes the first function cast to the argument/result.
right-step₄ : OneStep right-store₄ right₄
right-step₄ = from-just-step (step? right-store₄ right₄) refl

right₅ : Term (Δ′ right-step₄)
right₅ =
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

right-store₅ : TyStore (Δ′ right-step₄)
right-store₅ = store-after right-step₄

-- 6. β-⇒ pushes the second function cast to the argument/result.
right-step₅ : OneStep right-store₅ right₅
right-step₅ = from-just-step (step? right-store₅ right₅) refl

right₆ : Term (Δ′ right-step₅)
right₆ =
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

right-store₆ : TyStore (Δ′ right-step₅)
right-store₆ = store-after right-step₅

-- 7. β-id removes an administrative identity cast from the argument.
right-step₆ : OneStep right-store₆ right₆
right-step₆ = from-just-step (step? right-store₆ right₆) refl

right₇ : Term (Δ′ right-step₆)
right₇ =
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

right-store₇ : TyStore (Δ′ right-step₆)
right-store₇ = store-after right-step₆

-- 8. β-reveal-⇒ distributes the next function reveal.
right-step₇ : OneStep right-store₇ right₇
right-step₇ = from-just-step (step? right-store₇ right₇) refl

right₈ : Term (Δ′ right-step₇)
right₈ =
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

right-store₈ : TyStore (Δ′ right-step₇)
right-store₈ = store-after right-step₇

-- 9. β-reveal-⇒ distributes the innermost function reveal.
right-step₈ : OneStep right-store₈ right₈
right-step₈ = from-just-step (step? right-store₈ right₈) refl

right₉ : Term (Δ′ right-step₈)
right₉ =
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

right-store₉ : TyStore (Δ′ right-step₈)
right-store₉ = store-after right-step₈

-- 10. β substitutes the fully wrapped argument into the identity body.
right-step₉ : OneStep right-store₉ right₉
right-step₉ = from-just-step (step? right-store₉ right₉) refl

right₁₀ : Term (Δ′ right-step₉)
right₁₀ =
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

right-store₁₀ : TyStore (Δ′ right-step₉)
right-store₁₀ = store-after right-step₉

-- 11. conceal-reveal cancels one abstract-boundary round trip.
right-step₁₀ : OneStep right-store₁₀ right₁₀
right-step₁₀ = from-just-step (step? right-store₁₀ right₁₀) refl

right₁₁ : Term (Δ′ right-step₁₀)
right₁₁ =
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

right-store₁₁ : TyStore (Δ′ right-step₁₀)
right-store₁₁ = store-after right-step₁₀

-- 12. conceal-reveal cancels the next abstract-boundary round trip.
right-step₁₁ : OneStep right-store₁₁ right₁₁
right-step₁₁ = from-just-step (step? right-store₁₁ right₁₁) refl

right₁₂ : Term (Δ′ right-step₁₁)
right₁₂ =
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

right-store₁₂ : TyStore (Δ′ right-step₁₁)
right-store₁₂ = store-after right-step₁₁

-- 13. β-id removes the remaining administrative identity cast.
right-step₁₂ : OneStep right-store₁₂ right₁₂
right-step₁₂ = from-just-step (step? right-store₁₂ right₁₂) refl

right₁₃ : Term (Δ′ right-step₁₂)
right₁₃ =
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

right-store₁₃ : TyStore (Δ′ right-step₁₂)
right-store₁₃ = store-after right-step₁₂

-- 14. tag-untag cancels the matching variable-ground tag pair.
right-step₁₃ : OneStep right-store₁₃ right₁₃
right-step₁₃ = from-just-step (step? right-store₁₃ right₁₃) refl

right₁₄ : Term (Δ′ right-step₁₃)
right₁₄ =
  ($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)

right-store₁₄ : TyStore (Δ′ right-step₁₃)
right-store₁₄ = store-after right-step₁₃

-- 15. conceal-reveal exposes the original natural-number value.
right-step₁₄ : OneStep right-store₁₄ right₁₄
right-step₁₄ = from-just-step (step? right-store₁₄ right₁₄) refl

right-final : Term (Δ′ right-step₁₄)
right-final = $ (κℕ 7)

right-final-is-7 : right-final ≡ $ (κℕ 7)
right-final-is-7 = refl

right-final-value : Value right-final
right-final-value = from-just-value (value? right-final) refl

right-changes : StoreChanges 0 (Δ′ right-step₁₄)
right-changes =
  bind ★ ∷ bind (＇ 0) ∷ bind (‵ `ℕ) ∷
  keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
  keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ []

example12-right-reduction : example12-right —↠[ right-changes ] right-final
example12-right-reduction =
  ((((Λ (ƛ (` 0)))
    ⟨ ((inst ((id (＇ 0) !) ↦ (id (＇ 0) !))) (λ ())) ⟩)
    ⟨ ((gen ((？ (id (＇ 0))) ↦ (？ (id (＇ 0))))) (λ ())) ⟩)
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)
  —→[ bind ★ ]⟨ reduction right-step₀ ⟩
  ((((Λ (ƛ (` 0))) ⦂∀ (＇ 0 ⇒ ＇ 0) [ ＇ 0 ])
      ↑ (seal 0 ★ ↦↑ unseal 0 ★)
      ⟨ id ★ ↦ id ★ ⟩
      ⟨ ((gen ((？ (id (＇ 0))) ↦ (？ (id (＇ 0))))) (λ ())) ⟩)
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)
  —→[ bind (＇ 0) ]⟨ reduction right-step₁ ⟩
  (((((ƛ (` 0))
    ↑ (seal 0 (＇ 1) ↦↑ unseal 0 (＇ 1)))
    ↑ (seal 1 ★ ↦↑ unseal 1 ★))
    ⟨ id ★ ↦ id ★ ⟩)
    ⟨ ((gen ((？ (id (＇ 0))) ↦ (？ (id (＇ 0))))) (λ ())) ⟩
    ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)
  —→[ bind (‵ `ℕ) ]⟨ reduction right-step₂ ⟩
  ((((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    ⟨ id ★ ↦ id ★ ⟩)
    ⟨ (？ (id (＇ 0))) ↦ (？ (id (＇ 0))) ⟩)
    ↑ (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ)))
    · $ (κℕ 7)
  —→[ keep ]⟨ reduction right-step₃ ⟩
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    ⟨ id ★ ↦ id ★ ⟩)
    ⟨ (？ (id (＇ 0))) ↦ (？ (id (＇ 0))) ⟩)
    · ($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₄ ⟩
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    ⟨ id ★ ↦ id ★ ⟩)
    · (($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id (＇ 0) ! ⟩))
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₅ ⟩
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    · ((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id (＇ 0) ! ⟩)
      ⟨ id ★ ⟩))
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₆ ⟩
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    ↑ (seal 2 ★ ↦↑ unseal 2 ★))
    · (($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id (＇ 0) ! ⟩))
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₇ ⟩
  (((((ƛ (` 0))
    ↑ (seal 1 (＇ 2) ↦↑ unseal 1 (＇ 2)))
    · ((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
      ⟨ id (＇ 0) ! ⟩)
      ↓ seal 2 ★))
    ↑ unseal 2 ★)
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₈ ⟩
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
  —→[ keep ]⟨ reduction right-step₉ ⟩
  ((((((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id (＇ 0) ! ⟩)
    ↓ seal 2 ★)
    ↓ seal 1 (＇ 2))
    ↑ unseal 1 (＇ 2))
    ↑ unseal 2 ★)
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₁₀ ⟩
  ((((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id (＇ 0) ! ⟩)
    ↓ seal 2 ★)
    ↑ unseal 2 ★)
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₁₁ ⟩
  (((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id (＇ 0) ! ⟩)
    ⟨ id ★ ⟩)
    ⟨ ？ (id (＇ 0)) ⟩)
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₁₂ ⟩
  ((($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
    ⟨ id (＇ 0) ! ⟩)
    ⟨ ？ (id (＇ 0)) ⟩)
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₁₃ ⟩
  ($ (κℕ 7) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction right-step₁₄ ⟩
  $ (κℕ 7) ∎[]

------------------------------------------------------------------------
-- Left program: ordinary polymorphic identity instantiated at ℕ
------------------------------------------------------------------------

left₀ : Term 0
left₀ = ((Λ (ƛ (` 0))) ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)

left-store₀ : TyStore 0
left-store₀ = store-empty

-- 1. β-Λ allocates the ℕ representation for the type application.
left-step₀ : OneStep left-store₀ left₀
left-step₀ = from-just-step (step? left-store₀ left₀) refl

left₁ : Term (Δ′ left-step₀)
left₁ =
  ((ƛ (` 0)) ↑ (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ)))
    · $ (κℕ 7)

left-store₁ : TyStore (Δ′ left-step₀)
left-store₁ = store-after left-step₀

-- 2. β-reveal-⇒ distributes the generated conversion across application.
left-step₁ : OneStep left-store₁ left₁
left-step₁ = from-just-step (step? left-store₁ left₁) refl

left₂ : Term (Δ′ left-step₁)
left₂ =
  ((ƛ (` 0)) ·
    (($ (κℕ 7)) ↓ seal 0 (‵ `ℕ)))
  ↑ unseal 0 (‵ `ℕ)

left-store₂ : TyStore (Δ′ left-step₁)
left-store₂ = store-after left-step₁

-- 3. β substitutes the sealed argument into the identity body.
left-step₂ : OneStep left-store₂ left₂
left-step₂ = from-just-step (step? left-store₂ left₂) refl

left₃ : Term (Δ′ left-step₂)
left₃ =
  (($ (κℕ 7)) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)

left-store₃ : TyStore (Δ′ left-step₂)
left-store₃ = store-after left-step₂

-- 4. conceal-reveal exposes the natural-number value.
left-step₃ : OneStep left-store₃ left₃
left-step₃ = from-just-step (step? left-store₃ left₃) refl

left-final : Term (Δ′ left-step₃)
left-final = $ (κℕ 7)

left-final-is-7 : left-final ≡ $ (κℕ 7)
left-final-is-7 = refl

left-final-value : Value left-final
left-final-value = from-just-value (value? left-final) refl

left-changes : StoreChanges 0 (Δ′ left-step₃)
left-changes =
  bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ []

example12-left-reduction : example12-left —↠[ left-changes ] left-final
example12-left-reduction =
  ((Λ (ƛ (` 0))) ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · $ (κℕ 7)
  —→[ bind (‵ `ℕ) ]⟨ reduction left-step₀ ⟩
  ((ƛ (` 0)) ↑ (seal 0 (‵ `ℕ) ↦↑ unseal 0 (‵ `ℕ)))
    · $ (κℕ 7)
  —→[ keep ]⟨ reduction left-step₁ ⟩
  ((ƛ (` 0)) · (($ (κℕ 7)) ↓ seal 0 (‵ `ℕ)))
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₂ ⟩
  (($ (κℕ 7)) ↓ seal 0 (‵ `ℕ))
  ↑ unseal 0 (‵ `ℕ)
  —→[ keep ]⟨ reduction left-step₃ ⟩
  $ (κℕ 7) ∎[]
