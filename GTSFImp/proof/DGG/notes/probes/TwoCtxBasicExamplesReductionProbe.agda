{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxBasicExamplesReductionProbe where

-- File Charter:
--   * Replays the ordinary compiler output for the matched and source-only
--     42 examples in proof.DGG.ReachabilityCatalog.
--   * Records every whole-term step through type allocation, function reveal,
--     term beta, and conceal-reveal cancellation on the polymorphic sides.
--   * Checks that the matched run allocates on both sides, whereas the
--     source-only run allocates only on the left and leaves the right store
--     unchanged.
--   * Depends only on Compile, Eval, Reduction, OneStep, and the catalog's
--     source terms and typing derivations; it does not use term imprecision.

open import Data.Product using (_×_; _,_; proj₁)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (★; ‵_; `ℕ)
open import TyStore using (TyStore; store-empty)
open import Consistency using (id; _!)
open import Conversion using (seal; unseal)
open import Primitives using (κℕ)
open import CastTerms using
  (Term; Value; `_; ƛ_; _·_; $; _⟨_⟩; _↑_; _↓_)
open import Reduction using
  (bind; keep; []; _∷_; _—→[_]_; _—↠[_]_; _∎[]; _—→[_]⟨_⟩_)
open import Eval using (step?; value?)
open import Compile using (compile)
import proof.DGG.OneStep as Step
open Step using
  (OneStep; Δ′; change; next; reduction; from-just-step; store-after;
   from-just-value)
import proof.DGG.ReachabilityCatalog as RC


------------------------------------------------------------------------
-- Matched instantiation: both compiled sides allocate
------------------------------------------------------------------------

matched-left₀ : Term 0
matched-left₀ =
  proj₁ (compile {Σ = store-empty} RC.matchedInstPathᴸ⊢)

matched-left-store₀ : TyStore 0
matched-left-store₀ = store-empty

matched-left-step₀ : OneStep matched-left-store₀ matched-left₀
matched-left-step₀ =
  from-just-step (step? matched-left-store₀ matched-left₀) refl

matched-left₁ : Term (Δ′ matched-left-step₀)
matched-left₁ = next matched-left-step₀

matched-left-store₁ : TyStore (Δ′ matched-left-step₀)
matched-left-store₁ = store-after matched-left-step₀

matched-left-step₁ : OneStep matched-left-store₁ matched-left₁
matched-left-step₁ =
  from-just-step (step? matched-left-store₁ matched-left₁) refl

matched-left₂ : Term (Δ′ matched-left-step₁)
matched-left₂ = next matched-left-step₁

matched-left-store₂ : TyStore (Δ′ matched-left-step₁)
matched-left-store₂ = store-after matched-left-step₁

matched-left-step₂ : OneStep matched-left-store₂ matched-left₂
matched-left-step₂ =
  from-just-step (step? matched-left-store₂ matched-left₂) refl

matched-left₃ : Term (Δ′ matched-left-step₂)
matched-left₃ = next matched-left-step₂

matched-left-store₃ : TyStore (Δ′ matched-left-step₂)
matched-left-store₃ = store-after matched-left-step₂

matched-left-step₃ : OneStep matched-left-store₃ matched-left₃
matched-left-step₃ =
  from-just-step (step? matched-left-store₃ matched-left₃) refl

matched-left₄ : Term (Δ′ matched-left-step₃)
matched-left₄ = next matched-left-step₃

matched-left-store₄ : TyStore (Δ′ matched-left-step₃)
matched-left-store₄ = store-after matched-left-step₃

matched-left-step₄ : OneStep matched-left-store₄ matched-left₄
matched-left-step₄ =
  from-just-step (step? matched-left-store₄ matched-left₄) refl

matched-left-final : Term (Δ′ matched-left-step₄)
matched-left-final = next matched-left-step₄

matched-left-final-value : Value matched-left-final
matched-left-final-value =
  from-just-value (value? matched-left-final) refl

matched-right₀ : Term 0
matched-right₀ =
  proj₁ (compile {Σ = store-empty} RC.matchedInstPathᴿ⊢)

matched-right-store₀ : TyStore 0
matched-right-store₀ = store-empty

matched-right-step₀ : OneStep matched-right-store₀ matched-right₀
matched-right-step₀ =
  from-just-step (step? matched-right-store₀ matched-right₀) refl

matched-right₁ : Term (Δ′ matched-right-step₀)
matched-right₁ = next matched-right-step₀

matched-right-store₁ : TyStore (Δ′ matched-right-step₀)
matched-right-store₁ = store-after matched-right-step₀

matched-right-step₁ : OneStep matched-right-store₁ matched-right₁
matched-right-step₁ =
  from-just-step (step? matched-right-store₁ matched-right₁) refl

matched-right₂ : Term (Δ′ matched-right-step₁)
matched-right₂ = next matched-right-step₁

matched-right-store₂ : TyStore (Δ′ matched-right-step₁)
matched-right-store₂ = store-after matched-right-step₁

matched-right-step₂ : OneStep matched-right-store₂ matched-right₂
matched-right-step₂ =
  from-just-step (step? matched-right-store₂ matched-right₂) refl

matched-right₃ : Term (Δ′ matched-right-step₂)
matched-right₃ = next matched-right-step₂

matched-right-store₃ : TyStore (Δ′ matched-right-step₂)
matched-right-store₃ = store-after matched-right-step₂

matched-right-step₃ : OneStep matched-right-store₃ matched-right₃
matched-right-step₃ =
  from-just-step (step? matched-right-store₃ matched-right₃) refl

matched-right-final : Term (Δ′ matched-right-step₃)
matched-right-final = next matched-right-step₃

matched-right-final-value : Value matched-right-final
matched-right-final-value =
  from-just-value (value? matched-right-final) refl

matched-left-allocates : change matched-left-step₀ ≡ bind (‵ `ℕ)
matched-left-allocates = refl

matched-right-allocates : change matched-right-step₀ ≡ bind ★
matched-right-allocates = refl

matched-left-subsequent-changes :
    change matched-left-step₁ ≡ keep
  × change matched-left-step₂ ≡ keep
  × change matched-left-step₃ ≡ keep
  × change matched-left-step₄ ≡ keep
matched-left-subsequent-changes = refl , refl , refl , refl

matched-right-subsequent-changes :
    change matched-right-step₁ ≡ keep
  × change matched-right-step₂ ≡ keep
  × change matched-right-step₃ ≡ keep
matched-right-subsequent-changes = refl , refl , refl

matched-left-β-Λ :
  matched-left₀ —→[ bind (‵ `ℕ) ] matched-left₁
matched-left-β-Λ = reduction matched-left-step₀

matched-left-β-id : matched-left₁ —→[ keep ] matched-left₂
matched-left-β-id = reduction matched-left-step₁

matched-left-β-reveal-⇒ : matched-left₂ —→[ keep ] matched-left₃
matched-left-β-reveal-⇒ = reduction matched-left-step₂

matched-left-β-ƛ : matched-left₃ —→[ keep ] matched-left₄
matched-left-β-ƛ = reduction matched-left-step₃

matched-left-conceal-reveal :
  matched-left₄ —→[ keep ] matched-left-final
matched-left-conceal-reveal = reduction matched-left-step₄

matched-right-β-Λ : matched-right₀ —→[ bind ★ ] matched-right₁
matched-right-β-Λ = reduction matched-right-step₀

matched-right-β-reveal-⇒ :
  matched-right₁ —→[ keep ] matched-right₂
matched-right-β-reveal-⇒ = reduction matched-right-step₁

matched-right-β-ƛ : matched-right₂ —→[ keep ] matched-right₃
matched-right-β-ƛ = reduction matched-right-step₂

matched-right-conceal-reveal :
  matched-right₃ —→[ keep ] matched-right-final
matched-right-conceal-reveal = reduction matched-right-step₃

matched-left-reduction :
  matched-left₀ —↠[
    bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
    matched-left-final
matched-left-reduction =
  matched-left₀
  —→[ bind (‵ `ℕ) ]⟨ reduction matched-left-step₀ ⟩
  matched-left₁
  —→[ keep ]⟨ reduction matched-left-step₁ ⟩
  matched-left₂
  —→[ keep ]⟨ reduction matched-left-step₂ ⟩
  matched-left₃
  —→[ keep ]⟨ reduction matched-left-step₃ ⟩
  matched-left₄
  —→[ keep ]⟨ reduction matched-left-step₄ ⟩
  matched-left-final ∎[]

matched-right-reduction :
  matched-right₀ —↠[ bind ★ ∷ keep ∷ keep ∷ keep ∷ [] ]
    matched-right-final
matched-right-reduction =
  matched-right₀
  —→[ bind ★ ]⟨ reduction matched-right-step₀ ⟩
  matched-right₁
  —→[ keep ]⟨ reduction matched-right-step₁ ⟩
  matched-right₂
  —→[ keep ]⟨ reduction matched-right-step₂ ⟩
  matched-right₃
  —→[ keep ]⟨ reduction matched-right-step₃ ⟩
  matched-right-final ∎[]

-- These are the whole terms immediately after β-reveal-⇒.  The shared
-- runtime pivot is zero; the direct entries differ exactly as the allocations
-- above say: ℕ on the left and ★ on the right.

matched-left-paired-conceal :
  matched-left₃ ≡
    ((ƛ (` 0)) · (($ (κℕ 42)) ↓ seal Fin.zero (‵ `ℕ)))
      ↑ unseal Fin.zero (‵ `ℕ)
matched-left-paired-conceal = refl

matched-right-paired-conceal :
  matched-right₂ ≡
    ((ƛ (` 0)) ·
      ((($ (κℕ 42)) ⟨ id (‵ `ℕ) ! ⟩) ↓ seal Fin.zero ★))
      ↑ unseal Fin.zero ★
matched-right-paired-conceal = refl


------------------------------------------------------------------------
-- Source-only instantiation: only the compiled left side allocates
------------------------------------------------------------------------

source-only-left₀ : Term 0
source-only-left₀ =
  proj₁ (compile {Σ = store-empty} RC.leftOnlyInstPathᴸ⊢)

source-only-left-store₀ : TyStore 0
source-only-left-store₀ = store-empty

source-only-left-step₀ : OneStep source-only-left-store₀ source-only-left₀
source-only-left-step₀ =
  from-just-step (step? source-only-left-store₀ source-only-left₀) refl

source-only-left₁ : Term (Δ′ source-only-left-step₀)
source-only-left₁ = next source-only-left-step₀

source-only-left-store₁ : TyStore (Δ′ source-only-left-step₀)
source-only-left-store₁ = store-after source-only-left-step₀

source-only-left-step₁ :
  OneStep source-only-left-store₁ source-only-left₁
source-only-left-step₁ =
  from-just-step (step? source-only-left-store₁ source-only-left₁) refl

source-only-left₂ : Term (Δ′ source-only-left-step₁)
source-only-left₂ = next source-only-left-step₁

source-only-left-store₂ : TyStore (Δ′ source-only-left-step₁)
source-only-left-store₂ = store-after source-only-left-step₁

source-only-left-step₂ :
  OneStep source-only-left-store₂ source-only-left₂
source-only-left-step₂ =
  from-just-step (step? source-only-left-store₂ source-only-left₂) refl

source-only-left₃ : Term (Δ′ source-only-left-step₂)
source-only-left₃ = next source-only-left-step₂

source-only-left-store₃ : TyStore (Δ′ source-only-left-step₂)
source-only-left-store₃ = store-after source-only-left-step₂

source-only-left-step₃ :
  OneStep source-only-left-store₃ source-only-left₃
source-only-left-step₃ =
  from-just-step (step? source-only-left-store₃ source-only-left₃) refl

source-only-left₄ : Term (Δ′ source-only-left-step₃)
source-only-left₄ = next source-only-left-step₃

source-only-left-store₄ : TyStore (Δ′ source-only-left-step₃)
source-only-left-store₄ = store-after source-only-left-step₃

source-only-left-step₄ :
  OneStep source-only-left-store₄ source-only-left₄
source-only-left-step₄ =
  from-just-step (step? source-only-left-store₄ source-only-left₄) refl

source-only-left-final : Term (Δ′ source-only-left-step₄)
source-only-left-final = next source-only-left-step₄

source-only-left-final-value : Value source-only-left-final
source-only-left-final-value =
  from-just-value (value? source-only-left-final) refl

source-only-right₀ : Term 0
source-only-right₀ =
  proj₁ (compile {Σ = store-empty} RC.leftOnlyInstPathᴿ⊢)

source-only-right-store₀ : TyStore 0
source-only-right-store₀ = store-empty

source-only-right-step₀ :
  OneStep source-only-right-store₀ source-only-right₀
source-only-right-step₀ =
  from-just-step (step? source-only-right-store₀ source-only-right₀) refl

source-only-right-final : Term (Δ′ source-only-right-step₀)
source-only-right-final = next source-only-right-step₀

source-only-right-final-value : Value source-only-right-final
source-only-right-final-value =
  from-just-value (value? source-only-right-final) refl

source-only-left-allocates :
  change source-only-left-step₀ ≡ bind (‵ `ℕ)
source-only-left-allocates = refl

source-only-right-keeps-store : change source-only-right-step₀ ≡ keep
source-only-right-keeps-store = refl

source-only-left-subsequent-changes :
    change source-only-left-step₁ ≡ keep
  × change source-only-left-step₂ ≡ keep
  × change source-only-left-step₃ ≡ keep
  × change source-only-left-step₄ ≡ keep
source-only-left-subsequent-changes = refl , refl , refl , refl

source-only-left-β-Λ :
  source-only-left₀ —→[ bind (‵ `ℕ) ] source-only-left₁
source-only-left-β-Λ = reduction source-only-left-step₀

source-only-left-β-id :
  source-only-left₁ —→[ keep ] source-only-left₂
source-only-left-β-id = reduction source-only-left-step₁

source-only-left-β-reveal-⇒ :
  source-only-left₂ —→[ keep ] source-only-left₃
source-only-left-β-reveal-⇒ = reduction source-only-left-step₂

source-only-left-β-ƛ :
  source-only-left₃ —→[ keep ] source-only-left₄
source-only-left-β-ƛ = reduction source-only-left-step₃

source-only-left-conceal-reveal :
  source-only-left₄ —→[ keep ] source-only-left-final
source-only-left-conceal-reveal = reduction source-only-left-step₄

source-only-right-β-ƛ :
  source-only-right₀ —→[ keep ] source-only-right-final
source-only-right-β-ƛ = reduction source-only-right-step₀

source-only-left-reduction :
  source-only-left₀ —↠[
    bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
    source-only-left-final
source-only-left-reduction =
  source-only-left₀
  —→[ bind (‵ `ℕ) ]⟨ reduction source-only-left-step₀ ⟩
  source-only-left₁
  —→[ keep ]⟨ reduction source-only-left-step₁ ⟩
  source-only-left₂
  —→[ keep ]⟨ reduction source-only-left-step₂ ⟩
  source-only-left₃
  —→[ keep ]⟨ reduction source-only-left-step₃ ⟩
  source-only-left₄
  —→[ keep ]⟨ reduction source-only-left-step₄ ⟩
  source-only-left-final ∎[]

source-only-right-reduction :
  source-only-right₀ —↠[ keep ∷ [] ] source-only-right-final
source-only-right-reduction =
  source-only-right₀
  —→[ keep ]⟨ reduction source-only-right-step₀ ⟩
  source-only-right-final ∎[]

-- The left checkpoint has the same β-reveal-⇒ shape as the matched left
-- run, but the right run has already β-reduced to a tagged constant.  Thus
-- this conceal has no target-side runtime pivot or conceal partner.

source-only-genuinely-left-conceal :
  source-only-left₃ ≡
    ((ƛ (` 0)) · (($ (κℕ 42)) ↓ seal Fin.zero (‵ `ℕ)))
      ↑ unseal Fin.zero (‵ `ℕ)
source-only-genuinely-left-conceal = refl

source-only-right-has-no-conceal :
  source-only-right-final ≡ ($ (κℕ 42)) ⟨ id (‵ `ℕ) ! ⟩
source-only-right-has-no-conceal = refl
