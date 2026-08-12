module proof.DGG.CompileImageShape where

-- File Charter:
--   * Defines a decidable syntactic over-approximation of the term shapes
--     emitted by Compile.compile.
--   * Proves the generic compile-output shape theorem and records refl gates
--     for every Phase-1 catalog entry.
--   * Checks the Phase-0 hand-built suspect pair against the shape grammar.
--   * Depends on Compile, ReachabilityCatalog, and ReachabilityScreen.

open import Data.Bool using (Bool; false; true; _∧_; _∨_)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore; store-empty; store-lift)
open import TermCtx using (TermCtx)
open import Consistency using (_⊢_∼_)
open import GradualTerms using (_∣_⊢_⦂_)
open import Compile using (compile)
import CastTerms as C
import proof.DGG.ReachabilityCatalog as RC
import proof.DGG.ReachabilityScreen as RS

------------------------------------------------------------------------
-- Syntactic shape grammar
------------------------------------------------------------------------

mutual

  image-shape? : ∀ {Δ} → C.Term Δ → Bool
  image-shape? (C.` x) = true
  image-shape? (C.ƛ M) = image-shape? M
  image-shape? (L C.· M) = image-head? L ∧ image-operand? M
  image-shape? (C.Λ M) = image-shape? M
  image-shape? (M C.⦂∀ B [ A ]) = image-shape? M
  image-shape? (C.$ κ) = true
  image-shape? (L C.⊕[ op ] M) =
    image-operand? L ∧ image-operand? M
  image-shape? (M C.⟨ c ⟩) = false
  image-shape? (M C.↑ c) = false
  image-shape? (M C.↓ c) = false
  image-shape? C.blame = false

  image-cast? : ∀ {Δ} → C.Term Δ → Bool
  image-cast? (M C.⟨ c ⟩) = image-shape? M
  image-cast? (C.` x) = false
  image-cast? (C.ƛ M) = false
  image-cast? (L C.· M) = false
  image-cast? (C.Λ M) = false
  image-cast? (M C.⦂∀ B [ A ]) = false
  image-cast? (C.$ κ) = false
  image-cast? (L C.⊕[ op ] M) = false
  image-cast? (M C.↑ c) = false
  image-cast? (M C.↓ c) = false
  image-cast? C.blame = false

  image-head? : ∀ {Δ} → C.Term Δ → Bool
  image-head? M = image-shape? M ∨ image-cast? M

  image-operand? : ∀ {Δ} → C.Term Δ → Bool
  image-operand? = image-cast?

image-head-shape : ∀ {Δ} {M : C.Term Δ}
  → image-shape? M ≡ true
  → image-head? M ≡ true
image-head-shape M-ok rewrite M-ok = refl

image-head-cast : ∀ {Δ} {M : C.Term Δ} {μ A B}
    {c : μ ⊢ A ∼ B}
  → image-shape? M ≡ true
  → image-head? (M C.⟨ c ⟩) ≡ true
image-head-cast M-ok rewrite M-ok = refl

image-operand-cast : ∀ {Δ} {M : C.Term Δ} {μ A B}
    {c : μ ⊢ A ∼ B}
  → image-shape? M ≡ true
  → image-operand? (M C.⟨ c ⟩) ≡ true
image-operand-cast M-ok rewrite M-ok = refl

------------------------------------------------------------------------
-- Generic compile-output shape theorem
------------------------------------------------------------------------

compile-image-shape : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {M A}
  → (M⊢ : Δ ∣ Γ ⊢ M ⦂ A)
  → image-shape? (proj₁ (compile {Σ = Σ} M⊢)) ≡ true
compile-image-shape (GradualTerms.⊢` x∈) = refl
compile-image-shape {Σ = Σ} (GradualTerms.⊢ƛ M⊢)
    rewrite compile-image-shape {Σ = Σ} M⊢ =
  refl
compile-image-shape {Σ = Σ} (GradualTerms.⊢· L⊢ M⊢ A∼A′)
    rewrite compile-image-shape {Σ = Σ} L⊢
          | compile-image-shape {Σ = Σ} M⊢ =
  refl
compile-image-shape {Σ = Σ} (GradualTerms.⊢·★ L⊢ M⊢ A′∼★)
    rewrite compile-image-shape {Σ = Σ} L⊢
          | compile-image-shape {Σ = Σ} M⊢ =
  refl
compile-image-shape {Σ = Σ} (GradualTerms.⊢Λ vM M⊢)
    rewrite compile-image-shape {Σ = store-lift Σ} M⊢ =
  refl
compile-image-shape {Σ = Σ} (GradualTerms.⊢• M⊢)
    rewrite compile-image-shape {Σ = Σ} M⊢ =
  refl
compile-image-shape (GradualTerms.⊢$ κ) = refl
compile-image-shape {Σ = Σ}
    (GradualTerms.⊢⊕ op L⊢ A∼arg M⊢ B∼arg)
    rewrite compile-image-shape {Σ = Σ} L⊢
          | compile-image-shape {Σ = Σ} M⊢ =
  refl

------------------------------------------------------------------------
-- Phase-1 catalog gates
------------------------------------------------------------------------

compiled-entry-image-shape? : RC.SourceEntry → Bool
compiled-entry-image-shape? e =
  image-shape? (RS.Entry.more-precise (RC.compiled-standard e)) ∧
  image-shape? (RS.Entry.more-imprecise (RC.compiled-standard e))

baseline-direct-image-shape :
  compiled-entry-image-shape? RC.baseline-direct ≡ true
baseline-direct-image-shape = refl

baseline-nat-direct-image-shape :
  compiled-entry-image-shape? RC.baseline-nat-direct ≡ true
baseline-nat-direct-image-shape = refl

baseline-bool-direct-image-shape :
  compiled-entry-image-shape? RC.baseline-bool-direct ≡ true
baseline-bool-direct-image-shape = refl

baseline-poly-to-dyn-image-shape :
  compiled-entry-image-shape? RC.baseline-poly-to-dyn ≡ true
baseline-poly-to-dyn-image-shape = refl

baseline-bool-to-dyn-image-shape :
  compiled-entry-image-shape? RC.baseline-bool-to-dyn ≡ true
baseline-bool-to-dyn-image-shape = refl

baseline-fun-to-dyn-image-shape :
  compiled-entry-image-shape? RC.baseline-fun-to-dyn ≡ true
baseline-fun-to-dyn-image-shape = refl

baseline-higher-order-image-shape :
  compiled-entry-image-shape? RC.baseline-higher-order ≡ true
baseline-higher-order-image-shape = refl

seal-chain-depth1-image-shape :
  compiled-entry-image-shape? RC.seal-chain-depth1 ≡ true
seal-chain-depth1-image-shape = refl

seal-chain-depth2-image-shape :
  compiled-entry-image-shape? RC.seal-chain-depth2 ≡ true
seal-chain-depth2-image-shape = refl

seal-chain-depth3-image-shape :
  compiled-entry-image-shape? RC.seal-chain-depth3 ≡ true
seal-chain-depth3-image-shape = refl

seal-chain-depth4-image-shape :
  compiled-entry-image-shape? RC.seal-chain-depth4 ≡ true
seal-chain-depth4-image-shape = refl

skew-tag-depth2-image-shape :
  compiled-entry-image-shape? RC.skew-tag-depth2 ≡ true
skew-tag-depth2-image-shape = refl

skew-tag-depth3-image-shape :
  compiled-entry-image-shape? RC.skew-tag-depth3 ≡ true
skew-tag-depth3-image-shape = refl

skew-star-inst-image-shape :
  compiled-entry-image-shape? RC.skew-star-inst ≡ true
skew-star-inst-image-shape = refl

tag-boundary-depth4-image-shape :
  compiled-entry-image-shape? RC.tag-boundary-depth4 ≡ true
tag-boundary-depth4-image-shape = refl

tag-boundary-star-inst-image-shape :
  compiled-entry-image-shape? RC.tag-boundary-star-inst ≡ true
tag-boundary-star-inst-image-shape = refl

gen-inst-return-poly-image-shape :
  compiled-entry-image-shape? RC.gen-inst-return-poly ≡ true
gen-inst-return-poly-image-shape = refl

gen-inst-self-nat-image-shape :
  compiled-entry-image-shape? RC.gen-inst-self-nat ≡ true
gen-inst-self-nat-image-shape = refl

reveal-conceal-self-star-image-shape :
  compiled-entry-image-shape? RC.reveal-conceal-self-star ≡ true
reveal-conceal-self-star-image-shape = refl

reveal-conceal-return-poly-image-shape :
  compiled-entry-image-shape? RC.reveal-conceal-return-poly ≡ true
reveal-conceal-return-poly-image-shape = refl

shared-prefix-nat-image-shape :
  compiled-entry-image-shape? RC.shared-prefix-nat ≡ true
shared-prefix-nat-image-shape = refl

shared-prefix-bool-image-shape :
  compiled-entry-image-shape? RC.shared-prefix-bool ≡ true
shared-prefix-bool-image-shape = refl

shared-prefix-star-image-shape :
  compiled-entry-image-shape? RC.shared-prefix-star ≡ true
shared-prefix-star-image-shape = refl

higher-order-poly-arg-image-shape :
  compiled-entry-image-shape? RC.higher-order-poly-arg ≡ true
higher-order-poly-arg-image-shape = refl

higher-order-shared-arg-image-shape :
  compiled-entry-image-shape? RC.higher-order-shared-arg ≡ true
higher-order-shared-arg-image-shape = refl

adversarial-source-chain-image-shape :
  compiled-entry-image-shape? RC.adversarial-source-chain ≡ true
adversarial-source-chain-image-shape = refl

adversarial-source-star-image-shape :
  compiled-entry-image-shape? RC.adversarial-source-star ≡ true
adversarial-source-star-image-shape = refl

blame-dyn-bool-image-shape :
  compiled-entry-image-shape? RC.blame-dyn-bool ≡ true
blame-dyn-bool-image-shape = refl

------------------------------------------------------------------------
-- Phase-0 suspect exclusion
------------------------------------------------------------------------

tag-chain-program-outside-image :
  image-shape? RS.tag-chain-program ≡ false
tag-chain-program-outside-image = refl

tag-direct-program-outside-image :
  image-shape? RS.tag-direct-program ≡ false
tag-direct-program-outside-image = refl
