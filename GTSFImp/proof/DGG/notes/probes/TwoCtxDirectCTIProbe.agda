{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxDirectCTIProbe where

-- File Charter:
--   * Checks the no-alias-boundary cast-term-imprecision surface over the
--     canonical two-Ctx world.
--   * Retains the canonical, unique endpoint type-imprecision proof as the
--     relation index; no scoped type wrapper is introduced.
--   * Replaces the plain and smart-comma source-only universal rules with one
--     structural fresh-behind plan.
--   * Folds generator position, endpoint occupancy, conversion typing, and
--     structural rebasing into six typed conversion-action families.
--   * Keeps the term relation independent of conversion-position internals;
--     exact target aliases remain a separate boundary.

import Data.Nat as Nat
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import TyStore using (TyStore; lookupStore)
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import Imprecision using (X⊑X; X⊑★; ⇒⊑⇒)
open import Primitives using
  (Const; Prim; constTy; primArgTy; primResultTy)
open import CastTerms using
  (Ctx; Δᵉ; Σᵉ; Term; Value; _∋ᵗ_⦂_; _⊢_⦂_; `_; ƛ_; _·_; Λ_;
   _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩; _↑_; _↓_; blame)
open import proof.DGG.World
open import proof.DGG.SourceRebasePlan using
  (SourceRebasePlan; rebaseSource)
open import proof.DGG.SourceFreshBehindPlan using
  (SourceFreshBehindPlan; insertSourceFreshBehind)
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition; concealGeneratorPosition)


------------------------------------------------------------------------
-- Typed conversion actions
------------------------------------------------------------------------

data TargetRevealAction {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ)
    {B B′ : Ty (Δᵉ Cᴿ)} (c′ : Conv↑ (Δᵉ Cᴿ) B B′) : Set where

  target-reveal-absent : ∀ {Xᴿ Rᴿ}
    → (c′⊢ : Σᵉ Cᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c′⊢ ≡ generator-absent
    → TargetRevealAction W c′

  target-reveal-only : ∀ {Xᴿ Rᴿ}
    → (∀ Xᴸ
        → toRenameᵗ (ηᴸᶜ W) Xᴸ
          ≢ toRenameᵗ (ηᴿᶜ W) Xᴿ)
    → (c′⊢ : Σᵉ Cᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c′⊢ ≢ generator-absent
    → TargetRevealAction W c′


data TargetConcealAction {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ)
    {B B′ : Ty (Δᵉ Cᴿ)} (c′ : Conv↓ (Δᵉ Cᴿ) B B′) : Set where

  target-conceal-absent : ∀ {Xᴿ Rᴿ}
    → (c′⊢ : Σᵉ Cᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c′⊢ ≡ generator-absent
    → TargetConcealAction W c′

  target-conceal-only : ∀ {Xᴿ Rᴿ}
    → (∀ Xᴸ
        → toRenameᵗ (ηᴸᶜ W) Xᴸ
          ≢ toRenameᵗ (ηᴿᶜ W) Xᴿ)
    → (c′⊢ : Σᵉ Cᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c′⊢ ≢ generator-absent
    → TargetConcealAction W c′


data SourceRevealAction {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ)
    {A A′ : Ty (Δᵉ Cᴸ)} (c : Conv↑ (Δᵉ Cᴸ) A A′) :
    Cᴸ ⊑ᶜ Cᴿ → Set where

  source-reveal-absent : ∀ {Xᴸ Rᴸ}
    → (c⊢ : Σᵉ Cᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → revealGeneratorPosition c⊢ ≡ generator-absent
    → SourceRevealAction W c W

  source-reveal-only : ∀ {Xᴸ Rᴸ}
    → marksᶜ W (toRenameᵗ (ηᴸᶜ W) Xᴸ) ≡ X⊑★
    → (∀ Xᴿ
        → toRenameᵗ (ηᴿᶜ W) Xᴿ
          ≢ toRenameᵗ (ηᴸᶜ W) Xᴸ)
    → lookupStore (Σᵉ Cᴸ) Xᴸ ⊑ᵀ⟨ W ⟩ ★
    → (c⊢ : Σᵉ Cᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → revealGeneratorPosition c⊢ ≢ generator-absent
    → SourceRevealAction W c W

  source-reveal-rebase : ∀ {Xᴸ Xᴿ Rᴸ}
    → toRenameᵗ (ηᴸᶜ W) Xᴸ ≢ toRenameᵗ (ηᴿᶜ W) Xᴿ
    → (plan : SourceRebasePlan W Xᴸ Xᴿ)
    → lookupStore (Σᵉ Cᴸ) Xᴸ
        ⊑ᵀ⟨ rebaseSource plan ⟩ lookupStore (Σᵉ Cᴿ) Xᴿ
    → (c⊢ : Σᵉ Cᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → revealGeneratorPosition c⊢ ≢ generator-absent
    → SourceRevealAction W c (rebaseSource plan)


data SourceConcealAction {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ)
    {A A′ : Ty (Δᵉ Cᴸ)} (c : Conv↓ (Δᵉ Cᴸ) A A′) : Set where

  source-conceal-absent : ∀ {Xᴸ Rᴸ}
    → (c⊢ : Σᵉ Cᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → concealGeneratorPosition c⊢ ≡ generator-absent
    → SourceConcealAction W c

  source-conceal-only : ∀ {Xᴸ Rᴸ}
    → marksᶜ W (toRenameᵗ (ηᴸᶜ W) Xᴸ) ≡ X⊑★
    → (∀ Xᴿ
        → toRenameᵗ (ηᴿᶜ W) Xᴿ
          ≢ toRenameᵗ (ηᴸᶜ W) Xᴸ)
    → lookupStore (Σᵉ Cᴸ) Xᴸ ⊑ᵀ⟨ W ⟩ ★
    → (c⊢ : Σᵉ Cᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → concealGeneratorPosition c⊢ ≢ generator-absent
    → SourceConcealAction W c


data PairedRevealAction {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ)
    {A A′ : Ty (Δᵉ Cᴸ)} {B B′ : Ty (Δᵉ Cᴿ)}
    (c : Conv↑ (Δᵉ Cᴸ) A A′) (c′ : Conv↑ (Δᵉ Cᴿ) B B′) :
    Cᴸ ⊑ᶜ Cᴿ → Set where

  paired-reveal-action : ∀ {Xᴸ Xᴿ Rᴸ Rᴿ}
    → (plan : SourceRebasePlan W Xᴸ Xᴿ)
    → lookupStore (Σᵉ Cᴸ) Xᴸ
        ⊑ᵀ⟨ rebaseSource plan ⟩ lookupStore (Σᵉ Cᴿ) Xᴿ
    → (c⊢ : Σᵉ Cᴸ ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Cᴿ ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
    → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
    → revealGeneratorPosition c⊢ ≢ generator-absent
    → PairedRevealAction W c c′ (rebaseSource plan)


data PairedConcealAction {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ)
    {A A′ : Ty (Δᵉ Cᴸ)} {B B′ : Ty (Δᵉ Cᴿ)}
    (c : Conv↓ (Δᵉ Cᴸ) A A′) (c′ : Conv↓ (Δᵉ Cᴿ) B B′) :
    Cᴸ ⊑ᶜ Cᴿ → Set where

  paired-conceal-action : ∀ {W′ Xᴸ Xᴿ Rᴸ Rᴿ}
    → (plan : SourceRebasePlan W′ Xᴸ Xᴿ)
    → rebaseSource plan ≡ W
    → lookupStore (Σᵉ Cᴸ) Xᴸ
        ⊑ᵀ⟨ rebaseSource plan ⟩ lookupStore (Σᵉ Cᴿ) Xᴿ
    → (c⊢ : Σᵉ Cᴸ ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
    → (c′⊢ : Σᵉ Cᴿ ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
    → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
    → concealGeneratorPosition c⊢ ≢ generator-absent
    → PairedConcealAction W c c′ W′


infix 4 _⊢ᴰ_⊑_∶_

data _⊢ᴰ_⊑_∶_ {Cᴸ Cᴿ : Ctx} (W : Cᴸ ⊑ᶜ Cᴿ) :
    Term (Δᵉ Cᴸ) → Term (Δᵉ Cᴿ)
    → {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
    → A ⊑ᵀ⟨ W ⟩ B → Set where

  var⊑varᴰ : ∀ {x A B} {p : A ⊑ᵀ⟨ W ⟩ B}
    → Cᴸ ∋ᵗ x ⦂ A
    → Cᴿ ∋ᵗ x ⦂ B
    → W ⊢ᴰ ` x ⊑ ` x ∶ p

  lambda⊑lambdaᴰ : ∀ {M M′ A A′ B B′}
      {pA : A ⊑ᵀ⟨ W ⟩ A′} {pB : B ⊑ᵀ⟨ W ⟩ B′}
    → bind-termᶜ W pA ⊢ᴰ M ⊑ M′ ∶ pB
    → W ⊢ᴰ ƛ M ⊑ ƛ M′ ∶ ⇒⊑⇒ pA pB

  app⊑appᴰ : ∀ {L L′ M M′ A A′ B B′}
      {pA : A ⊑ᵀ⟨ W ⟩ A′} {pB : B ⊑ᵀ⟨ W ⟩ B′}
    → W ⊢ᴰ L ⊑ L′ ∶ ⇒⊑⇒ pA pB
    → W ⊢ᴰ M ⊑ M′ ∶ pA
    → W ⊢ᴰ L · M ⊑ L′ · M′ ∶ pB

  all⊑allᴰ : ∀ {V V′ A B}
      {p : A ⊑ᵀ⟨ liftBothᶜ X⊑X W ⟩ B}
    → Value V
    → Value V′
    → liftBothᶜ X⊑X W ⊢ᴰ V ⊑ V′ ∶ p
    → (q : (`∀ A) ⊑ᵀ⟨ W ⟩ (`∀ B))
    → W ⊢ᴰ Λ V ⊑ Λ V′ ∶ q

  all⊑ᴰ : ∀ {V M A B}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → (plan : SourceFreshBehindPlan W)
    → {p : A ⊑ᵀ⟨ insertSourceFreshBehind plan ⟩ B}
    → Value V
    → Cᴿ ⊢ M ⦂ B
    → insertSourceFreshBehind plan ⊢ᴰ V ⊑ M ∶ p
    → (q : (`∀ A) ⊑ᵀ⟨ W ⟩ B)
    → W ⊢ᴰ Λ V ⊑ M ∶ q

  type-app⊑type-appᴰ : ∀ {M M′ D D′ A A′}
    → (p∀ : (`∀ D) ⊑ᵀ⟨ W ⟩ (`∀ D′))
    → W ⊢ᴰ M ⊑ M′ ∶ p∀
    → (q : A ⊑ᵀ⟨ W ⟩ A′)
    → (r : (D [ A ]ᵗ) ⊑ᵀ⟨ W ⟩ (D′ [ A′ ]ᵗ))
    → W ⊢ᴰ M ⦂∀ D [ A ] ⊑ M′ ⦂∀ D′ [ A′ ] ∶ r

  type-app⊑ᴰ : ∀ {M M′ D A B}
    → (p∀ : (`∀ D) ⊑ᵀ⟨ W ⟩ B)
    → W ⊢ᴰ M ⊑ M′ ∶ p∀
    → (q : A ⊑ᵀ⟨ W ⟩ ★)
    → (r : (D [ A ]ᵗ) ⊑ᵀ⟨ W ⟩ B)
    → W ⊢ᴰ M ⦂∀ D [ A ] ⊑ M′ ∶ r

  constant⊑constantᴰ : ∀ (kappa : Const)
    → (p : constTy kappa ⊑ᵀ⟨ W ⟩ constTy kappa)
    → W ⊢ᴰ $ kappa ⊑ $ kappa ∶ p

  primitive⊑primitiveᴰ : ∀ {L L′ M M′} (op : Prim)
      {p q : primArgTy op ⊑ᵀ⟨ W ⟩ primArgTy op}
    → W ⊢ᴰ L ⊑ L′ ∶ p
    → W ⊢ᴰ M ⊑ M′ ∶ q
    → (r : primResultTy op ⊑ᵀ⟨ W ⟩ primResultTy op)
    → W ⊢ᴰ L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′ ∶ r

  blame⊑ᴰ : ∀ {M′ A B}
    → Cᴿ ⊢ M′ ⦂ B
    → (p : A ⊑ᵀ⟨ W ⟩ B)
    → W ⊢ᴰ blame ⊑ M′ ∶ p

  cast⊑castᴰ : ∀ {M M′ A A′ B B′}
      {p : A ⊑ᵀ⟨ W ⟩ A′}
      {ν : Env∼ (Δᵉ Cᴸ)} {ν′ : Env∼ (Δᵉ Cᴿ)}
    → (c : ν ⊢ A ∼ B)
    → (c′ : ν′ ⊢ A′ ∼ B′)
    → W ⊢ᴰ M ⊑ M′ ∶ p
    → (q : B ⊑ᵀ⟨ W ⟩ B′)
    → W ⊢ᴰ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ∶ q

  cast⊑ᴰ : ∀ {M M′ A A′ B} {p : A ⊑ᵀ⟨ W ⟩ B}
      {ν : Env∼ (Δᵉ Cᴸ)}
    → (c : ν ⊢ A ∼ A′)
    → W ⊢ᴰ M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ W ⟩ B)
    → W ⊢ᴰ M ⟨ c ⟩ ⊑ M′ ∶ q

  ⊑castᴰ : ∀ {M M′ A B B′} {p : A ⊑ᵀ⟨ W ⟩ B}
      {ν′ : Env∼ (Δᵉ Cᴿ)}
    → (c′ : ν′ ⊢ B ∼ B′)
    → W ⊢ᴰ M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ W ⟩ B′)
    → W ⊢ᴰ M ⊑ M′ ⟨ c′ ⟩ ∶ q

  target-revealᴰ : ∀ {M M′ A B B′}
      {p : A ⊑ᵀ⟨ W ⟩ B} {c′ : Conv↑ (Δᵉ Cᴿ) B B′}
    → TargetRevealAction W c′
    → W ⊢ᴰ M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ W ⟩ B′)
    → W ⊢ᴰ M ⊑ M′ ↑ c′ ∶ q

  target-concealᴰ : ∀ {M M′ A B B′}
      {p : A ⊑ᵀ⟨ W ⟩ B} {c′ : Conv↓ (Δᵉ Cᴿ) B B′}
    → TargetConcealAction W c′
    → W ⊢ᴰ M ⊑ M′ ∶ p
    → (q : A ⊑ᵀ⟨ W ⟩ B′)
    → W ⊢ᴰ M ⊑ M′ ↓ c′ ∶ q

  source-revealᴰ : ∀ {W′ : Cᴸ ⊑ᶜ Cᴿ}
      {M M′ A A′ B}
      {c : Conv↑ (Δᵉ Cᴸ) A A′}
    → SourceRevealAction W c W′
    → {p : A ⊑ᵀ⟨ W′ ⟩ B}
    → W′ ⊢ᴰ M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ W ⟩ B)
    → W ⊢ᴰ M ↑ c ⊑ M′ ∶ q

  source-concealᴰ : ∀ {M M′ A A′ B}
      {p : A ⊑ᵀ⟨ W ⟩ B} {c : Conv↓ (Δᵉ Cᴸ) A A′}
    → SourceConcealAction W c
    → W ⊢ᴰ M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ W ⟩ B)
    → W ⊢ᴰ M ↓ c ⊑ M′ ∶ q

  paired-revealᴰ : ∀ {W′ : Cᴸ ⊑ᶜ Cᴿ}
      {M M′ A A′ B B′}
      {c : Conv↑ (Δᵉ Cᴸ) A A′}
      {c′ : Conv↑ (Δᵉ Cᴿ) B B′}
    → PairedRevealAction W c c′ W′
    → {p : A ⊑ᵀ⟨ W′ ⟩ B}
    → W′ ⊢ᴰ M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ W ⟩ B′)
    → W ⊢ᴰ M ↑ c ⊑ M′ ↑ c′ ∶ q

  paired-concealᴰ : ∀ {W′ : Cᴸ ⊑ᶜ Cᴿ}
      {M M′ A A′ B B′}
      {c : Conv↓ (Δᵉ Cᴸ) A A′}
      {c′ : Conv↓ (Δᵉ Cᴿ) B B′}
      {p : A ⊑ᵀ⟨ W′ ⟩ B}
    → PairedConcealAction W c c′ W′
    → W′ ⊢ᴰ M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵀ⟨ W ⟩ B′)
    → W ⊢ᴰ M ↓ c ⊑ M′ ↓ c′ ∶ q
