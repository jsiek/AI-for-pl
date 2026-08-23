module proof.LR-narrow.RevealFrames where

-- File Charter:
--   * Instantiates the abstract evaluation frames of
--     proof.LR-narrow.FramePhases with reveal (`_↑_`) and conceal
--     (`_↓_`) conversions, whose operand evaluates first and whose
--     conversion transports along store changes by renaming.

open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)

open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (Conv↑; Conv↓; unseal; seal; _↦↑_; _↦↓_; `∀↑_; `∀↓_; id↑; id↓;
   rename↑; rename↓)
open import Reduction
import Eval as E
open import proof.LR-narrow.FramePhases

------------------------------------------------------------------------
-- Reveal frames
------------------------------------------------------------------------

record RevealFrm (Δ : TyCtx) : Set where
  constructor reveal-frm
  field
    {source target} : Ty Δ
    conv : Conv↑ Δ source target

reveal-final-none : ∀ {Δ} {M : Term Δ} {A B : Ty Δ} (c : Conv↑ Δ A B)
  → M ≢ blame
  → E.value? M ≡ nothing
  → E.reveal-final? M c ≡ nothing
reveal-final-none {M = blame} c M≢blame value-eq = ⊥-elim (M≢blame refl)
  where open import Data.Empty using (⊥-elim)
reveal-final-none {M = ` x} (unseal X R) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = ` x} (c ↦↑ d) M≢blame value-eq = refl
reveal-final-none {M = ` x} (`∀↑ c) M≢blame value-eq = refl
reveal-final-none {M = ` x} (id↑ A) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = ƛ N} c M≢blame ()
reveal-final-none {M = L · M} (unseal X R) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = L · M} (c ↦↑ d) M≢blame value-eq = refl
reveal-final-none {M = L · M} (`∀↑ c) M≢blame value-eq = refl
reveal-final-none {M = L · M} (id↑ A) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = Λ N} (unseal X R) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = Λ N} (c ↦↑ d) M≢blame value-eq = refl
reveal-final-none {M = Λ N} (`∀↑ c) M≢blame value-eq = refl
reveal-final-none {M = Λ N} (id↑ A) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = L ⦂∀ B [ A ]} (unseal X R) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = L ⦂∀ B [ A ]} (c ↦↑ d) M≢blame value-eq = refl
reveal-final-none {M = L ⦂∀ B [ A ]} (`∀↑ c) M≢blame value-eq = refl
reveal-final-none {M = L ⦂∀ B [ A ]} (id↑ A′) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = $ κ} c M≢blame ()
reveal-final-none {M = L ⊕[ op ] M} (unseal X R) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = L ⊕[ op ] M} (c ↦↑ d) M≢blame value-eq = refl
reveal-final-none {M = L ⊕[ op ] M} (`∀↑ c) M≢blame value-eq = refl
reveal-final-none {M = L ⊕[ op ] M} (id↑ A) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = M ⟨ d ⟩} (unseal X R) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = M ⟨ d ⟩} (c ↦↑ d′) M≢blame value-eq = refl
reveal-final-none {M = M ⟨ d ⟩} (`∀↑ c) M≢blame value-eq = refl
reveal-final-none {M = M ⟨ d ⟩} (id↑ A) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = M ↑ d} (unseal X R) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = M ↑ d} (c ↦↑ d′) M≢blame value-eq = refl
reveal-final-none {M = M ↑ d} (`∀↑ c) M≢blame value-eq = refl
reveal-final-none {M = M ↑ d} (id↑ A) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = M ↓ d} (unseal X R) M≢blame value-eq
    rewrite value-eq = refl
reveal-final-none {M = M ↓ d} (c ↦↑ d′) M≢blame value-eq = refl
reveal-final-none {M = M ↓ d} (`∀↑ c) M≢blame value-eq = refl
reveal-final-none {M = M ↓ d} (id↑ A) M≢blame value-eq
    rewrite value-eq = refl

revealFrame : Frame
revealFrame = record
  { Frm = RevealFrm
  ; plug = λ f M → M ↑ RevealFrm.conv f
  ; transport = λ χ f →
      reveal-frm (rename↑ (λ X → χ ▷ᵛ X) (RevealFrm.conv f))
  ; plug-step = λ f step → ξ-reveal step refl
  ; plug-step? = λ { f {Σ} {χ} {M} {N} {step} step-eq →
      step-question {Σ = Σ} {M = M} {χ = χ} {N = N} {step = step}
        {c = RevealFrm.conv f} step-eq }
  ; plug-stuck = λ { f {Σ} {M} step-eq value-eq M≢blame →
      stuck {Σ = Σ} {M = M} {c = RevealFrm.conv f}
        step-eq value-eq M≢blame }
  ; plug-nonvalue = λ { f value-eq →
      nonvalue {c = RevealFrm.conv f} value-eq }
  ; plug-not-blame = λ f M ()
  ; plug-blame = λ f → blame-reveal
  ; plug-blame-step? = λ f → refl
  }
  where
  step-question : ∀ {Δ Δ′} {Σ : TyStore Δ} {M : Term Δ}
      {χ : StoreChange Δ Δ′} {N : Term Δ′} {step : M —→[ χ ] N}
      {A B : Ty Δ} {c : Conv↑ Δ A B}
    → E.step? Σ M ≡ just (E.step-result χ N step)
    → E.step? Σ (M ↑ c) ≡
        just (E.step-result χ (N ↑ rename↑ (λ X → χ ▷ᵛ X) c)
          (ξ-reveal step refl))
  step-question step-eq rewrite step-eq = refl

  stuck : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ} {A B : Ty Δ}
      {c : Conv↑ Δ A B}
    → E.step? Σ M ≡ nothing
    → E.value? M ≡ nothing
    → M ≢ blame
    → E.step? Σ (M ↑ c) ≡ nothing
  stuck {c = c} step-eq value-eq M≢blame rewrite step-eq =
    reveal-final-none c M≢blame value-eq

  nonvalue : ∀ {Δ} {M : Term Δ} {A B : Ty Δ} {c : Conv↑ Δ A B}
    → E.value? M ≡ nothing
    → E.value? (M ↑ c) ≡ nothing
  nonvalue value-eq rewrite value-eq = refl

------------------------------------------------------------------------
-- Conceal frames
------------------------------------------------------------------------

record ConcealFrm (Δ : TyCtx) : Set where
  constructor conceal-frm
  field
    {source target} : Ty Δ
    conv : Conv↓ Δ source target

conceal-final-none : ∀ {Δ} {M : Term Δ} {A B : Ty Δ}
    (c : Conv↓ Δ A B)
  → M ≢ blame
  → E.value? M ≡ nothing
  → E.conceal-final? M c ≡ nothing
conceal-final-none {M = blame} c M≢blame value-eq = ⊥-elim (M≢blame refl)
  where open import Data.Empty using (⊥-elim)
conceal-final-none {M = ` x} (seal X R) M≢blame value-eq = refl
conceal-final-none {M = ` x} (c ↦↓ d) M≢blame value-eq = refl
conceal-final-none {M = ` x} (`∀↓ c) M≢blame value-eq = refl
conceal-final-none {M = ` x} (id↓ A) M≢blame value-eq
    rewrite value-eq = refl
conceal-final-none {M = ƛ N} c M≢blame ()
conceal-final-none {M = L · M} (seal X R) M≢blame value-eq = refl
conceal-final-none {M = L · M} (c ↦↓ d) M≢blame value-eq = refl
conceal-final-none {M = L · M} (`∀↓ c) M≢blame value-eq = refl
conceal-final-none {M = L · M} (id↓ A) M≢blame value-eq
    rewrite value-eq = refl
conceal-final-none {M = Λ N} (seal X R) M≢blame value-eq = refl
conceal-final-none {M = Λ N} (c ↦↓ d) M≢blame value-eq = refl
conceal-final-none {M = Λ N} (`∀↓ c) M≢blame value-eq = refl
conceal-final-none {M = Λ N} (id↓ A) M≢blame value-eq
    rewrite value-eq = refl
conceal-final-none {M = L ⦂∀ B [ A ]} (seal X R) M≢blame value-eq = refl
conceal-final-none {M = L ⦂∀ B [ A ]} (c ↦↓ d) M≢blame value-eq = refl
conceal-final-none {M = L ⦂∀ B [ A ]} (`∀↓ c) M≢blame value-eq = refl
conceal-final-none {M = L ⦂∀ B [ A ]} (id↓ A′) M≢blame value-eq
    rewrite value-eq = refl
conceal-final-none {M = $ κ} c M≢blame ()
conceal-final-none {M = L ⊕[ op ] M} (seal X R) M≢blame value-eq = refl
conceal-final-none {M = L ⊕[ op ] M} (c ↦↓ d) M≢blame value-eq = refl
conceal-final-none {M = L ⊕[ op ] M} (`∀↓ c) M≢blame value-eq = refl
conceal-final-none {M = L ⊕[ op ] M} (id↓ A) M≢blame value-eq
    rewrite value-eq = refl
conceal-final-none {M = M ⟨ d ⟩} (seal X R) M≢blame value-eq = refl
conceal-final-none {M = M ⟨ d ⟩} (c ↦↓ d′) M≢blame value-eq = refl
conceal-final-none {M = M ⟨ d ⟩} (`∀↓ c) M≢blame value-eq = refl
conceal-final-none {M = M ⟨ d ⟩} (id↓ A) M≢blame value-eq
    rewrite value-eq = refl
conceal-final-none {M = M ↑ d} (seal X R) M≢blame value-eq = refl
conceal-final-none {M = M ↑ d} (c ↦↓ d′) M≢blame value-eq = refl
conceal-final-none {M = M ↑ d} (`∀↓ c) M≢blame value-eq = refl
conceal-final-none {M = M ↑ d} (id↓ A) M≢blame value-eq
    rewrite value-eq = refl
conceal-final-none {M = M ↓ d} (seal X R) M≢blame value-eq = refl
conceal-final-none {M = M ↓ d} (c ↦↓ d′) M≢blame value-eq = refl
conceal-final-none {M = M ↓ d} (`∀↓ c) M≢blame value-eq = refl
conceal-final-none {M = M ↓ d} (id↓ A) M≢blame value-eq
    rewrite value-eq = refl

concealFrame : Frame
concealFrame = record
  { Frm = ConcealFrm
  ; plug = λ f M → M ↓ ConcealFrm.conv f
  ; transport = λ χ f →
      conceal-frm (rename↓ (λ X → χ ▷ᵛ X) (ConcealFrm.conv f))
  ; plug-step = λ f step → ξ-conceal step refl
  ; plug-step? = λ { f {Σ} {χ} {M} {N} {step} step-eq →
      step-question {Σ = Σ} {M = M} {χ = χ} {N = N} {step = step}
        {c = ConcealFrm.conv f} step-eq }
  ; plug-stuck = λ { f {Σ} {M} step-eq value-eq M≢blame →
      stuck {Σ = Σ} {M = M} {c = ConcealFrm.conv f}
        step-eq value-eq M≢blame }
  ; plug-nonvalue = λ { f value-eq →
      nonvalue {c = ConcealFrm.conv f} value-eq }
  ; plug-not-blame = λ f M ()
  ; plug-blame = λ f → blame-conceal
  ; plug-blame-step? = λ f → refl
  }
  where
  step-question : ∀ {Δ Δ′} {Σ : TyStore Δ} {M : Term Δ}
      {χ : StoreChange Δ Δ′} {N : Term Δ′} {step : M —→[ χ ] N}
      {A B : Ty Δ} {c : Conv↓ Δ A B}
    → E.step? Σ M ≡ just (E.step-result χ N step)
    → E.step? Σ (M ↓ c) ≡
        just (E.step-result χ (N ↓ rename↓ (λ X → χ ▷ᵛ X) c)
          (ξ-conceal step refl))
  step-question step-eq rewrite step-eq = refl

  stuck : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ} {A B : Ty Δ}
      {c : Conv↓ Δ A B}
    → E.step? Σ M ≡ nothing
    → E.value? M ≡ nothing
    → M ≢ blame
    → E.step? Σ (M ↓ c) ≡ nothing
  stuck {c = c} step-eq value-eq M≢blame rewrite step-eq =
    conceal-final-none c M≢blame value-eq

  nonvalue : ∀ {Δ} {M : Term Δ} {A B : Ty Δ} {c : Conv↓ Δ A B}
    → E.value? M ≡ nothing
    → E.value? (M ↓ c) ≡ nothing
  nonvalue value-eq rewrite value-eq = refl
