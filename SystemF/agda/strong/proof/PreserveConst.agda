module strong.proof.PreserveConst where

-- Strong System F v8 — preservation for `Const`.
--
--   k ⟨ c ⟩  -→  k        when `base c` is defined
--
-- `base` accepts only identity crossings over a ground terminator, and
-- a crossing relates a type to its `shiftAtᵗ` image — which, at a
-- GROUND type, is the type itself.  So the boundary's two endpoints are
-- equal and the literal already has the boundary's type.

open import Data.Nat using (ℕ)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.proof.Canonical using
  (GroundShape; ground-ℕ; ground-𝔹; shift-ground)

-- A ground type is its own shift: it has no variables to move.
ground-fixed : ∀ {A} X → GroundShape A → renameᵗ (shiftAtᵗ X) A ≡ A
ground-fixed X ground-ℕ = refl
ground-fixed X ground-𝔹 = refl

base-id : ∀ {A ι} → base (id A) ≡ just ι → GroundShape A
base-id {A = ` X} ()
base-id {A = `ℕ} refl = ground-ℕ
base-id {A = `𝔹} refl = ground-𝔹
base-id {A = A ⇒ B} ()
base-id {A = `∀ A} ()

-- A `base`-accepted conversion has EQUAL, ground endpoints.
base-typing : ∀ {Sg Δᵢ Δ c A B ι}
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → base c ≡ just ι
  → (A ≡ B) × GroundShape A
base-typing (conv-id wf) eq = refl , base-id eq
base-typing (conv-cons (conv-seal rep rd p) tl) ()
base-typing (conv-cons (conv-unseal rep rd p na) tl) ()
base-typing (conv-cons (conv-fun s t) tl) ()
base-typing (conv-cons (conv-all s) tl) ()
base-typing {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf p na) tl) eq
  with base-typing tl eq
base-typing {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf p na) tl) eq
  | teq , sh with shift-ground X A sh
base-typing {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf p na) tl) eq
  | teq , sh | shA = trans (sym (ground-fixed X shA)) teq , shA
base-typing {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p na) tl) eq
  with base-typing tl eq
base-typing {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p na) tl) eq
  | refl , sh rewrite ground-fixed X sh = refl , sh

preserve-Const : ∀ {Sg Δ Γ k c B ι}
  → Literal k → base c ≡ just ι
  → Sg ∣ Δ ∣ Γ ⊢ k ⟨ c ⟩ ⦂ B
  → Sg ∣ Δ ∣ Γ ⊢ k ⦂ B
preserve-Const lit base-eq (⊢⟨⟩ nf ⊢k conv) with base-typing conv base-eq
preserve-Const literal-$ base-eq (⊢⟨⟩ nf ⊢$ conv) | refl , sh = ⊢$
preserve-Const literal-# base-eq (⊢⟨⟩ nf ⊢# conv) | refl , sh = ⊢#
