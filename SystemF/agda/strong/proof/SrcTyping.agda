module strong.proof.SrcTyping where

-- Strong System F v8 — `srcᶜ` reads a conversion's SOURCE type off its
-- syntax, and this module says it reads it correctly.
--
-- `instReveal` needs it: it is specified as
--
--     +X(c) ≡ +X(src c) ⨟ c[X:=S]
--
-- so the builder is applied to the source type that `srcᶜ` computed,
-- and the composition only typechecks if that really is the source.
--
-- `srcᶜ` is partial exactly where the syntax does not determine the
-- source — on a seal-headed conversion, whose source is a read-back —
-- and the two crossing cases are where the work is: a `hide` states
-- its types as a `shiftAtᵗ` rename, so reading back through it needs
-- `closeAt-shiftAt`, that closing over a slot undoes shifting past it.

open import Data.Nat using
  (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _<?_; _≤?_; _≟_; _∸_)
open import Data.Nat.Properties using (n≮n; ≤-refl; ≰⇒>; <⇒≤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction
open import strong.proof.Canonical using (conv-target)

------------------------------------------------------------------------
-- Closing a slot undoes shifting past it
------------------------------------------------------------------------

substᵗ-renameᵗ : ∀ σ ρ A
  → substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ X → σ (ρ X)) A
substᵗ-renameᵗ σ ρ (` X) = refl
substᵗ-renameᵗ σ ρ `ℕ = refl
substᵗ-renameᵗ σ ρ `𝔹 = refl
substᵗ-renameᵗ σ ρ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-renameᵗ σ ρ A) (substᵗ-renameᵗ σ ρ B)
substᵗ-renameᵗ σ ρ (`∀ A) =
  cong `∀ (trans (substᵗ-renameᵗ (extsᵗ σ) (extᵗ ρ) A)
                 (substᵗ-cong h A))
  where
  h : ∀ X → extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
  h zero = refl
  h (suc X) = refl

substᵗ-id : ∀ A → substᵗ `_ A ≡ A
substᵗ-id (` X) = refl
substᵗ-id `ℕ = refl
substᵗ-id `𝔹 = refl
substᵗ-id (A ⇒ B) = cong₂ _⇒_ (substᵗ-id A) (substᵗ-id B)
substᵗ-id (`∀ A) = cong `∀ (trans (substᵗ-cong h A) (substᵗ-id A))
  where
  h : ∀ X → extsᵗ `_ X ≡ ` X
  h zero = refl
  h (suc X) = refl

-- `shiftAtᵗ X` is the identity below the slot and `suc` at or above it
shiftAt-below : ∀ X Y → Y < X → shiftAtᵗ X Y ≡ Y
shiftAt-below (suc X) zero lt = refl
shiftAt-below (suc X) (suc Y) (s≤s lt) = cong suc (shiftAt-below X Y lt)

shiftAt-above : ∀ X Y → X ≤ Y → shiftAtᵗ X Y ≡ suc Y
shiftAt-above zero Y le = refl
shiftAt-above (suc X) (suc Y) (s≤s le) = cong suc (shiftAt-above X Y le)

closeEnv-shiftAt : ∀ X S Y → closeEnv X S (shiftAtᵗ X Y) ≡ ` Y
closeEnv-shiftAt X S Y with X ≤? Y
closeEnv-shiftAt X S Y | yes le
  rewrite shiftAt-above X Y le = above
  where
  above : closeEnv X S (suc Y) ≡ ` Y
  above with X ≟ suc Y
  above | yes refl = ⊥-elim (n≮n Y le)
  above | no _ with X <? suc Y
  above | no _ | yes _ = refl
  above | no _ | no ¬lt = ⊥-elim (¬lt (s≤s le))
closeEnv-shiftAt X S Y | no ¬le
  rewrite shiftAt-below X Y (≰⇒> ¬le) = below
  where
  below : closeEnv X S Y ≡ ` Y
  below with X ≟ Y
  below | yes refl = ⊥-elim (¬le ≤-refl)
  below | no _ with X <? Y
  below | no _ | yes lt = ⊥-elim (¬le (<⇒≤ lt))
  below | no _ | no _ = refl

closeAt-shiftAt : ∀ X S A → closeAt X S (renameᵗ (shiftAtᵗ X) A) ≡ A
closeAt-shiftAt X S A =
  trans (substᵗ-renameᵗ (closeEnv X S) (shiftAtᵗ X) A)
        (trans (substᵗ-cong (closeEnv-shiftAt X S) A) (substᵗ-id A))

------------------------------------------------------------------------
-- `srcᶜ` reads the source correctly
------------------------------------------------------------------------
-- The recursion follows the syntax, not the derivation's spine: a
-- crossing reads its tail's source and undoes its own reindexing, and
-- a `↦` or `all` reads the source out of a COMPONENT.  A seal-headed
-- conversion is where the syntax gives out, and there `srcᶜ` is
-- `nothing`, so the case is vacuous.

-- Stated as a GRAPH rather than with the equation as an input: where
-- `srcᶜ` answers at all, it answers with the source.  Taking the
-- equation as a hypothesis would bind its type's index before the
-- `with` introduces the tail's answer, and the two cannot be unified.
srcᶜ-sound : ∀ {Sg Δᵢ Δ c A B}
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ
  → (srcᶜ c ≡ just A) ⊎ (srcᶜ c ≡ nothing)
srcᶜ-sound (conv-id wf) = inj₁ refl
srcᶜ-sound (conv-cons (conv-seal rep rd p) tl) = inj₂ refl
srcᶜ-sound (conv-cons (conv-unseal rep rd p na) tl) = inj₁ refl

-- a `hide` shifts its target, so reading back closes over the slot
srcᶜ-sound {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf p na) tl)
  with srcᶜ c | srcᶜ-sound tl
srcᶜ-sound {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf p na) tl)
  | just B | inj₁ refl rewrite closeAt-shiftAt X (`ℕ) A = inj₁ refl
srcᶜ-sound {c = hide X α ∷ᶜ c} (conv-cons (conv-hide wf p na) tl)
  | just B | inj₂ ()
srcᶜ-sound {c = hide X α ∷ᶜ c} (conv-cons (conv-hide wf p na) tl)
  | nothing | inj₁ ()
srcᶜ-sound {c = hide X α ∷ᶜ c} (conv-cons (conv-hide wf p na) tl)
  | nothing | inj₂ refl = inj₂ refl

-- a `show` shifts its source, which is exactly what `srcᶜ` re-applies
srcᶜ-sound {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p na) tl)
  with srcᶜ c | srcᶜ-sound tl
srcᶜ-sound {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p na) tl)
  | just B | inj₁ refl = inj₁ refl
srcᶜ-sound {c = show X α ∷ᶜ c} (conv-cons (conv-show wf p na) tl)
  | just B | inj₂ ()
srcᶜ-sound {c = show X α ∷ᶜ c} (conv-cons (conv-show wf p na) tl)
  | nothing | inj₁ ()
srcᶜ-sound {c = show X α ∷ᶜ c} (conv-cons (conv-show wf p na) tl)
  | nothing | inj₂ refl = inj₂ refl

-- a `↦` reads the covariant component's source; the contravariant
-- one's TARGET is the domain, which `conv-target` supplies
srcᶜ-sound {c = (s ↦ t) ∷ᶜ c} (conv-cons (conv-fun ⊢s ⊢t) tl)
  with srcᶜ t | srcᶜ-sound ⊢t
srcᶜ-sound {c = (s ↦ t) ∷ᶜ c} (conv-cons (conv-fun ⊢s ⊢t) tl)
  | just B | inj₁ refl rewrite conv-target ⊢s = inj₁ refl
srcᶜ-sound {c = (s ↦ t) ∷ᶜ c} (conv-cons (conv-fun ⊢s ⊢t) tl)
  | just B | inj₂ ()
srcᶜ-sound {c = (s ↦ t) ∷ᶜ c} (conv-cons (conv-fun ⊢s ⊢t) tl)
  | nothing | inj₁ ()
srcᶜ-sound {c = (s ↦ t) ∷ᶜ c} (conv-cons (conv-fun ⊢s ⊢t) tl)
  | nothing | inj₂ refl = inj₂ refl

-- an `all` reads its component's source under the binder
srcᶜ-sound {c = all s ∷ᶜ c} (conv-cons (conv-all ⊢s) tl)
  with srcᶜ s | srcᶜ-sound ⊢s
srcᶜ-sound {c = all s ∷ᶜ c} (conv-cons (conv-all ⊢s) tl)
  | just B | inj₁ refl = inj₁ refl
srcᶜ-sound {c = all s ∷ᶜ c} (conv-cons (conv-all ⊢s) tl)
  | just B | inj₂ ()
srcᶜ-sound {c = all s ∷ᶜ c} (conv-cons (conv-all ⊢s) tl)
  | nothing | inj₁ ()
srcᶜ-sound {c = all s ∷ᶜ c} (conv-cons (conv-all ⊢s) tl)
  | nothing | inj₂ refl = inj₂ refl
