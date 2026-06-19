module NuReduction where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Types
open import Coercions
open import NuTerms
open import Primitives

--------------------------------------------------------------------------------
-- One-step reduction
--------------------------------------------------------------------------------

infix 2 _—→_
data _—→_ : Term → Term → Set where

  δ-⊕ : ∀ {m n : ℕ} →
    -----------------------------------------------
    $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)  —→  $ (κℕ (m + n))

  β : ∀ {N V : Term}
    → Value V
    ---------------------
    → (ƛ N) · V —→ N [ V ]

  β-Λ : ∀ {α : SealVar} {V : Term}
    ------------------------
    → (Λ V) • α  —→ V [ α ]ᵀ

  β-id : ∀ {V}{A}
    → Value V
    -------------------
    → V ⟨ id A ⟩ —→  V

  β-seq : ∀ {V p q}
    → Value V
    ------------------------------
    → V ⟨ p ︔ q ⟩ —→ V ⟨ p ⟩ ⟨ q ⟩

  β-↦ : ∀ {V W p q}
    → Value V → Value W
    --------------------------------------------
    → V ⟨ p ↦ q ⟩ · W  —→  (V · (W ⟨ p ⟩)) ⟨ q ⟩

  β-∀ : ∀ {V : Term}{c : Coercion}{α : SealVar}
    → Value V
    ----------------------------------------
    → V ⟨ `∀ c ⟩ • α —→ (V • α) ⟨ c [ α ]ᵀᶜ ⟩

  β-gen : ∀ {V c α}
    → Value V
    --------------------------------------
    → V ⟨ gen c ⟩ • α —→ V ⟨ c [ α ]ᶜ ⟩

  β-inst : ∀ {V c}
    → Value V
    ----------------------------------------------
    → V ⟨ inst c ⟩ —→ ν ★ (((⇑ˢᵐ V) • zero) ⟨ c ⟩)

  tag-untag-ok : ∀ {V G H}
    → Value V → G ≡ H
    ------------------------------
    → V ⟨ G ! ⟩ ⟨ H ？ ⟩  —→  V

  tag-untag-bad : ∀ {V G H}
    → Value V → G ≢ H
    ----------------------------------------
    → V ⟨ G ! ⟩ ⟨ H ？ ⟩ —→  blame

  seal-unseal : ∀ {α β V A B}
    → Value V → α ≡ β
    ------------------------------------
    → V ⟨ seal A α ⟩ ⟨ unseal β B ⟩ —→ V

  blame-·₁ : ∀ {L M : Term} →
    L ≡ blame →
    (L · M) —→ blame

  blame-·₂ : ∀ {V M : Term} →
    Value V → M ≡ blame →
    (V · M) —→ blame

  blame-·α : ∀ {M : Term}{α : SealVar} →
    M ≡ blame →
    (M • α) —→ blame

  blame-⟨⟩ : ∀ {M : Term}{c : Coercion} →
    M ≡ blame →
    (M ⟨ c ⟩) —→ blame

  blame-⊕₁ : ∀ {L M : Term} {op : Prim} →
    L ≡ blame →
    (L ⊕[ op ] M) —→ blame

  blame-⊕₂ : ∀ {L M : Term} {op : Prim} →
    Value L → M ≡ blame →
    (L ⊕[ op ] M) —→ blame


--------------------------------------------------------------------------------
-- Telescope-threaded one-step reduction
--------------------------------------------------------------------------------

-- Runtime states are ordinary telescopes that contain only seal entries.  The
-- old `Store` is therefore represented as a predicate on the same telescope
-- object used by typing, rather than as a second structure that must be
-- injected into a telescope with a function call.
data RuntimeTelescope : Telescope → Set where
  rt∅ : RuntimeTelescope []

  rtSeal : ∀ {Γ A}
    → RuntimeTelescope Γ
    → WfTy Γ A
    → RuntimeTelescope (sealᵉ A ∷ Γ)

-- A single reduction step either preserves the telescope or allocates one fresh
-- head seal.  When allocation happens below an evaluation frame, the unchanged
-- parts of the frame must be raised over the new head seal.
data StepExt : Telescope → Telescope → Set where
  ext-refl : ∀ {Γ} →
    StepExt Γ Γ

  ext-seal : ∀ {Γ A} →
    StepExt Γ (sealᵉ A ∷ Γ)

weakenSeal : ∀ {Γ Γ′} → StepExt Γ Γ′ → SealVar → SealVar
weakenSeal ext-refl α = α
weakenSeal ext-seal α = suc α

weakenTerm : ∀ {Γ Γ′} → StepExt Γ Γ′ → Term → Term
weakenTerm ext-refl M = M
weakenTerm ext-seal M = ⇑ˢᵐ M

weakenCoercion : ∀ {Γ Γ′} → StepExt Γ Γ′ → Coercion → Coercion
weakenCoercion ext-refl c = c
weakenCoercion ext-seal c = ⇑ˢᶜ c

infix 2 _∣_—→_∣_
data _∣_—→_∣_ : Telescope → Term → Telescope → Term → Set where

  pure-step : ∀ {Γ M M′}
    → M —→ M′
    -----------------
    → Γ ∣ M —→ Γ ∣ M′

  ν-step : ∀ {Γ N A}
    -------------------------------------
    → Γ ∣ ν A N —→ sealᵉ A ∷ Γ ∣ N

  ξ-·₁ : ∀ {Γ Γ′ L M L′ M↑}
    → (ext : StepExt Γ Γ′)
    → Γ ∣ L —→ Γ′ ∣ L′
    → M↑ ≡ weakenTerm ext M
    → Γ ∣ (L · M) —→ Γ′ ∣ (L′ · M↑)

  ξ-·₂ : ∀ {Γ Γ′ V V↑ M M′}
    → Value V
    → (ext : StepExt Γ Γ′)
    → Γ ∣ M —→ Γ′ ∣ M′
    → V↑ ≡ weakenTerm ext V
    → Γ ∣ (V · M) —→ Γ′ ∣ (V↑ · M′)

  ξ-·α : ∀ {Γ Γ′ M M′ α α↑}
    → (ext : StepExt Γ Γ′)
    → Γ ∣ M —→ Γ′ ∣ M′
    → α↑ ≡ weakenSeal ext α
    → Γ ∣ (M • α) —→ Γ′ ∣ (M′ • α↑)

  ξ-⟨⟩ : ∀ {Γ Γ′ c c↑ M M′}
    → (ext : StepExt Γ Γ′)
    → Γ ∣ M —→ Γ′ ∣ M′
    → c↑ ≡ weakenCoercion ext c
    → Γ ∣ (M ⟨ c ⟩) —→ Γ′ ∣ (M′ ⟨ c↑ ⟩)

  ξ-⊕₁ : ∀ {Γ Γ′ L M L′ M↑ op}
    → (ext : StepExt Γ Γ′)
    → Γ ∣ L —→ Γ′ ∣ L′
    → M↑ ≡ weakenTerm ext M
    → Γ ∣ (L ⊕[ op ] M) —→ Γ′ ∣ (L′ ⊕[ op ] M↑)

  ξ-⊕₂ : ∀ {Γ Γ′ L L↑ M M′ op}
    → Value L
    → (ext : StepExt Γ Γ′)
    → Γ ∣ M —→ Γ′ ∣ M′
    → L↑ ≡ weakenTerm ext L
    → Γ ∣ (L ⊕[ op ] M) —→ Γ′ ∣ (L↑ ⊕[ op ] M′)

stepExt :
  ∀ {Γ Γ′ M M′} →
  Γ ∣ M —→ Γ′ ∣ M′ →
  StepExt Γ Γ′
stepExt (pure-step red) = ext-refl
stepExt ν-step = ext-seal
stepExt (ξ-·₁ ext red eq) = ext
stepExt (ξ-·₂ vV ext red eq) = ext
stepExt (ξ-·α ext red eq) = ext
stepExt (ξ-⟨⟩ ext red eq) = ext
stepExt (ξ-⊕₁ ext red eq) = ext
stepExt (ξ-⊕₂ vL ext red eq) = ext
