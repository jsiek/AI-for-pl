module proof.NuProgress where

-- File Charter:
--   * Canonical-form lemmas and progress for Nu GTSF terms typed in runtime
--     telescopes.
--   * Produces values, blame crashes, or one telescope-threaded reduction step.
--   * Uses the redesigned `NuTerms`/`NuReduction` formulation directly; the
--     seal-weakening boundary is supplied by `proof.NuTermProperties`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (sym)
  renaming (subst to substEq)
open import Relation.Nullary using (yes; no)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction
open import proof.NuTermProperties using (typing-insert-seal)

------------------------------------------------------------------------
-- Runtime telescopes contain no term variables
------------------------------------------------------------------------

runtime-no-lookup :
  ∀ {Γ x A} →
  RuntimeTelescope Γ →
  Γ ∋ˣ x ⦂ A →
  ⊥
runtime-no-lookup rt∅ ()
runtime-no-lookup (rtSeal rt hA) (Sˣ-seal h) =
  runtime-no-lookup rt h

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress {Γ : Telescope} (M : Term) : Set where
  done : Value M → Progress M
  step :
    ∀ {Γ′ : Telescope}{N : Term} →
    RuntimeTelescope Γ′ →
    Γ ∣ M —→ Γ′ ∣ N →
    Progress M
  crash :
    M ≡ blame →
    Progress M

------------------------------------------------------------------------
-- Canonical forms for runtime-closed values
------------------------------------------------------------------------

data FunView (V : Term) : Set where
  fv-ƛ :
    ∀ {N : Term} →
    V ≡ ƛ N →
    FunView V

  fv-↦ :
    ∀ {W : Term}{c d : Coercion} →
    Value W →
    V ≡ W ⟨ c ↦ d ⟩ →
    FunView V

canonical-⇒ :
  ∀ {Γ : Telescope}{V : Term}{A B : Ty} →
  Value V →
  Γ ⊢ V ⦂ (A ⇒ B) →
  FunView V
canonical-⇒ (ƛ N) (⊢ƛ hA hN) = fv-ƛ refl
canonical-⇒ (Λ vV) ()
canonical-⇒ ($ (κℕ n)) ()
canonical-⇒ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (c ↦ d))
    (⊢⟨⟩ (cast-fun c⊢ d⊢) hW) =
  fv-↦ vW refl
canonical-⇒ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (gen c)) (⊢⟨⟩ () hW)

data AllView (V : Term) : Set where
  av-Λ :
    ∀ {W : Term} →
    V ≡ Λ W →
    AllView V

  av-∀ :
    ∀ {W : Term}{c : Coercion} →
    Value W →
    V ≡ W ⟨ `∀ c ⟩ →
    AllView V

  av-gen :
    ∀ {W : Term}{c : Coercion} →
    Value W →
    V ≡ W ⟨ gen c ⟩ →
    AllView V

canonical-∀ :
  ∀ {Γ : Telescope}{V : Term}{A : Ty} →
  Value V →
  Γ ⊢ V ⦂ (`∀ A) →
  AllView V
canonical-∀ (ƛ N) ()
canonical-∀ (Λ vV) (⊢Λ _ hV) = av-Λ refl
canonical-∀ ($ (κℕ n)) ()
canonical-∀ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ (cast-all c⊢) hW) =
  av-∀ vW refl
canonical-∀ (_⟨_⟩ {V = W} vW (gen c))
    (⊢⟨⟩ (cast-gen hA hB occ c⊢) hW) =
  av-gen vW refl

data NatView (V : Term) : Set where
  nv-const :
    ∀ {n : ℕ} →
    V ≡ $ (κℕ n) →
    NatView V

canonical-ℕ :
  ∀ {Γ : Telescope}{V : Term} →
  Value V →
  Γ ⊢ V ⦂ (‵ `ℕ) →
  NatView V
canonical-ℕ (ƛ N) ()
canonical-ℕ (Λ vV) ()
canonical-ℕ ($ (κℕ n)) (⊢$ (κℕ .n)) = nv-const refl
canonical-ℕ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (gen c)) (⊢⟨⟩ () hW)

data StarView (V : Term) : Set where
  sv-tag :
    ∀ {W : Term}{G : Ty} →
    Value W →
    V ≡ W ⟨ G ! ⟩ →
    StarView V

canonical-★ :
  ∀ {Γ : Telescope}{V : Term} →
  Value V →
  Γ ⊢ V ⦂ ★ →
  StarView V
canonical-★ (ƛ N) ()
canonical-★ (Λ vV) ()
canonical-★ ($ (κℕ n)) ()
canonical-★ (_⟨_⟩ {V = W} vW (G !))
    (⊢⟨⟩ (cast-tag hG gG ok) hW) =
  sv-tag vW refl
canonical-★ (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ () hW)
canonical-★ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-★ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-★ (_⟨_⟩ {V = W} vW (gen c)) (⊢⟨⟩ () hW)

data SealView {α : SealVar} (V : Term) : Set where
  sv-seal :
    ∀ {W : Term}{A : Ty} →
    Value W →
    V ≡ W ⟨ seal A α ⟩ →
    SealView {α = α} V

canonical-α :
  ∀ {Γ : Telescope}{V : Term}{α : SealVar} →
  Value V →
  Γ ⊢ V ⦂ (`α α) →
  SealView {α = α} V
canonical-α (ƛ N) ()
canonical-α (Λ vV) ()
canonical-α ($ (κℕ n)) ()
canonical-α (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-α (_⟨_⟩ {V = W} vW (seal A α))
    (⊢⟨⟩ (cast-seal hA use hα) hW) =
  sv-seal vW refl
canonical-α (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-α (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-α (_⟨_⟩ {V = W} vW (gen c)) (⊢⟨⟩ () hW)

------------------------------------------------------------------------
-- Progress helpers
------------------------------------------------------------------------

untag-progress :
  ∀ {Γ : Telescope}{M : Term}{G : Ty} →
  RuntimeTelescope Γ →
  Value M →
  Γ ⊢ M ⦂ ★ →
  Progress {Γ = Γ} (M ⟨ G ？ ⟩)
untag-progress {G = G} rt vM M⊢ with canonical-★ vM M⊢
untag-progress {G = G} rt vM M⊢
    | sv-tag {G = H} vW refl with H ≟Ty G
untag-progress {G = G} rt vM M⊢
    | sv-tag {G = .G} vW refl | yes refl =
  step rt (pure-step (tag-untag-ok vW refl))
untag-progress {G = G} rt vM M⊢
    | sv-tag {G = H} vW refl | no H≢G =
  step rt (pure-step (tag-untag-bad vW H≢G))

unseal-progress :
  ∀ {Γ : Telescope}{M : Term}{α : SealVar}{A : Ty} →
  RuntimeTelescope Γ →
  Value M →
  Γ ⊢ M ⦂ (`α α) →
  Progress {Γ = Γ} (M ⟨ unseal α A ⟩)
unseal-progress rt vM M⊢ with canonical-α vM M⊢
unseal-progress rt vM M⊢ | sv-seal vW refl =
  step rt (pure-step (seal-unseal vW refl))

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress :
  ∀ {Γ : Telescope}{M : Term}{A : Ty} →
  RuntimeTelescope Γ →
  Γ ⊢ M ⦂ A →
  Progress {Γ = Γ} M
progress rt (⊢` h) = ⊥-elim (runtime-no-lookup rt h)
progress rt (⊢ƛ hA hM) = done (ƛ _)
progress rt (⊢· {L = L} {M = M} L⊢ M⊢) with progress rt L⊢
progress rt (⊢· {L = L} {M = M} L⊢ M⊢) | step rt′ L→L′ =
  step rt′ (ξ-·₁ (stepExt L→L′) L→L′ refl)
progress rt (⊢· {L = L} {M = M} L⊢ M⊢) | crash refl =
  step rt (pure-step (blame-·₁ refl))
progress rt (⊢· {L = L} {M = M} L⊢ M⊢) | done vL
    with progress rt M⊢
progress rt (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | step rt′ M→M′ =
  step rt′ (ξ-·₂ vL (stepExt M→M′) M→M′ refl)
progress rt (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | crash refl =
  step rt (pure-step (blame-·₂ vL refl))
progress rt (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    with canonical-⇒ vL L⊢
progress rt (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    | fv-ƛ refl =
  step rt (pure-step (β vM))
progress rt (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    | fv-↦ vW refl =
  step rt (pure-step (β-↦ vW vM))
progress rt (⊢Λ vM hM) = done (Λ vM)
progress rt
    (⊢• {Γ⁻ = Γ⁻} {Γ⁺ = Γ⁺} {L = L} {B = B} {L↑ = L↑}
      i L⊢ hB eqL eqT)
    with progress rt L↑⊢
  where
    L↑⊢ :
      Γ⁺ ⊢ L↑ ⦂ rename idᵗ (insertRenˢ i) (`∀ B)
    L↑⊢ =
      substEq
        (λ N → Γ⁺ ⊢ N ⦂ rename idᵗ (insertRenˢ i) (`∀ B))
        (sym eqL)
        (typing-insert-seal i L⊢)
progress rt
    (⊢• {Γ⁻ = Γ⁻} {Γ⁺ = Γ⁺} {L = L} {B = B} {L↑ = L↑}
      i L⊢ hB eqL eqT)
    | step rt′ L→L′ =
  step rt′ (ξ-·α (stepExt L→L′) L→L′ refl)
progress rt
    (⊢• {Γ⁻ = Γ⁻} {Γ⁺ = Γ⁺} {L = L} {B = B} {L↑ = L↑}
      i L⊢ hB eqL eqT)
    | crash refl =
  step rt (pure-step (blame-·α refl))
progress rt
    (⊢• {Γ⁻ = Γ⁻} {Γ⁺ = Γ⁺} {L = L} {B = B} {L↑ = L↑}
      i L⊢ hB eqL eqT)
    | done vL with canonical-∀ vL L↑⊢
  where
    L↑⊢ :
      Γ⁺ ⊢ L↑ ⦂ rename idᵗ (insertRenˢ i) (`∀ B)
    L↑⊢ =
      substEq
        (λ N → Γ⁺ ⊢ N ⦂ rename idᵗ (insertRenˢ i) (`∀ B))
        (sym eqL)
        (typing-insert-seal i L⊢)
progress rt
    (⊢• {Γ⁻ = Γ⁻} {Γ⁺ = Γ⁺} {L = L} {B = B} {L↑ = L↑}
      i L⊢ hB eqL eqT)
    | done vL | av-Λ refl =
  step rt (pure-step β-Λ)
progress rt
    (⊢• {Γ⁻ = Γ⁻} {Γ⁺ = Γ⁺} {L = L} {B = B} {L↑ = L↑}
      i L⊢ hB eqL eqT)
    | done vL | av-∀ vW refl =
  step rt (pure-step (β-∀ vW))
progress rt
    (⊢• {Γ⁻ = Γ⁻} {Γ⁺ = Γ⁺} {L = L} {B = B} {L↑ = L↑}
      i L⊢ hB eqL eqT)
    | done vL | av-gen vW refl =
  step rt (pure-step (β-gen vW))
progress rt (⊢ν {A = A} hA N⊢) =
  step (rtSeal rt hA) ν-step
progress rt (⊢$ κ) = done ($ κ)
progress rt (⊢⊕ {L = L} {M = M} L⊢ op M⊢) with progress rt L⊢
progress rt (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | step rt′ L→L′ =
  step rt′ (ξ-⊕₁ (stepExt L→L′) L→L′ refl)
progress rt (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | crash refl =
  step rt (pure-step (blame-⊕₁ refl))
progress rt (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL
    with progress rt M⊢
progress rt (⊢⊕ {L = L} {M = M} L⊢ op M⊢)
    | done vL | step rt′ M→M′ =
  step rt′ (ξ-⊕₂ vL (stepExt M→M′) M→M′ refl)
progress rt (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL | crash refl =
  step rt (pure-step (blame-⊕₂ vL refl))
progress rt (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL | done vM
    with canonical-ℕ vL L⊢ | canonical-ℕ vM M⊢
progress rt (⊢⊕ {L = L} {M = M} L⊢ addℕ M⊢)
    | done vL | done vM | nv-const refl | nv-const refl =
  step rt (pure-step δ-⊕)
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) with progress rt M⊢
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | step rt′ M→M′ =
  step rt′ (ξ-⟨⟩ (stepExt M→M′) M→M′ refl)
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | crash refl =
  step rt (pure-step (blame-⟨⟩ refl))
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM with c⊢
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM | cast-id hA =
  step rt (pure-step (β-id vM))
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-seal hA use hα =
  done (vM ⟨ seal _ _ ⟩)
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-unseal hA use hα =
  unseal-progress rt vM M⊢
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-seq p⊢ q⊢ =
  step rt (pure-step (β-seq vM))
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢)
    | done vM | cast-tag hG gG ok =
  done (vM ⟨ _ ! ⟩)
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-untag hG gG ok =
  untag-progress rt vM M⊢
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-fun p⊢ q⊢ =
  done (vM ⟨ _ ↦ _ ⟩)
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM | cast-all d⊢ =
  done (vM ⟨ `∀ _ ⟩)
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢)
    | done vM | cast-inst hA hB occ d⊢ =
  step rt (pure-step (β-inst vM))
progress rt (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢)
    | done vM | cast-gen hA hB occ d⊢ =
  done (vM ⟨ gen _ ⟩)
progress rt (⊢blame hA) = crash refl
