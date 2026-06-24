module proof.Progress where

-- File Charter:
--   * Canonical-form lemmas and progress for closed GTSF terms.
--   * Produces values, blame crashes, or one store-threaded reduction step.
--   * Depends only on the definition-layer syntax, typing, coercions, and
--     reduction rules; preservation-specific proof infrastructure belongs in
--     sibling proof modules.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Relation.Nullary using (yes; no)

open import Types
open import Ctx
open import Coercions
open import Primitives
open import Terms
open import Reduction

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress {Σ : Store} (M : Term) : Set where
  done : Value M → Progress M
  step :
    ∀ {Σ′ : Store}{N : Term} →
    Σ ∣ M —→ Σ′ ∣ N →
    Progress M
  crash :
    M ≡ blame →
    Progress M

------------------------------------------------------------------------
-- Canonical forms for closed values
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
  ∀ {Δ : TyCtx}{Σ : Store}{V : Term}{A B : Ty} →
  Value V →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ (A ⇒ B) →
  FunView V
canonical-⇒ (ƛ N) (⊢ƛ hA hN) = fv-ƛ refl
canonical-⇒ (Λ vV) ()
canonical-⇒ ($ (κℕ n)) ()
canonical-⇒ (_⟨_⟩ {V = W} vW (G !)) (⊢up () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (seal A α)) (⊢up () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢up (cast-fun cwt dwt) hW) =
  fv-↦ vW refl
canonical-⇒ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢up () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (gen A c)) (⊢up () hW)

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
    ∀ {W : Term}{A : Ty}{c : Coercion} →
    Value W →
    V ≡ W ⟨ gen A c ⟩ →
    AllView V

canonical-∀ :
  ∀ {Δ : TyCtx}{Σ : Store}{V : Term}{A : Ty} →
  Value V →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ (`∀ A) →
  AllView V
canonical-∀ (ƛ N) ()
canonical-∀ (Λ vV) (⊢Λ _ hV) = av-Λ refl
canonical-∀ ($ (κℕ n)) ()
canonical-∀ (_⟨_⟩ {V = W} vW (G !)) (⊢up () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (seal A α)) (⊢up () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢up () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢up (cast-all cwt) hW) =
  av-∀ vW refl
canonical-∀ (_⟨_⟩ {V = W} vW (gen A c)) (⊢up (cast-gen _ _ _ cwt) hW) =
  av-gen vW refl

data NatView (V : Term) : Set where
  nv-const :
    ∀ {n : ℕ} →
    V ≡ $ (κℕ n) →
    NatView V

canonical-ℕ :
  ∀ {Δ : TyCtx}{Σ : Store}{V : Term} →
  Value V →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ (‵ `ℕ) →
  NatView V
canonical-ℕ (ƛ N) ()
canonical-ℕ (Λ vV) ()
canonical-ℕ ($ (κℕ n)) (⊢$ (κℕ .n)) = nv-const refl
canonical-ℕ (_⟨_⟩ {V = W} vW (G !)) (⊢up () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (seal A α)) (⊢up () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢up () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢up () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (gen A c)) (⊢up () hW)

data StarView (V : Term) : Set where
  sv-tag :
    ∀ {W : Term}{G : Ty} →
    Value W →
    V ≡ W ⟨ G ! ⟩ →
    StarView V

canonical-★ :
  ∀ {Δ : TyCtx}{Σ : Store}{V : Term} →
  Value V →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ ★ →
  StarView V
canonical-★ (ƛ N) ()
canonical-★ (Λ vV) ()
canonical-★ ($ (κℕ n)) ()
canonical-★ (_⟨_⟩ {V = W} vW (G !)) (⊢up (cast-tag _ _ _) hW) =
  sv-tag vW refl
canonical-★ (_⟨_⟩ {V = W} vW (seal A α)) (⊢up () hW)
canonical-★ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢up () hW)
canonical-★ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢up () hW)
canonical-★ (_⟨_⟩ {V = W} vW (gen A c)) (⊢up () hW)

data SealView {α : TyVar} (V : Term) : Set where
  sv-seal :
    ∀ {W : Term}{A : Ty} →
    Value W →
    V ≡ W ⟨ seal A α ⟩ →
    SealView {α = α} V

canonical-＇ :
  ∀ {Δ : TyCtx}{Σ : Store}{V : Term}{α : TyVar} →
  Value V →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ (＇ α) →
  SealView {α = α} V
canonical-＇ (ƛ N) ()
canonical-＇ (Λ vV) ()
canonical-＇ ($ (κℕ n)) ()
canonical-＇ (_⟨_⟩ {V = W} vW (G !)) (⊢up () hW)
canonical-＇ (_⟨_⟩ {V = W} vW (seal A α)) (⊢up (cast-seal _ _ _ _) hW) =
  sv-seal vW refl
canonical-＇ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢up () hW)
canonical-＇ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢up () hW)
canonical-＇ (_⟨_⟩ {V = W} vW (gen A c)) (⊢up () hW)

------------------------------------------------------------------------
-- Progress helpers
------------------------------------------------------------------------

untag-progress :
  ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{G : Ty} →
  Value M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ ★ →
  Progress {Σ = Σ} (M ⟨ G ？ ⟩)
untag-progress {G = G} vM M⊢ with canonical-★ vM M⊢
untag-progress {G = G} vM M⊢
    | sv-tag {G = H} vW refl with H ≟Ty G
untag-progress {G = G} vM M⊢
    | sv-tag {G = .G} vW refl | yes refl =
  step (pure-step (tag-untag-ok vW))
untag-progress {G = G} vM M⊢
    | sv-tag {G = H} vW refl | no H≢G =
  step (pure-step (tag-untag-bad vW H≢G))

unseal-progress :
  ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{α : TyVar}{A : Ty} →
  Value M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ (＇ α) →
  Progress {Σ = Σ} (M ⟨ unseal α A ⟩)
unseal-progress vM M⊢ with canonical-＇ vM M⊢
unseal-progress vM M⊢ | sv-seal vW refl =
  step (pure-step (seal-unseal vW))

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress :
  ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{A : Ty} →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  Progress {Σ = Σ} M
progress (⊢` ())
progress (⊢ƛ hA hM) = done (ƛ _)
progress (⊢· {L = L} {M = M} L⊢ M⊢) with progress L⊢
progress (⊢· {L = L} {M = M} L⊢ M⊢) | step L→L′ =
  step (ξ-·₁ L→L′)
progress (⊢· {L = L} {M = M} L⊢ M⊢) | crash refl =
  step (pure-step blame-·₁)
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL with progress M⊢
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | step M→M′ =
  step (ξ-·₂ vL M→M′)
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | crash refl =
  step (pure-step (blame-·₂ vL))
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    with canonical-⇒ vL L⊢
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    | fv-ƛ refl =
  step (pure-step (β vM))
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | done vM
    | fv-↦ vW refl =
  step (pure-step (β-↦ vW vM))
progress (⊢Λ vM hM) = done (Λ vM)
progress (⊢• {M = M} {B = B} {A = A} M⊢ hA) with progress M⊢
progress (⊢• {M = M} {B = B} {A = A} M⊢ hA) | step M→M′ =
  step (ξ-·α M→M′)
progress (⊢• {M = M} {B = B} {A = A} M⊢ hA) | crash refl =
  step (pure-step blame-·α)
progress (⊢• {M = M} {B = B} {A = A} M⊢ hA) | done vM
    with canonical-∀ vM M⊢
progress (⊢• {M = M} {B = B} {A = A} M⊢ hA) | done vM
    | av-Λ refl =
  step (β-Λ)
progress (⊢• {M = M} {B = B} {A = A} M⊢ hA) | done vM
    | av-∀ vW refl =
  step (β-∀ vW)
progress (⊢• {M = M} {B = B} {A = A} M⊢ hA) | done vM
    | av-gen vW refl =
  step (β-down-ν vW)
progress (⊢$ κ) = done ($ κ)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) with progress L⊢
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | step L→L′ =
  step (ξ-⊕₁ L→L′)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | crash refl =
  step (pure-step blame-⊕₁)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL with progress M⊢
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL | step M→M′ =
  step (ξ-⊕₂ vL M→M′)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL | crash refl =
  step (pure-step (blame-⊕₂ vL))
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL | done vM
    with canonical-ℕ vL L⊢ | canonical-ℕ vM M⊢
progress (⊢⊕ {L = L} {M = M} L⊢ addℕ M⊢)
    | done vL | done vM | nv-const refl | nv-const refl =
  step (pure-step δ-⊕)
progress (⊢up {M = M} {c = c} c⊢ M⊢) with progress M⊢
progress (⊢up {M = M} {c = c} c⊢ M⊢) | step M→M′ =
  step (ξ-⟨⟩ M→M′)
progress (⊢up {M = M} {c = c} c⊢ M⊢) | crash refl =
  step (pure-step blame-⟨⟩)
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM with c⊢
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM | cast-id hA _ =
  step (pure-step (β-id vM))
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-seal hA hα _ _ =
  done (vM ⟨ seal _ _ ⟩)
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-unseal hA hα _ _ =
  unseal-progress vM M⊢
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-seq p⊢ q⊢ =
  step (pure-step (β-seq vM))
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM | cast-tag hG gG _ =
  done (vM ⟨ _ ! ⟩)
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-untag hG gG _ =
  untag-progress vM M⊢
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-fun p⊢ q⊢ =
  done (vM ⟨ _ ↦ _ ⟩)
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM | cast-all cwt =
  done (vM ⟨ `∀ _ ⟩)
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM | cast-inst _ _ _ cwt =
  step (β-up-ν vM)
progress (⊢up {M = M} {c = c} c⊢ M⊢) | done vM | cast-gen _ _ _ cwt =
  done (vM ⟨ gen _ _ ⟩)
progress (⊢blame hA) = crash refl
