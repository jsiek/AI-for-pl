module proof.NuProgress where

-- File Charter:
--   * Canonical-form lemmas and progress for closed Nu GTSF terms.
--   * Produces values, blame crashes, or one store-threaded reduction step.
--   * Ports `proof.Progress` to the `NuTerms`/`NuReduction` formulation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero)
open import Data.Product as Product using (_,_)
open import Relation.Nullary using (yes; no)

open import Types
open import Ctx
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction

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
    Product.Σ Label (λ ℓ → M ≡ blame ℓ) →
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
canonical-⇒ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (c ↦ d))
    (⊢⟨⟩ (cast-fun cwt dwt) hW) =
  fv-↦ vW refl
canonical-⇒ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (gen A c)) (⊢⟨⟩ () hW)

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
canonical-∀ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ (cast-all cwt) hW) =
  av-∀ vW refl
canonical-∀ (_⟨_⟩ {V = W} vW (gen A c)) (⊢⟨⟩ (cast-gen _ cwt) hW) =
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
canonical-ℕ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (gen A c)) (⊢⟨⟩ () hW)

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
canonical-★ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ (cast-tag _ _) hW) =
  sv-tag vW refl
canonical-★ (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ () hW)
canonical-★ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-★ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-★ (_⟨_⟩ {V = W} vW (gen A c)) (⊢⟨⟩ () hW)

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
canonical-＇ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-＇ (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ (cast-seal _ _) hW) =
  sv-seal vW refl
canonical-＇ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-＇ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-＇ (_⟨_⟩ {V = W} vW (gen A c)) (⊢⟨⟩ () hW)

------------------------------------------------------------------------
-- Progress helpers
------------------------------------------------------------------------

untag-progress :
  ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{G : Ty}{ℓ : Label} →
  Value M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ ★ →
  Progress {Σ = Σ} (M ⟨ G ？ ℓ ⟩)
untag-progress {G = G} {ℓ = ℓ} vM M⊢ with canonical-★ vM M⊢
untag-progress {G = G} {ℓ = ℓ} vM M⊢
    | sv-tag {G = H} vW refl with H ≟Ty G
untag-progress {G = G} {ℓ = ℓ} vM M⊢
    | sv-tag {G = .G} vW refl | yes refl =
  step (pure-step (tag-untag-ok vW))
untag-progress {G = G} {ℓ = ℓ} vM M⊢
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
progress (⊢· {L = L} {M = M} L⊢ M⊢) | crash (ℓ , refl) =
  step (pure-step blame-·₁)
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL with progress M⊢
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL | step M→M′ =
  step (ξ-·₂ vL M→M′)
progress (⊢· {L = L} {M = M} L⊢ M⊢) | done vL
    | crash (ℓ , refl) =
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
progress (⊢• {L = M} {B = B} {α = α} M⊢ α<Δ) with progress M⊢
progress (⊢• {L = M} {B = B} {α = α} M⊢ α<Δ) | step M→M′ =
  step (ξ-·α M→M′)
progress (⊢• {L = M} {B = B} {α = α} M⊢ α<Δ) | crash (ℓ , refl) =
  step (pure-step blame-·α)
progress (⊢• {L = M} {B = B} {α = α} M⊢ α<Δ) | done vM
    with canonical-∀ vM M⊢
progress (⊢• {L = M} {B = B} {α = α} M⊢ α<Δ) | done vM
    | av-Λ refl =
  step (pure-step β-Λ)
progress (⊢• {L = M} {B = B} {α = α} M⊢ α<Δ) | done vM
    | av-∀ vW refl =
  step (pure-step (β-∀ vW))
progress {Σ = Σ} (⊢• {L = M} {B = B} {α = α} M⊢ α<Δ) | done vM
    | av-gen vW refl =
  step (pure-step (β-gen {Σ = Σ} vW))
progress (⊢ν {A = A} hA N⊢) = step (ν-step {A = A} {α = zero})
progress (⊢$ κ) = done ($ κ)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) with progress L⊢
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | step L→L′ =
  step (ξ-⊕₁ L→L′)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | crash (ℓ , refl) =
  step (pure-step blame-⊕₁)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL with progress M⊢
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL | step M→M′ =
  step (ξ-⊕₂ vL M→M′)
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL
    | crash (ℓ , refl) =
  step (pure-step (blame-⊕₂ vL))
progress (⊢⊕ {L = L} {M = M} L⊢ op M⊢) | done vL | done vM
    with canonical-ℕ vL L⊢ | canonical-ℕ vM M⊢
progress (⊢⊕ {L = L} {M = M} L⊢ addℕ M⊢)
    | done vL | done vM | nv-const refl | nv-const refl =
  step (pure-step δ-⊕)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) with progress M⊢
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | step M→M′ =
  step (ξ-⟨⟩ M→M′)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | crash (ℓ , refl) =
  step (pure-step blame-⟨⟩)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM with c⊢
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM | cast-id hA =
  step (pure-step (β-id vM))
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-seal hA hα =
  done (vM ⟨ seal _ _ ⟩)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-unseal hA hα =
  unseal-progress vM M⊢
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-seq p⊢ q⊢ =
  step (pure-step (β-seq vM))
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM | cast-tag hG gG =
  done (vM ⟨ _ ! ⟩)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-untag hG gG =
  untag-progress vM M⊢
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-fun p⊢ q⊢ =
  done (vM ⟨ _ ↦ _ ⟩)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM | cast-all cwt =
  done (vM ⟨ `∀ _ ⟩)
progress {Σ = Σ} (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢)
    | done vM | cast-inst _ cwt =
  step (pure-step (β-inst {Σ = Σ} {α = zero} vM))
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM | cast-gen _ cwt =
  done (vM ⟨ gen _ _ ⟩)
progress (⊢blame hA ℓ) = crash (ℓ , refl)
