module proof.Progress where

-- File Charter:
--   * Canonical-form lemmas and progress for closed GTPLC terms.
--   * Produces a value, blame, or one store-change reduction step.
--   * Adapts GTSF's Nu progress proof to GTPLC's meta-level type
--     application and simplified coercions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore
open import Coercions
open import Primitives
open import Terms
open import Reduction

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress {Δ : TyCtx}{Σ : TyStore} (M : Term) : Set where
  done : Value M → Progress M
  step : ∀ {χ : StoreChange}{N : Term}
    → M —→[ χ ] N
    → Progress M
  crash : M ≡ blame
    → Progress M

------------------------------------------------------------------------
-- Canonical forms for closed values
------------------------------------------------------------------------

data FunValue (V : Term) : Set where
  fv-ƛ : ∀ {N : Term}
    → V ≡ ƛ N
    → FunValue V

  fv-↦ : ∀ {W : Term}{c d : Coercion}
    → Value W
    → V ≡ W ⟨ c ↦ d ⟩
    → FunValue V

canonical-⇒ : ∀ {Δ : TyCtx}{Σ : TyStore}{V : Term}{A B : Ty}
  → Value V
  → Δ ∣ Σ ∣ [] ⊢ V ⦂ (A ⇒ B)
  → FunValue V
canonical-⇒ (ƛ N) (⊢ƛ hA hN) = fv-ƛ refl
canonical-⇒ (Λ vV) ()
canonical-⇒ ($ (κℕ n)) ()
canonical-⇒ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (seal α)) (⊢⟨⟩ () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (c ↦ d))
    (⊢⟨⟩ (cast-fun c⊢ d⊢) hW) =
  fv-↦ vW refl
canonical-⇒ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-⇒ (_⟨_⟩ {V = W} vW (gen c)) (⊢⟨⟩ () hW)

data AllValue (V : Term) : Set where
  av-Λ : ∀ {W : Term}
    → V ≡ Λ W
    → AllValue V

  av-∀ : ∀ {W : Term}{c : Coercion}
    → Value W
    → V ≡ W ⟨ `∀ c ⟩
    → AllValue V

  av-gen : ∀ {W : Term}{c : Coercion}
    → Value W
    → V ≡ W ⟨ gen c ⟩
    → AllValue V

canonical-∀ : ∀ {Δ : TyCtx}{Σ : TyStore}{V : Term}{A : Ty}
  → Value V
  → Δ ∣ Σ ∣ [] ⊢ V ⦂ (`∀ A)
  → AllValue V
canonical-∀ (ƛ N) ()
canonical-∀ (Λ vV) (⊢Λ _ hV) = av-Λ refl
canonical-∀ ($ (κℕ n)) ()
canonical-∀ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (seal α)) (⊢⟨⟩ () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-∀ (_⟨_⟩ {V = W} vW (`∀ c))
    (⊢⟨⟩ (cast-all c⊢) hW) =
  av-∀ vW refl
canonical-∀ (_⟨_⟩ {V = W} vW (gen c))
    (⊢⟨⟩ (cast-gen hA X∈B c⊢) hW) =
  av-gen vW refl

data NatValue (V : Term) : Set where
  nv-const : ∀ {n : ℕ}
    → V ≡ $ (κℕ n)
    → NatValue V

canonical-ℕ : ∀ {Δ : TyCtx}{Σ : TyStore}{V : Term}
  → Value V
  → Δ ∣ Σ ∣ [] ⊢ V ⦂ (‵ `ℕ)
  → NatValue V
canonical-ℕ (ƛ N) ()
canonical-ℕ (Λ vV) ()
canonical-ℕ ($ (κℕ n)) (⊢$ (κℕ .n)) = nv-const refl
canonical-ℕ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (seal α)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-ℕ (_⟨_⟩ {V = W} vW (gen c)) (⊢⟨⟩ () hW)

data DynValue (V : Term) : Set where
  sv-tag : ∀ {W : Term}{G : Tag}
    → Value W
    → V ≡ W ⟨ G ! ⟩
    → DynValue V

canonical-★ : ∀ {Δ : TyCtx}{Σ : TyStore}{V : Term}
  → Value V
  → Δ ∣ Σ ∣ [] ⊢ V ⦂ ★
  → DynValue V
canonical-★ (ƛ N) ()
canonical-★ (Λ vV) ()
canonical-★ ($ (κℕ n)) ()
canonical-★ (_⟨_⟩ {V = W} vW (G !))
    (⊢⟨⟩ (cast-tag hG gG G꞉A) hW) =
  sv-tag vW refl
canonical-★ (_⟨_⟩ {V = W} vW (seal α)) (⊢⟨⟩ () hW)
canonical-★ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-★ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-★ (_⟨_⟩ {V = W} vW (gen c)) (⊢⟨⟩ () hW)

data SealValue {α : TyVar} (V : Term) : Set where
  sv-seal : ∀ {W : Term}
    → Value W
    → V ≡ W ⟨ seal α ⟩
    → SealValue {α = α} V

canonical-tyvar : ∀ {Δ : TyCtx}{Σ : TyStore}{V : Term}{α : TyVar}
  → Value V
  → Δ ∣ Σ ∣ [] ⊢ V ⦂ (＇ α)
  → SealValue {α = α} V
canonical-tyvar (ƛ N) ()
canonical-tyvar (Λ vV) ()
canonical-tyvar ($ (κℕ n)) ()
canonical-tyvar (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
canonical-tyvar (_⟨_⟩ {V = W} vW (seal α))
    (⊢⟨⟩ (cast-seal hA α∈Σ sealed) hW) =
  sv-seal vW refl
canonical-tyvar (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-tyvar (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-tyvar (_⟨_⟩ {V = W} vW (gen c)) (⊢⟨⟩ () hW)

------------------------------------------------------------------------
-- Progress helpers
------------------------------------------------------------------------

untag-progress : ∀ {Δ : TyCtx}{Σ : TyStore}{M : Term}{G : Tag}
  → Value M
  → Δ ∣ Σ ∣ [] ⊢ M ⦂ ★
  → Progress {Δ = Δ} {Σ = Σ} (M ⟨ G ？ ⟩)
untag-progress {G = G} vM M⊢ with canonical-★ vM M⊢
untag-progress {G = G} vM M⊢
    | sv-tag {G = H} vW refl with H ≟Tag G
untag-progress {G = G} vM M⊢
    | sv-tag {G = .G} vW refl | yes refl =
  step (pure-step (tag-untag-ok vW))
untag-progress {G = G} vM M⊢
    | sv-tag {G = H} vW refl | no H≢G =
  step (pure-step (tag-untag-bad vW H≢G))

unseal-progress : ∀ {Δ : TyCtx}{Σ : TyStore}{M : Term}{α : TyVar}
  → Value M
  → Δ ∣ Σ ∣ [] ⊢ M ⦂ (＇ α)
  → Progress {Δ = Δ} {Σ = Σ} (M ⟨ unseal α ⟩)
unseal-progress vM M⊢ with canonical-tyvar vM M⊢
unseal-progress vM M⊢ | sv-seal vW refl =
  step (pure-step (seal-unseal vW))

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

mutual

  progress : ∀ {Δ : TyCtx}{Σ : TyStore}{M : Term}{A : Ty}
    → Δ ∣ Σ ∣ [] ⊢ M ⦂ A
    → Progress {Δ = Δ} {Σ = Σ} M
  progress (⊢` ())
  progress (⊢ƛ hA hM) = done (ƛ _)
  progress (⊢· L⊢ M⊢) = progress-·₁ L⊢ M⊢
  progress (⊢Λ vM hM) = done (Λ vM)
  progress (⊢ν hA L⊢ c⊢) = progress-ν hA L⊢ c⊢
  progress (⊢$ κ) = done ($ κ)
  progress (⊢⊕ L⊢ op M⊢) = progress-⊕₁ L⊢ M⊢
  progress (⊢⟨⟩ c⊢ M⊢) = progress-cast c⊢ M⊢
  progress (⊢blame hA) = crash refl

  progress-·₁ : ∀ {Δ : TyCtx}{Σ : TyStore}{L M : Term}{A B : Ty}
    → Δ ∣ Σ ∣ [] ⊢ L ⦂ A ⇒ B
    → Δ ∣ Σ ∣ [] ⊢ M ⦂ A
    → Progress {Δ = Δ} {Σ = Σ} (L · M)
  progress-·₁ L⊢ M⊢ with progress L⊢
  progress-·₁ L⊢ M⊢ | step L→L′ =
    step (ξ-·₁ L→L′)
  progress-·₁ L⊢ M⊢ | crash refl =
    step (pure-step blame-·₁)
  progress-·₁ L⊢ M⊢ | done vL =
    progress-·₂ vL L⊢ M⊢

  progress-·₂ : ∀ {Δ : TyCtx}{Σ : TyStore}{V M : Term}{A B : Ty}
    → Value V
    → Δ ∣ Σ ∣ [] ⊢ V ⦂ A ⇒ B
    → Δ ∣ Σ ∣ [] ⊢ M ⦂ A
    → Progress {Δ = Δ} {Σ = Σ} (V · M)
  progress-·₂ vV V⊢ M⊢ with progress M⊢
  progress-·₂ vV V⊢ M⊢ | step M→M′ =
    step (ξ-·₂ vV M→M′)
  progress-·₂ vV V⊢ M⊢ | crash refl =
    step (pure-step (blame-·₂ vV))
  progress-·₂ vV V⊢ M⊢ | done vM with canonical-⇒ vV V⊢
  progress-·₂ vV V⊢ M⊢ | done vM | fv-ƛ refl =
    step (pure-step (β vM))
  progress-·₂ vV V⊢ M⊢ | done vM | fv-↦ vW refl =
    step (pure-step (β-↦ vW vM))

  progress-ν : ∀ {Δ : TyCtx}{Σ : TyStore}{A B C : Ty}{L}{c}{μ}
    → WfTy Δ A
    → Δ ∣ Σ ∣ [] ⊢ L ⦂ `∀ C
    → μ ∣ suc Δ ∣ (0 , ⇑ᵗ A) ∷ ⟰ᵗ Σ ⊢ c ∶ C =⇒ ⇑ᵗ B
    → Progress {Δ = Δ} {Σ = Σ} (ν A · L •⟨ c ⟩)
  progress-ν hA L⊢ c⊢ with progress L⊢
  progress-ν hA L⊢ c⊢ | step L→L′ =
    step (ξ-ν L→L′)
  progress-ν hA L⊢ c⊢ | crash refl =
    step blame-ν
  progress-ν hA L⊢ c⊢ | done vL =
    step (ν-step vL)

  progress-⊕₁ : ∀ {Δ : TyCtx}{Σ : TyStore}{L M : Term}{op : Prim}
    → Δ ∣ Σ ∣ [] ⊢ L ⦂ ‵ `ℕ
    → Δ ∣ Σ ∣ [] ⊢ M ⦂ ‵ `ℕ
    → Progress {Δ = Δ} {Σ = Σ} (L ⊕[ op ] M)
  progress-⊕₁ L⊢ M⊢ with progress L⊢
  progress-⊕₁ L⊢ M⊢ | step L→L′ =
    step (ξ-⊕₁ L→L′)
  progress-⊕₁ L⊢ M⊢ | crash refl =
    step (pure-step blame-⊕₁)
  progress-⊕₁ L⊢ M⊢ | done vL =
    progress-⊕₂ vL L⊢ M⊢

  progress-⊕₂ : ∀ {Δ : TyCtx}{Σ : TyStore}{L M : Term}{op : Prim}
    → Value L
    → Δ ∣ Σ ∣ [] ⊢ L ⦂ ‵ `ℕ
    → Δ ∣ Σ ∣ [] ⊢ M ⦂ ‵ `ℕ
    → Progress {Δ = Δ} {Σ = Σ} (L ⊕[ op ] M)
  progress-⊕₂ vL L⊢ M⊢ with progress M⊢
  progress-⊕₂ vL L⊢ M⊢ | step M→M′ =
    step (ξ-⊕₂ vL M→M′)
  progress-⊕₂ vL L⊢ M⊢ | crash refl =
    step (pure-step (blame-⊕₂ vL))
  progress-⊕₂ {op = addℕ} vL L⊢ M⊢ | done vM
      with canonical-ℕ vL L⊢ | canonical-ℕ vM M⊢
  progress-⊕₂ {op = addℕ} vL L⊢ M⊢
      | done vM | nv-const refl | nv-const refl =
    step (pure-step δ-⊕)

  progress-cast : ∀ {Δ : TyCtx}{Σ : TyStore}{M}{A B : Ty}{c}{μ}
    → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
    → Δ ∣ Σ ∣ [] ⊢ M ⦂ A
    → Progress {Δ = Δ} {Σ = Σ} (M ⟨ c ⟩)
  progress-cast c⊢ M⊢ with progress M⊢
  progress-cast c⊢ M⊢ | step M→M′ =
    step (ξ-⟨⟩ M→M′)
  progress-cast c⊢ M⊢ | crash refl =
    step (pure-step blame-⟨⟩)
  progress-cast c⊢ M⊢ | done vM with c⊢
  progress-cast c⊢ M⊢ | done vM | cast-id hA =
    step (pure-step (β-id vM))
  progress-cast c⊢ M⊢ | done vM | cast-seal hA hα sealed =
    done (vM ⟨ seal _ ⟩)
  progress-cast c⊢ M⊢ | done vM | cast-unseal hA hα sealed =
    unseal-progress vM M⊢
  progress-cast c⊢ M⊢ | done vM | cast-seq p⊢ q⊢ =
    step (pure-step (β-seq vM))
  progress-cast c⊢ M⊢ | done vM | cast-tag hG gG G꞉A =
    done (vM ⟨ _ ! ⟩)
  progress-cast c⊢ M⊢ | done vM | cast-untag hG gG G꞉B =
    untag-progress vM M⊢
  progress-cast c⊢ M⊢ | done vM | cast-fun p⊢ q⊢ =
    done (vM ⟨ _ ↦ _ ⟩)
  progress-cast c⊢ M⊢ | done vM | cast-all cwt =
    done (vM ⟨ `∀ _ ⟩)
  progress-cast c⊢ M⊢ | done vM | cast-inst hB X∈A cwt =
    step (pure-step (β-inst vM))
  progress-cast c⊢ M⊢ | done vM | cast-gen hA X∈B cwt =
    done (vM ⟨ gen _ ⟩)
