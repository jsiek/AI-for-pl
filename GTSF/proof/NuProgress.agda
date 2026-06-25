module proof.NuProgress where

-- File Charter:
--   * Canonical-form lemmas and progress for closed Nu GTSF terms.
--   * Produces values, blame crashes, or one store-threaded reduction step.
--   * Uses the `NuTerms`/`NuReduction` formulation of the dynamic semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero)
open import Data.Nat using (_<_; _≤_; _⊔_; suc; s≤s)
open import Data.Nat.Properties
  using (m≤m⊔n; m≤n⊔m; n≤1+n; <-≤-trans; <-irrefl; ≤-trans)
open import Data.Product as Product using (_,_)
open import Relation.Nullary using (yes; no)

open import Types
open import Ctx
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction

------------------------------------------------------------------------
-- Fresh seal choice for progress
------------------------------------------------------------------------

freshSeal : Store → TyVar
freshSeal [] = zero
freshSeal ((x , A) ∷ Σ) = suc (x ⊔ freshSeal Σ)

dom<freshSeal :
  ∀ Σ {α} →
  α ∈ domˢ Σ →
  α < freshSeal Σ
dom<freshSeal ((x , A) ∷ Σ) (here refl) =
  s≤s (m≤m⊔n x (freshSeal Σ))
dom<freshSeal ((x , B) ∷ Σ) (there α∈Σ) =
  <-≤-trans
    (dom<freshSeal Σ α∈Σ)
    (≤-trans (m≤n⊔m x (freshSeal Σ)) (n≤1+n (x ⊔ freshSeal Σ)))

freshSeal∉ :
  ∀ Σ →
  freshSeal Σ ∉ domˢ Σ
freshSeal∉ Σ fresh∈Σ = <-irrefl refl (dom<freshSeal Σ fresh∈Σ)

freshSealAbove : TyCtx → Store → TyVar
freshSealAbove Δ Σ = Δ ⊔ freshSeal Σ

freshSealAbove∉ :
  ∀ Δ Σ →
  freshSealAbove Δ Σ ∉ domˢ Σ
freshSealAbove∉ Δ Σ fresh∈Σ =
  <-irrefl refl
    (<-≤-trans
      (dom<freshSeal Σ fresh∈Σ)
      (m≤n⊔m Δ (freshSeal Σ)))

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress {Δ : TyCtx}{Σ : Store} (M : Term) : Set where
  done : Value M → Progress M
  step :
    ∀ {Δ′ : TyCtx}{Σ′ : Store}{N : Term} →
    Δ ∣ Σ ∣ M —→ Δ′ ∣ Σ′ ∣ N →
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
canonical-∀ (_⟨_⟩ {V = W} vW (gen A c))
    (⊢⟨⟩ (cast-gen _ _ cwt) hW) =
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
canonical-★ (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ (cast-tag _ _ _) hW) =
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
canonical-＇ (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ (cast-seal _ _ _) hW) =
  sv-seal vW refl
canonical-＇ (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
canonical-＇ (_⟨_⟩ {V = W} vW (`∀ c)) (⊢⟨⟩ () hW)
canonical-＇ (_⟨_⟩ {V = W} vW (gen A c)) (⊢⟨⟩ () hW)

------------------------------------------------------------------------
-- Progress helpers
------------------------------------------------------------------------

untag-progress :
  ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{G : Ty} →
  Value M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ ★ →
  Progress {Δ = Δ} {Σ = Σ} (M ⟨ G ？ ⟩)
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
  Progress {Δ = Δ} {Σ = Σ} (M ⟨ unseal α A ⟩)
unseal-progress vM M⊢ with canonical-＇ vM M⊢
unseal-progress vM M⊢ | sv-seal vW refl =
  step (pure-step (seal-unseal vW))

data TypeAppProgress (S : TypeApp) : Set where
  tap :
    ∀ {V : Term}{cs : List Coercion} →
    S —↠ᵀ val V cs →
    TypeAppProgress S

type-app-progress :
  ∀ {Δ : TyCtx}{Σ : Store}{L : Term}{C : Ty}{α : TyVar}
    {cs : List Coercion} →
  Value L →
  Δ ∣ Σ ∣ [] ⊢ L ⦂ `∀ C →
  TypeAppProgress (app L α cs)
type-app-progress (ƛ N) ()
type-app-progress (Λ vV) (⊢Λ _ hV) =
  tap (stepᵀ (β-Λᵀ vV) doneᵀ)
type-app-progress ($ (κℕ n)) ()
type-app-progress (_⟨_⟩ {V = W} vW (G !)) (⊢⟨⟩ () hW)
type-app-progress (_⟨_⟩ {V = W} vW (seal A α)) (⊢⟨⟩ () hW)
type-app-progress (_⟨_⟩ {V = W} vW (c ↦ d)) (⊢⟨⟩ () hW)
type-app-progress (_⟨_⟩ {V = W} vW (`∀ c))
    (⊢⟨⟩ (cast-all c⊢) hW)
    with type-app-progress vW hW
type-app-progress (_⟨_⟩ {V = W} vW (`∀ c))
    (⊢⟨⟩ (cast-all c⊢) hW)
    | tap W↠V =
  tap (stepᵀ (β-∀ᵀ vW) W↠V)
type-app-progress (_⟨_⟩ {V = W} vW (gen A c))
    (⊢⟨⟩ (cast-gen _ _ c⊢) hW) =
  tap (stepᵀ (β-genᵀ vW) doneᵀ)

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress :
  ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{A : Ty} →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  Progress {Δ = Δ} {Σ = Σ} M
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
progress {Δ = Δ} {Σ = Σ}
    (⊢ν {L = L} {A = A} {c = c} hA L⊢ c⊢)
    with progress L⊢
progress {Δ = Δ} {Σ = Σ}
    (⊢ν {L = L} {A = A} {c = c} hA L⊢ c⊢)
    | step L→L′ =
  step (ξ-ν L→L′)
progress {Δ = Δ} {Σ = Σ}
    (⊢ν {L = L} {A = A} {c = c} hA L⊢ c⊢)
    | crash refl =
  step blame-ν
progress {Δ = Δ} {Σ = Σ}
    (⊢ν {L = L} {A = A} {c = c} hA L⊢ c⊢)
    | done vL with type-app-progress
        {α = freshSealAbove Δ Σ}
        {cs = (c [ freshSealAbove Δ Σ ]ᶜ) ∷ []}
        vL L⊢
progress {Δ = Δ} {Σ = Σ}
    (⊢ν {L = L} {A = A} {c = c} hA L⊢ c⊢)
    | done vL | tap L↠V =
  step
    (ν-step {A = A} {α = freshSealAbove Δ Σ}
      (m≤m⊔n Δ (freshSeal Σ))
      (freshSealAbove∉ Δ Σ)
      L↠V)
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
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) with progress M⊢
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | step M→M′ =
  step (ξ-⟨⟩ M→M′)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | crash refl =
  step (pure-step blame-⟨⟩)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM with c⊢
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM | cast-id hA _ =
  step (pure-step (β-id vM))
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-seal hA hα _ =
  done (vM ⟨ seal _ _ ⟩)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-unseal hA hα _ =
  unseal-progress vM M⊢
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-seq p⊢ q⊢ =
  step (pure-step (β-seq vM))
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM | cast-tag hG gG _ =
  done (vM ⟨ _ ! ⟩)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-untag hG gG _ =
  untag-progress vM M⊢
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM
    | cast-fun p⊢ q⊢ =
  done (vM ⟨ _ ↦ _ ⟩)
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢) | done vM | cast-all cwt =
  done (vM ⟨ `∀ _ ⟩)
progress {Σ = Σ} (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢)
    | done vM | cast-inst _ _ cwt =
  step (pure-step (β-inst vM))
progress (⊢⟨⟩ {M = M} {c = c} c⊢ M⊢)
    | done vM | cast-gen _ _ cwt =
  done (vM ⟨ gen _ _ ⟩)
progress (⊢blame hA) = crash refl
