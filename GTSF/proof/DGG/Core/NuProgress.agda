module proof.DGG.Core.NuProgress where

-- File Charter:
--   * Canonical-form lemmas and progress for closed Nu GTSF terms.
--   * Produces values, blame crashes, or one store-change reduction step.
--   * Uses the `NuTerms`/`NuReduction` formulation of the dynamic semantics.
--   * The `GenSafe` repair needs no new progress branch: its eager
--     untag/gen and inst/tag forms are ordinary coercion sequences and step
--     through the existing `cast-seq` case.

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
open import proof.Core.Properties.NuTermProperties using (renameᵗᵐ-preserves-Value)

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
    ∀ {χ : StoreChange}{N : Term} →
    M —→[ χ ] N →
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

type-app-progress :
  ∀ {Δ : TyCtx}{Σ : Store}{V : Term}{A C : Ty} →
  Value V →
  No• V →
  Δ ∣ Σ ∣ [] ⊢ V ⦂ `∀ C →
  Progress {Δ = suc Δ} {Σ = (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ} ((⇑ᵗᵐ V) •)
type-app-progress (ƛ N) noV ()
type-app-progress (Λ vV) (no•-Λ noV) (⊢Λ _ hV) =
  step (pure-step (β-Λ• (renameᵗᵐ-preserves-Value (extᵗ suc) vV)))
type-app-progress ($ (κℕ n)) noV ()
type-app-progress (_⟨_⟩ {V = W} vW (G !)) noV (⊢⟨⟩ () hW)
type-app-progress (_⟨_⟩ {V = W} vW (seal A α)) noV (⊢⟨⟩ () hW)
type-app-progress (_⟨_⟩ {V = W} vW (c ↦ d)) noV (⊢⟨⟩ () hW)
type-app-progress (_⟨_⟩ {V = W} vW (`∀ c)) (no•-⟨⟩ noW)
    (⊢⟨⟩ (cast-all c⊢) hW) =
  step (pure-step (β-∀• (renameᵗᵐ-preserves-Value suc vW)))
type-app-progress (_⟨_⟩ {V = W} vW (gen A c)) (no•-⟨⟩ noW)
    (⊢⟨⟩ (cast-gen _ _ c⊢) hW) =
  step (pure-step (β-gen• (renameᵗᵐ-preserves-Value suc vW)))

shiftable-no :
  ∀ {χ : StoreChange}{M : Term} →
  No• M →
  Shiftable χ M
shiftable-no {χ = keep} noM = shift-keep
shiftable-no {χ = bind A} noM = shift-bind noM

runtime-value-no• :
  ∀ {V : Term} →
  RuntimeOK V →
  Value V →
  No• V
runtime-value-no• (ok-no noV) vV = noV
runtime-value-no• (ok-• vV noV) ()
runtime-value-no• (ok-·₁ okL noM) ()
runtime-value-no• (ok-·₂ vV noV okM) ()
runtime-value-no• (ok-ν okL) ()
runtime-value-no• (ok-⊕₁ okL noM) ()
runtime-value-no• (ok-⊕₂ vL noL okM) ()
runtime-value-no• (ok-⟨⟩ okM) (vM ⟨ i ⟩) =
  no•-⟨⟩ (runtime-value-no• okM vM)

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

mutual

  progress :
    ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{A : Ty} →
    RuntimeOK M →
    Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
    Progress {Δ = Δ} {Σ = Σ} M
  progress ok (⊢` ())
  progress ok (⊢ƛ hA hM) = done (ƛ _)
  progress (ok-no (no•-· noL noM)) (⊢· L⊢ M⊢) =
    progress-·₁ (ok-no noL) noM L⊢ M⊢
  progress (ok-·₁ okL noM) (⊢· L⊢ M⊢) =
    progress-·₁ okL noM L⊢ M⊢
  progress (ok-·₂ vL noL okM) (⊢· L⊢ M⊢) =
    progress-·₂ vL noL okM L⊢ M⊢
  progress ok (⊢Λ vM hM) = done (Λ vM)
  progress ok (⊢• refl refl hC vV noV hV) =
    type-app-progress vV noV hV
  progress (ok-no (no•-ν noL)) (⊢ν hA L⊢ c⊢) =
    progress-ν (ok-no noL) hA L⊢ c⊢
  progress (ok-ν okL) (⊢ν hA L⊢ c⊢) =
    progress-ν okL hA L⊢ c⊢
  progress ok (⊢$ κ) = done ($ κ)
  progress (ok-no (no•-⊕ noL noM)) (⊢⊕ L⊢ op M⊢) =
    progress-⊕₁ (ok-no noL) noM L⊢ M⊢
  progress (ok-⊕₁ okL noM) (⊢⊕ L⊢ op M⊢) =
    progress-⊕₁ okL noM L⊢ M⊢
  progress (ok-⊕₂ vL noL okM) (⊢⊕ L⊢ op M⊢) =
    progress-⊕₂ vL noL okM L⊢ M⊢
  progress (ok-no (no•-⟨⟩ noM)) (⊢⟨⟩ c⊢ M⊢) =
    progress-cast (ok-no noM) c⊢ M⊢
  progress (ok-⟨⟩ okM) (⊢⟨⟩ c⊢ M⊢) =
    progress-cast okM c⊢ M⊢
  progress ok (⊢blame hA) = crash refl

  progress-·₁ :
    ∀ {Δ : TyCtx}{Σ : Store}{L M : Term}{A B : Ty} →
    RuntimeOK L →
    No• M →
    Δ ∣ Σ ∣ [] ⊢ L ⦂ A ⇒ B →
    Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
    Progress {Δ = Δ} {Σ = Σ} (L · M)
  progress-·₁ okL noM L⊢ M⊢ with progress okL L⊢
  progress-·₁ okL noM L⊢ M⊢ | step L→L′ =
    step (ξ-·₁ L→L′ (shiftable-no noM))
  progress-·₁ okL noM L⊢ M⊢ | crash refl =
    step (pure-step blame-·₁)
  progress-·₁ okL noM L⊢ M⊢ | done vL =
    progress-·₂ vL (runtime-value-no• okL vL) (ok-no noM) L⊢ M⊢

  progress-·₂ :
    ∀ {Δ : TyCtx}{Σ : Store}{V M : Term}{A B : Ty} →
    Value V →
    No• V →
    RuntimeOK M →
    Δ ∣ Σ ∣ [] ⊢ V ⦂ A ⇒ B →
    Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
    Progress {Δ = Δ} {Σ = Σ} (V · M)
  progress-·₂ vV noV okM V⊢ M⊢ with progress okM M⊢
  progress-·₂ vV noV okM V⊢ M⊢ | step M→M′ =
    step (ξ-·₂ vV (shiftable-no noV) M→M′)
  progress-·₂ vV noV okM V⊢ M⊢ | crash refl =
    step (pure-step (blame-·₂ vV))
  progress-·₂ vV noV okM V⊢ M⊢ | done vM
      with canonical-⇒ vV V⊢
  progress-·₂ vV noV okM V⊢ M⊢ | done vM | fv-ƛ refl =
    step (pure-step (β vM))
  progress-·₂ vV noV okM V⊢ M⊢ | done vM | fv-↦ vW refl =
    step (pure-step (β-↦ vW vM))

  progress-ν :
    ∀ {Δ : TyCtx}{Σ : Store}{A B C : Ty}{L : Term}
      {c : Coercion}{μ : ModeEnv} →
    RuntimeOK L →
    WfTy Δ A →
    Δ ∣ Σ ∣ [] ⊢ L ⦂ `∀ C →
    μ ∣ suc Δ ∣ (0 , ⇑ᵗ A) ∷ ⟰ᵗ Σ ⊢ c ∶ C =⇒ ⇑ᵗ B →
    Progress {Δ = Δ} {Σ = Σ} (ν A L c)
  progress-ν okL hA L⊢ c⊢ with progress okL L⊢
  progress-ν okL hA L⊢ c⊢ | step L→L′ =
    step (ξ-ν L→L′)
  progress-ν okL hA L⊢ c⊢ | crash refl =
    step blame-ν
  progress-ν okL hA L⊢ c⊢ | done vL =
    step (ν-step vL (runtime-value-no• okL vL))

  progress-⊕₁ :
    ∀ {Δ : TyCtx}{Σ : Store}{L M : Term}{op : Prim} →
    RuntimeOK L →
    No• M →
    Δ ∣ Σ ∣ [] ⊢ L ⦂ ‵ `ℕ →
    Δ ∣ Σ ∣ [] ⊢ M ⦂ ‵ `ℕ →
    Progress {Δ = Δ} {Σ = Σ} (L ⊕[ op ] M)
  progress-⊕₁ okL noM L⊢ M⊢ with progress okL L⊢
  progress-⊕₁ okL noM L⊢ M⊢ | step L→L′ =
    step (ξ-⊕₁ L→L′ (shiftable-no noM))
  progress-⊕₁ okL noM L⊢ M⊢ | crash refl =
    step (pure-step blame-⊕₁)
  progress-⊕₁ okL noM L⊢ M⊢ | done vL =
    progress-⊕₂ vL (runtime-value-no• okL vL) (ok-no noM) L⊢ M⊢

  progress-⊕₂ :
    ∀ {Δ : TyCtx}{Σ : Store}{L M : Term}{op : Prim} →
    Value L →
    No• L →
    RuntimeOK M →
    Δ ∣ Σ ∣ [] ⊢ L ⦂ ‵ `ℕ →
    Δ ∣ Σ ∣ [] ⊢ M ⦂ ‵ `ℕ →
    Progress {Δ = Δ} {Σ = Σ} (L ⊕[ op ] M)
  progress-⊕₂ vL noL okM L⊢ M⊢ with progress okM M⊢
  progress-⊕₂ vL noL okM L⊢ M⊢ | step M→M′ =
    step (ξ-⊕₂ vL (shiftable-no noL) M→M′)
  progress-⊕₂ vL noL okM L⊢ M⊢ | crash refl =
    step (pure-step (blame-⊕₂ vL))
  progress-⊕₂ {op = addℕ} vL noL okM L⊢ M⊢ | done vM
      with canonical-ℕ vL L⊢ | canonical-ℕ vM M⊢
  progress-⊕₂ {op = addℕ} vL noL okM L⊢ M⊢
      | done vM | nv-const refl | nv-const refl =
    step (pure-step δ-⊕)

  progress-cast :
    ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{A B : Ty}
      {c : Coercion}{μ : ModeEnv} →
    RuntimeOK M →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
    Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
    Progress {Δ = Δ} {Σ = Σ} (M ⟨ c ⟩)
  progress-cast okM c⊢ M⊢ with progress okM M⊢
  progress-cast okM c⊢ M⊢ | step M→M′ =
    step (ξ-⟨⟩ M→M′)
  progress-cast okM c⊢ M⊢ | crash refl =
    step (pure-step blame-⟨⟩)
  progress-cast okM c⊢ M⊢ | done vM with c⊢
  progress-cast okM c⊢ M⊢ | done vM | cast-id hA _ =
    step (pure-step (β-id vM))
  progress-cast okM c⊢ M⊢ | done vM | cast-seal hA hα _ =
    done (vM ⟨ seal _ _ ⟩)
  progress-cast okM c⊢ M⊢ | done vM | cast-unseal hA hα _ =
    unseal-progress vM M⊢
  progress-cast okM c⊢ M⊢ | done vM | cast-seq p⊢ q⊢ =
    step (pure-step (β-seq vM))
  progress-cast okM c⊢ M⊢ | done vM | cast-tag hG gG _ =
    done (vM ⟨ _ ! ⟩)
  progress-cast okM c⊢ M⊢ | done vM | cast-untag hG gG _ =
    untag-progress vM M⊢
  progress-cast okM c⊢ M⊢ | done vM | cast-fun p⊢ q⊢ =
    done (vM ⟨ _ ↦ _ ⟩)
  progress-cast okM c⊢ M⊢ | done vM | cast-all cwt =
    done (vM ⟨ `∀ _ ⟩)
  progress-cast okM c⊢ M⊢ | done vM | cast-inst _ _ cwt =
    step (pure-step (β-inst vM))
  progress-cast okM c⊢ M⊢ | done vM | cast-gen _ _ cwt =
    done (vM ⟨ gen _ _ ⟩)
