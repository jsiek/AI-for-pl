module proof.Preservation where

-- File Charter:
--   * Type preservation for GTSF one-step reduction.
--   * Keeps store growth, fresh type-variable allocation, and redex typing
--     obligations local to preservation.
--   * Uses the type/coercion/term metatheory factored into sibling proof files.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (suc; _≤_)
open import Data.Nat.Properties using (≤-refl; n≤1+n; n<1+n)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import Types
open import Ctx
open import Store
open import Coercions
open import Primitives
open import Terms
open import Reduction
open import proof.TypeProperties
open import proof.StoreProperties
open import proof.CoercionProperties
open import proof.TermProperties

------------------------------------------------------------------------
-- Preservation result for store-threaded steps
------------------------------------------------------------------------

record PreservationResult
    (Δ : TyCtx) (Σ : Store) (Γ : Ctx)
    (Σ′ : Store) (N : Term) (A : Ty) : Set₁ where
  constructor preserve
  field
    Δ′ : TyCtx
    storeWf : StoreWf Δ′ Σ′
    ctx≤ : Δ ≤ Δ′
    storeIncl : StoreIncl Σ Σ′
    ctxWf : CtxWf Δ′ Γ
    typed : Δ′ ∣ Σ′ ∣ Γ ⊢ N ⦂ A

open PreservationResult public

StoreWf-fresh-ext-Δ :
  ∀ {Δ Σ A} →
  StoreWf Δ Σ →
  WfTy Δ A →
  StoreWf (suc Δ) ((Δ , A) ∷ Σ)
StoreWf-fresh-ext-Δ {Δ = Δ} {Σ = Σ} {A = A} wfΣ hA =
  subst (λ α → StoreWf (suc Δ) ((α , A) ∷ Σ))
        (len wfΣ)
        (StoreWf-fresh-ext wfΣ hA)

------------------------------------------------------------------------
-- Raw redex preservation
------------------------------------------------------------------------

pure-preservation :
  ∀ {Δ Σ Γ M N A} →
  StoreWf Δ Σ →
  CtxWf Δ Γ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  M —→ N →
  Δ ∣ Σ ∣ Γ ⊢ N ⦂ A
pure-preservation wfΣ hΓ (⊢· (⊢ƛ hA hN) hV) (β vV) =
  typing-single-subst hN hV
pure-preservation wfΣ hΓ
    (⊢· (⊢up (cast-fun p⊢ q⊢) hV) hW)
    (β-↦ vV vW) =
  ⊢up q⊢ (⊢· hV (⊢up p⊢ hW))
pure-preservation wfΣ hΓ (⊢up (cast-id hA) hV) (β-id vV) =
  hV
pure-preservation wfΣ hΓ (⊢up (cast-seq p⊢ q⊢) hV) (β-seq vV) =
  ⊢up q⊢ (⊢up p⊢ hV)
pure-preservation wfΣ hΓ
    (⊢up (cast-unseal hB αB∈Σ)
      (⊢up (cast-seal hA αA∈Σ) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ hΓ
    (⊢up (cast-untag hG gG) (⊢up (cast-tag hG′ gG′) hV))
    (tag-untag-ok vV) =
  hV
pure-preservation wfΣ hΓ
    (⊢up (cast-untag hH gH) (⊢up (cast-tag hG gG) hV))
    (tag-untag-bad vV G≢H) =
  ⊢blame hH _
pure-preservation wfΣ hΓ
    (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n)))
    δ-⊕ =
  ⊢$ _
pure-preservation wfΣ hΓ (⊢· (⊢blame (wf⇒ hA hB) ℓ) hM) blame-·₁ =
  ⊢blame hB ℓ
pure-preservation wfΣ hΓ (⊢· hV (⊢blame hA ℓ)) (blame-·₂ vV)
    with typing-wf (at wfΣ) hΓ hV
pure-preservation wfΣ hΓ (⊢· hV (⊢blame hA ℓ)) (blame-·₂ vV)
    | wf⇒ hA′ hB =
  ⊢blame hB ℓ
pure-preservation wfΣ hΓ (⊢• (⊢blame (wf∀ hB) ℓ) hT) blame-·α =
  ⊢blame (substᵗ-preserves-WfTy hB (singleTyEnv-Wf hT)) ℓ
pure-preservation wfΣ hΓ (⊢up c⊢ (⊢blame hA ℓ)) blame-⟨⟩
    with coercion-wf (at wfΣ) c⊢
pure-preservation wfΣ hΓ (⊢up c⊢ (⊢blame hA ℓ)) blame-⟨⟩
    | hA′ , hB =
  ⊢blame hB ℓ
pure-preservation wfΣ hΓ (⊢⊕ (⊢blame hA ℓ) op hM) blame-⊕₁ =
  ⊢blame wfBase ℓ
pure-preservation wfΣ hΓ (⊢⊕ hL op (⊢blame hA ℓ)) (blame-⊕₂ vL) =
  ⊢blame wfBase ℓ

------------------------------------------------------------------------
-- Store-threaded preservation
------------------------------------------------------------------------

preservation :
  ∀ {Δ Σ Σ′ Γ M N A} →
  StoreWf Δ Σ →
  CtxWf Δ Γ →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Σ ∣ M —→ Σ′ ∣ N →
  PreservationResult Δ Σ Γ Σ′ N A
preservation wfΣ hΓ M⊢ (pure-step red) =
  preserve _ wfΣ ≤-refl StoreIncl-refl hΓ
    (pure-preservation wfΣ hΓ M⊢ red)
preservation {Δ = Δ} {Σ = Σ} {Γ = Γ} wfΣ hΓ
    (⊢• {B = B} {A = T} (⊢Λ {A = B′} vV V⊢) hT)
    β-Λ
    rewrite len wfΣ =
  preserve
    (suc Δ)
    (StoreWf-fresh-ext-Δ wfΣ hT)
    (n≤1+n Δ)
    StoreIncl-drop
    (CtxWf-weaken hΓ (n≤1+n Δ))
    (⊢up
      (reveal-fresh-typing hT hB′)
      (typing-openᵀ (n<1+n Δ) V⊢))
  where
    hB′ : WfTy (suc Δ) B′
    hB′ = typing-wf (StoreWfAt-⟰ᵗ (at wfΣ)) (CtxWf-⤊ hΓ) V⊢
preservation {Δ = Δ} {Σ = Σ} {Γ = Γ} wfΣ hΓ
    (⊢• {B = B} {A = T}
      (⊢up {M = V} (`∀⊢@(cast-all {s = c} c⊢)) V⊢)
      hT)
    (β-∀ vV)
    rewrite len wfΣ =
  preserve
    (suc Δ)
    (StoreWf-fresh-ext-Δ wfΣ hT)
    (n≤1+n Δ)
    StoreIncl-drop
    (CtxWf-weaken hΓ (n≤1+n Δ))
    (⊢up
      (reveal-fresh-typing hT hB)
      (⊢up
        (coercion-open (n<1+n Δ) c⊢)
        app-src⊢))
  where
    hB : WfTy (suc Δ) B
    hB with typing-wf (at wfΣ) hΓ (⊢up `∀⊢ V⊢)
    hB | wf∀ hB′ = hB′

    src-open-eq :
      (src c) [ ＇ Δ ]ᵗ ≡ _ [ Δ ]ᴿ
    src-open-eq with coercion-src-tgt c⊢
    src-open-eq | src-eq , tgt-eq =
      trans (cong (λ T → T [ ＇ Δ ]ᵗ) src-eq)
            (subst-var-rename Δ _)

    V-src⊢ :
      Δ ∣ Σ ∣ Γ ⊢ V ⦂ `∀ (src c)
    V-src⊢ with coercion-src-tgt c⊢
    V-src⊢ | src-eq , tgt-eq =
      subst (λ U → Δ ∣ Σ ∣ Γ ⊢ V ⦂ `∀ U) (sym src-eq) V⊢

    app-src⊢ :
      suc Δ ∣ (Δ , T) ∷ Σ ∣ Γ ⊢ V ⦂∀ src c • ＇ Δ ⦂ _ [ Δ ]ᴿ
    app-src⊢ =
      subst
        (λ U → suc Δ ∣ (Δ , T) ∷ Σ ∣ Γ ⊢ V ⦂∀ src c • ＇ Δ ⦂ U)
        src-open-eq
        (⊢• (term-weaken (n≤1+n Δ) StoreIncl-drop V-src⊢)
             (wfVar (n<1+n Δ)))
preservation {Δ = Δ} {Σ = Σ} {Γ = Γ} wfΣ hΓ
    (⊢• {B = B} {A = T}
      (⊢up (gen⊢@(cast-gen hC c⊢)) V⊢)
      hT)
    (β-down-ν vV)
    rewrite len wfΣ =
  preserve
    (suc Δ)
    (StoreWf-fresh-ext-Δ wfΣ hT)
    (n≤1+n Δ)
    StoreIncl-drop
    (CtxWf-weaken hΓ (n≤1+n Δ))
    (⊢up
      (reveal-fresh-typing hT hB)
      (⊢up
        (coercion-open (n<1+n Δ) c⊢)
        (subst
          (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
          (sym (renameᵗ-single-suc-cancel Δ _))
          (term-weaken (n≤1+n Δ) StoreIncl-drop V⊢))))
  where
    hB : WfTy (suc Δ) B
    hB with typing-wf (at wfΣ) hΓ (⊢up gen⊢ V⊢)
    hB | wf∀ hB′ = hB′
preservation {Δ = Δ} {Σ = Σ} {Γ = Γ} wfΣ hΓ
    (⊢up {M = V} (cast-inst {s = c} hB c⊢) V⊢)
    (β-up-ν vV)
    rewrite len wfΣ =
  preserve
    (suc Δ)
    (StoreWf-fresh-ext-Δ wfΣ wf★)
    (n≤1+n Δ)
    StoreIncl-drop
    (CtxWf-weaken hΓ (n≤1+n Δ))
    (subst
      (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
      (renameᵗ-single-suc-cancel Δ _)
      (⊢up
        (coercion-open-head (n<1+n Δ) c⊢)
        app-src⊢))
  where
    src-open-eq :
      (src c) [ ＇ Δ ]ᵗ ≡ _ [ Δ ]ᴿ
    src-open-eq with coercion-src-tgt c⊢
    src-open-eq | src-eq , tgt-eq =
      trans (cong (λ T → T [ ＇ Δ ]ᵗ) src-eq)
            (subst-var-rename Δ _)

    V-src⊢ :
      Δ ∣ Σ ∣ Γ ⊢ V ⦂ `∀ (src c)
    V-src⊢ with coercion-src-tgt c⊢
    V-src⊢ | src-eq , tgt-eq =
      subst (λ U → Δ ∣ Σ ∣ Γ ⊢ V ⦂ `∀ U) (sym src-eq) V⊢

    app-src⊢ :
      suc Δ ∣ (Δ , ★) ∷ Σ ∣ Γ ⊢ V ⦂∀ src c • ＇ Δ ⦂ _ [ Δ ]ᴿ
    app-src⊢ =
      subst
        (λ U → suc Δ ∣ (Δ , ★) ∷ Σ ∣ Γ ⊢ V ⦂∀ src c • ＇ Δ ⦂ U)
        src-open-eq
        (⊢• (term-weaken (n≤1+n Δ) StoreIncl-drop V-src⊢)
             (wfVar (n<1+n Δ)))
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₁ red)
    with preservation wfΣ hΓ L⊢ red
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₁ red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ L′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢· L′⊢ (term-weaken Δ≤Δ′ incl M⊢))
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢· (term-weaken Δ≤Δ′ incl L⊢) M′⊢)
preservation wfΣ hΓ (⊢• M⊢ hA) (ξ-·α red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢• M⊢ hA) (ξ-·α red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢• M′⊢ (WfTy-weakenᵗ hA Δ≤Δ′))
preservation wfΣ hΓ (⊢up c⊢ M⊢) (ξ-⟨⟩ red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢up c⊢ M⊢) (ξ-⟨⟩ red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢up (coercion-weaken Δ≤Δ′ incl c⊢) M′⊢)
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
    with preservation wfΣ hΓ L⊢ red
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ L′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢⊕ L′⊢ op (term-weaken Δ≤Δ′ incl M⊢))
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢⊕ (term-weaken Δ≤Δ′ incl L⊢) op M′⊢)
