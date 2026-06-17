module proof.NuPreservation where

-- File Charter:
--   * Type preservation for Nu GTSF one-step reduction.
--   * Keeps store growth, fresh type-variable allocation, and redex typing
--     obligations local to preservation.
--   * Uses the type/coercion/term metatheory factored into sibling proof files.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; _<_; _≤_; _⊔_; zero; z<s; s≤s)
open import Data.Nat.Properties
  using (≤-refl; n≤1+n; <-≤-trans; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Ctx
open import NuStore
open import Coercions
open import Primitives
open import NuTerms
open import NuReduction
open import proof.TypeProperties
open import proof.NuStoreProperties
open import proof.CoercionProperties
open import proof.NuTermProperties

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

coercion-open-existing :
  ∀ {μ Δ Σ c A B α} →
  α < Δ →
  μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  Δ ∣ Σ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open-existing {μ = μ} {Σ = Σ} {α = α} α<Δ c⊢ =
  subst
    (λ Σ′ → _ ∣ Σ′ ⊢ _ ∶ _ =⇒ _)
    (renameStoreᵗ-single-suc-cancel α Σ)
    (coercion-renameᵗᵐ
      (singleRenameᵗ-Wf-< α<Δ)
      (ModeRename-to-normal {ρ = singleRenameᵗ α} {μ = μ})
      c⊢)

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
pure-preservation wfΣ hΓ
    (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n)))
    δ-⊕ =
  ⊢$ _
pure-preservation wfΣ hΓ (⊢· (⊢ƛ hA hN) hV) (β vV) =
  typing-single-subst hN hV
pure-preservation wfΣ hΓ
    (⊢• {B = B} (⊢Λ {A = B′} vV V⊢) α<Δ)
    β-Λ =
  typing-open-existingᵀ α<Δ V⊢
pure-preservation wfΣ hΓ (⊢⟨⟩ (cast-id hA) hV) (β-id vV) =
  hV
pure-preservation wfΣ hΓ (⊢⟨⟩ (cast-seq p⊢ q⊢) hV) (β-seq vV) =
  ⊢⟨⟩ q⊢ (⊢⟨⟩ p⊢ hV)
pure-preservation wfΣ hΓ
    (⊢· (⊢⟨⟩ (cast-fun p⊢ q⊢) hV) hW)
    (β-↦ vV vW) =
  ⊢⟨⟩ q⊢ (⊢· hV (⊢⟨⟩ p⊢ hW))
pure-preservation wfΣ hΓ
    (⊢• {α = α}
      (⊢⟨⟩ {M = V} (`∀⊢@(cast-all {A = A₀} {s = c} c⊢)) V⊢)
      α<Δ)
    (β-∀ vV) =
  ⊢⟨⟩
    (coercion-open-existing α<Δ c⊢)
    app-src⊢
  where
    src-open-eq :
      (src c) [ α ]ᴿ ≡ A₀ [ α ]ᴿ
    src-open-eq with coercion-src-tgtᵐ c⊢
    src-open-eq | src-eq , tgt-eq =
      cong (λ T → T [ α ]ᴿ) src-eq

    V-src⊢ :
      _ ∣ _ ∣ _ ⊢ V ⦂ `∀ (src c)
    V-src⊢ with coercion-src-tgtᵐ c⊢
    V-src⊢ | src-eq , tgt-eq =
      subst (λ U → _ ∣ _ ∣ _ ⊢ V ⦂ `∀ U) (sym src-eq) V⊢

    app-src⊢ :
      _ ∣ _ ∣ _ ⊢ V • α ⦂ A₀ [ α ]ᴿ
    app-src⊢ =
      subst
        (λ U → _ ∣ _ ∣ _ ⊢ V • α ⦂ U)
        src-open-eq
        (⊢• V-src⊢ α<Δ)
pure-preservation wfΣ hΓ
    (⊢• {α = α}
      (⊢⟨⟩ (gen⊢@(cast-gen {s = c} hC c⊢)) V⊢)
      α<Δ)
    (β-gen vV) =
  ⊢⟨⟩
    (subst
      (λ T → _ ∣ _ ⊢ c [ _ ]ᶜ ∶ T =⇒ _)
      (renameᵗ-single-suc-cancel _ _)
      (coercion-open-existing α<Δ c⊢))
    V⊢
pure-preservation wfΣ hΓ
    (⊢⟨⟩ {M = V} (cast-inst {A = A} {B = B} {s = c} hB c⊢) V⊢)
    (β-inst vV) =
  ⊢ν
    wf★
    (⊢⟨⟩ (coercion-mode-relax modeIncl-normal c⊢) app-src⊢)
  where
    app-src-eq :
      (renameᵗ (extᵗ suc) A) [ zero ]ᴿ ≡ A
    app-src-eq =
      trans
        (renameᵗ-compose (extᵗ suc) (singleRenameᵗ zero) A)
        (trans
          (rename-cong
            (λ { zero → refl
               ; (suc X) → refl})
            A)
          (renameᵗ-id A))

    shifted-V⊢ :
      _ ∣ _ ∣ _ ⊢ ⇑ᵗᵐ V ⦂ `∀ (renameᵗ (extᵗ suc) A)
    shifted-V⊢ =
      term-weaken ≤-refl StoreIncl-drop (typing-renameᵀ TyRenameWf-suc V⊢)

    app-src⊢ :
      _ ∣ _ ∣ _ ⊢ ⇑ᵗᵐ V • zero ⦂ A
    app-src⊢ =
      subst
        (λ T → _ ∣ _ ∣ _ ⊢ ⇑ᵗᵐ V • zero ⦂ T)
        app-src-eq
        (⊢• shifted-V⊢ z<s)
pure-preservation wfΣ hΓ
    (⊢⟨⟩ (cast-unseal hB αB∈Σ)
      (⊢⟨⟩ (cast-seal hA αA∈Σ) hV))
    (seal-unseal vV) =
  subst (λ T → _ ∣ _ ∣ _ ⊢ _ ⦂ T)
        (unique wfΣ αA∈Σ αB∈Σ)
        hV
pure-preservation wfΣ hΓ
    (⊢⟨⟩ (cast-untag hG gG) (⊢⟨⟩ (cast-tag hG′ gG′) hV))
    (tag-untag-ok vV) =
  hV
pure-preservation wfΣ hΓ
    (⊢⟨⟩ (cast-untag hH gH) (⊢⟨⟩ (cast-tag hG gG) hV))
    (tag-untag-bad vV G≢H) =
  ⊢blame hH
pure-preservation wfΣ hΓ (⊢· (⊢blame (wf⇒ hA hB)) hM) blame-·₁ =
  ⊢blame hB
pure-preservation wfΣ hΓ (⊢· hV (⊢blame hA)) (blame-·₂ vV)
    with typing-wf (at wfΣ) hΓ hV
pure-preservation wfΣ hΓ (⊢· hV (⊢blame hA)) (blame-·₂ vV)
    | wf⇒ hA′ hB =
  ⊢blame hB
pure-preservation wfΣ hΓ (⊢• (⊢blame (wf∀ hB)) α<Δ) blame-·α =
  ⊢blame (renameᵗ-preserves-WfTy hB (singleRenameᵗ-Wf-< α<Δ))
pure-preservation wfΣ hΓ (⊢⟨⟩ c⊢ (⊢blame hA)) blame-⟨⟩
    with coercion-wf (at wfΣ) c⊢
pure-preservation wfΣ hΓ (⊢⟨⟩ c⊢ (⊢blame hA)) blame-⟨⟩
    | hA′ , hB =
  ⊢blame hB
pure-preservation wfΣ hΓ (⊢⊕ (⊢blame hA) op hM) blame-⊕₁ =
  ⊢blame wfBase
pure-preservation wfΣ hΓ (⊢⊕ hL op (⊢blame hA)) (blame-⊕₂ vL) =
  ⊢blame wfBase

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
    (⊢ν {A = A} hA hN)
    (ν-step {α = α} α∉Σ) =
  preserve
    (suc (α ⊔ Δ))
    (StoreWf-fresh-ext
      wfΣ
      (≤-trans (m≤n⊔m α Δ) (n≤1+n (α ⊔ Δ)))
      (s≤s (m≤m⊔n α Δ))
      hA
      α∉Σ)
    (≤-trans (m≤n⊔m α Δ) (n≤1+n (α ⊔ Δ)))
    StoreIncl-drop
    (CtxWf-weaken hΓ (≤-trans (m≤n⊔m α Δ) (n≤1+n (α ⊔ Δ))))
    (typing-open-headᵀ
      (s≤s (m≤m⊔n α Δ))
      (term-weaken (s≤s (m≤n⊔m α Δ)) StoreIncl-refl hN))
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
preservation wfΣ hΓ (⊢• M⊢ α<Δ) (ξ-·α red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢• M⊢ α<Δ) (ξ-·α red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢• M′⊢ (<-≤-trans α<Δ Δ≤Δ′))
preservation wfΣ hΓ (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ red)
    with preservation wfΣ hΓ M⊢ red
preservation wfΣ hΓ (⊢⟨⟩ c⊢ M⊢) (ξ-⟨⟩ red)
    | preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′ M′⊢ =
  preserve Δ′ wfΣ′ Δ≤Δ′ incl hΓ′
    (⊢⟨⟩ (coercion-weaken Δ≤Δ′ incl c⊢) M′⊢)
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
